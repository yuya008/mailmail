package mailmail

import (
	"bufio"
	"bytes"
	"crypto/rand"
	"crypto/tls"
	"encoding/base64"
	"errors"
	"fmt"
	"io"
	"math"
	"math/big"
	"mime"
	"mime/multipart"
	"mime/quotedprintable"
	"net/mail"
	"net/smtp"
	"net/textproto"
	"os"
	"path/filepath"
	"strings"
	"time"
	"unicode"
)

type part struct {
	header textproto.MIMEHeader
	body   []byte
}

type Email struct {
	ReplyTo     []string
	From        string
	To          []string
	Bcc         []string
	Cc          []string
	Subject     string
	Text        []byte
	HTML        []byte
	Sender      string
	Headers     textproto.MIMEHeader
	Attachments []*Attachment
	ReadReceipt []string
}

func NewEmail() *Email {
	return &Email{Headers: textproto.MIMEHeader{}}
}

var ErrMissingContentType = errors.New("No Content-Type found for MIME entity")

func NewEmailFromReader(r io.Reader) (*Email, error) {
	e := NewEmail()
	s := &trimReader{rd: r}
	tp := textproto.NewReader(bufio.NewReader(s))

	hdrs, err := tp.ReadMIMEHeader()
	if err != nil {
		return e, err
	}

	for h, v := range hdrs {
		switch h {
		case "Subject":
			e.Subject = v[0]
			subj, err := (&mime.WordDecoder{}).DecodeHeader(e.Subject)
			if err == nil && len(subj) > 0 {
				e.Subject = subj
			}
			delete(hdrs, h)
		case "To":
			e.To = handleAddressList(v)
			delete(hdrs, h)
		case "Cc":
			e.Cc = handleAddressList(v)
			delete(hdrs, h)
		case "Bcc":
			e.Bcc = handleAddressList(v)
			delete(hdrs, h)
		case "Reply-To":
			e.ReplyTo = handleAddressList(v)
			delete(hdrs, h)
		case "From":
			e.From = v[0]
			fr, err := (&mime.WordDecoder{}).DecodeHeader(e.From)
			if err == nil && len(fr) > 0 {
				e.From = fr
			}
			delete(hdrs, h)
		}
	}

	e.Headers = hdrs
	body := tp.R

	ps, err := parseMIMEParts(e.Headers, body)
	if err != nil {
		return e, err
	}
	for _, p := range ps {
		if ct := p.header.Get("Content-Type"); ct == "" {
			return e, ErrMissingContentType
		}
		ct, _, err := mime.ParseMediaType(p.header.Get("Content-Type"))
		if err != nil {
			return e, err
		}

		if cd := p.header.Get("Content-Disposition"); cd != "" {
			cd, params, err := mime.ParseMediaType(p.header.Get("Content-Disposition"))
			if err != nil {
				return e, err
			}
			filename, filenameDefined := params["filename"]
			if cd == "attachment" || (cd == "inline" && filenameDefined) {
				_, err = e.Attach(bytes.NewReader(p.body), filename, ct)
				if err != nil {
					return e, err
				}
				continue
			}
		}
		switch {
		case ct == "text/plain":
			e.Text = p.body
		case ct == "text/html":
			e.HTML = p.body
		}
	}
	return e, nil
}

func (e *Email) Attach(r io.Reader, filename string, c string) (a *Attachment, err error) {
	var buffer bytes.Buffer
	if _, err = io.Copy(&buffer, r); err != nil {
		return
	}
	at := &Attachment{
		Filename:    filename,
		ContentType: c,
		Header:      textproto.MIMEHeader{},
		Content:     buffer.Bytes(),
	}
	e.Attachments = append(e.Attachments, at)
	return at, nil
}

func (e *Email) AttachFile(filename string) (a *Attachment, err error) {
	f, err := os.Open(filename)
	if err != nil {
		return
	}
	defer f.Close()

	ct := mime.TypeByExtension(filepath.Ext(filename))
	basename := filepath.Base(filename)
	return e.Attach(f, basename, ct)
}

func (e *Email) msgHeaders() (textproto.MIMEHeader, error) {
	r := make(textproto.MIMEHeader, len(e.Headers)+6)

	if e.Headers != nil {
		for _, h := range []string{"Reply-To", "To", "Cc", "From", "Subject", "Date", "Message-Id", "MIME-Version"} {
			if v, ok := e.Headers[h]; ok {
				r[h] = v
			}
		}
	}

	if _, ok := r["Reply-To"]; !ok && len(e.ReplyTo) > 0 {
		r.Set("Reply-To", strings.Join(e.ReplyTo, ", "))
	}

	if _, ok := r["To"]; !ok && len(e.To) > 0 {
		r.Set("To", strings.Join(e.To, ", "))
	}

	if _, ok := r["Cc"]; !ok && len(e.Cc) > 0 {
		r.Set("Cc", strings.Join(e.Cc, ", "))
	}

	if _, ok := r["Subject"]; !ok && e.Subject != "" {
		r.Set("Subject", e.Subject)
	}

	if _, ok := r["Message-Id"]; !ok {
		id, err := generateMessageID()
		if err != nil {
			return nil, err
		}
		r.Set("Message-Id", id)
	}

	if _, ok := r["From"]; !ok {
		r.Set("From", e.From)
	}

	if _, ok := r["Date"]; !ok {
		r.Set("Date", time.Now().Format(time.RFC1123Z))
	}

	if _, ok := r["MIME-Version"]; !ok {
		r.Set("MIME-Version", "1.0")
	}

	for field, vals := range e.Headers {
		if _, ok := r[field]; !ok {
			r[field] = vals
		}
	}
	return r, nil
}

func (e *Email) categorizeAttachments() (htmlRelated, others []*Attachment) {
	for _, a := range e.Attachments {
		if a.HTMLRelated {
			htmlRelated = append(htmlRelated, a)
		} else {
			others = append(others, a)
		}
	}
	return
}

func (e *Email) Bytes() ([]byte, error) {
	buff := bytes.NewBuffer(make([]byte, 0, 4096))

	headers, err := e.msgHeaders()
	if err != nil {
		return nil, err
	}

	htmlAttachments, otherAttachments := e.categorizeAttachments()
	if len(e.HTML) == 0 && len(htmlAttachments) > 0 {
		return nil, errors.New("there are HTML attachments, but no HTML body")
	}

	var (
		isMixed       = len(otherAttachments) > 0
		isAlternative = len(e.Text) > 0 && len(e.HTML) > 0
		isRelated     = len(e.HTML) > 0 && len(htmlAttachments) > 0
	)

	var w *multipart.Writer
	if isMixed || isAlternative || isRelated {
		w = multipart.NewWriter(buff)
	}
	switch {
	case isMixed:
		headers.Set("Content-Type", "multipart/mixed;\r\n boundary="+w.Boundary())
	case isAlternative:
		headers.Set("Content-Type", "multipart/alternative;\r\n boundary="+w.Boundary())
	case isRelated:
		headers.Set("Content-Type", "multipart/related;\r\n boundary="+w.Boundary())
	case len(e.HTML) > 0:
		headers.Set("Content-Type", "text/html; charset=UTF-8")
		headers.Set("Content-Transfer-Encoding", "quoted-printable")
	default:
		headers.Set("Content-Type", "text/plain; charset=UTF-8")
		headers.Set("Content-Transfer-Encoding", "quoted-printable")
	}
	headerToBytes(buff, headers)
	_, err = io.WriteString(buff, "\r\n")
	if err != nil {
		return nil, err
	}

	if len(e.Text) > 0 || len(e.HTML) > 0 {
		var (
			subWriter *multipart.Writer
		)

		if isMixed && isAlternative {
			subWriter = multipart.NewWriter(buff)
			header := textproto.MIMEHeader{
				"Content-Type": {"multipart/alternative;\r\n boundary=" + subWriter.Boundary()},
			}
			if _, err := w.CreatePart(header); err != nil {
				return nil, err
			}
		} else {
			subWriter = w
		}

		if len(e.Text) > 0 {
			if err := writeMessage(buff, e.Text, isMixed || isAlternative, "text/plain", subWriter); err != nil {
				return nil, err
			}
		}

		if len(e.HTML) > 0 {
			var (
				relatedWriter *multipart.Writer
			)

			messageWriter := subWriter

			if (isMixed || isAlternative) && len(htmlAttachments) > 0 {
				relatedWriter = multipart.NewWriter(buff)
				header := textproto.MIMEHeader{
					"Content-Type": {"multipart/related;\r\n boundary=" + relatedWriter.Boundary()},
				}
				if _, err := subWriter.CreatePart(header); err != nil {
					return nil, err
				}

				messageWriter = relatedWriter
			} else if isRelated && len(htmlAttachments) > 0 {
				relatedWriter = w
				messageWriter = w
			}

			if err := writeMessage(buff, e.HTML, isMixed || isAlternative || isRelated, "text/html", messageWriter); err != nil {
				return nil, err
			}

			if len(htmlAttachments) > 0 {
				for _, a := range htmlAttachments {
					a.setDefaultHeaders()
					ap, err := relatedWriter.CreatePart(a.Header)
					if err != nil {
						return nil, err
					}
					base64Wrap(ap, a.Content)
				}
				if isMixed || isAlternative {
					relatedWriter.Close()
				}
			}
		}
		if isMixed && isAlternative {
			if err := subWriter.Close(); err != nil {
				return nil, err
			}
		}
	}

	for _, a := range otherAttachments {
		a.setDefaultHeaders()
		ap, err := w.CreatePart(a.Header)
		if err != nil {
			return nil, err
		}
		base64Wrap(ap, a.Content)
	}
	if isMixed || isAlternative || isRelated {
		if err := w.Close(); err != nil {
			return nil, err
		}
	}
	return buff.Bytes(), nil
}

func (e *Email) Send(addr string, a smtp.Auth) error {
	to := make([]string, 0, len(e.To)+len(e.Cc)+len(e.Bcc))
	to = append(append(append(to, e.To...), e.Cc...), e.Bcc...)

	for i := 0; i < len(to); i++ {
		addr, err := mail.ParseAddress(to[i])
		if err != nil {
			return err
		}
		to[i] = addr.Address
	}

	if e.From == "" || len(to) == 0 {
		return errors.New("Must specify at least one From address and one To address")
	}

	sender, err := e.parseSender()
	if err != nil {
		return err
	}

	raw, err := e.Bytes()
	if err != nil {
		return err
	}
	return smtp.SendMail(addr, a, sender, to, raw)
}

func (e *Email) parseSender() (string, error) {
	if e.Sender != "" {
		sender, err := mail.ParseAddress(e.Sender)
		if err != nil {
			return "", err
		}
		return sender.Address, nil
	} else {
		from, err := mail.ParseAddress(e.From)
		if err != nil {
			return "", err
		}
		return from.Address, nil
	}
}

func (e *Email) SendWithTLS(addr string, a smtp.Auth, t *tls.Config) error {
	to := make([]string, 0, len(e.To)+len(e.Cc)+len(e.Bcc))
	to = append(append(append(to, e.To...), e.Cc...), e.Bcc...)
	for i := 0; i < len(to); i++ {
		addr, err := mail.ParseAddress(to[i])
		if err != nil {
			return err
		}
		to[i] = addr.Address
	}

	if e.From == "" || len(to) == 0 {
		return errors.New("Must specify at least one From address and one To address")
	}

	sender, err := e.parseSender()
	if err != nil {
		return err
	}

	raw, err := e.Bytes()
	if err != nil {
		return err
	}

	conn, err := tls.Dial("tcp", addr, t)
	if err != nil {
		return err
	}

	c, err := smtp.NewClient(conn, t.ServerName)
	if err != nil {
		return err
	}

	defer c.Close()

	if err = c.Hello("localhost"); err != nil {
		return err
	}

	if a != nil {
		if ok, _ := c.Extension("AUTH"); ok {
			if err = c.Auth(a); err != nil {
				return err
			}
		}
	}

	if err = c.Mail(sender); err != nil {
		return err
	}

	for _, addr := range to {
		if err = c.Rcpt(addr); err != nil {
			return err
		}
	}

	w, err := c.Data()
	if err != nil {
		return err
	}

	_, err = w.Write(raw)
	if err != nil {
		return err
	}

	err = w.Close()
	if err != nil {
		return err
	}
	return c.Quit()
}

func (e *Email) SendWithStartTLS(addr string, a smtp.Auth, t *tls.Config) error {
	to := make([]string, 0, len(e.To)+len(e.Cc)+len(e.Bcc))
	to = append(append(append(to, e.To...), e.Cc...), e.Bcc...)
	for i := 0; i < len(to); i++ {
		addr, err := mail.ParseAddress(to[i])
		if err != nil {
			return err
		}
		to[i] = addr.Address
	}

	if e.From == "" || len(to) == 0 {
		return errors.New("Must specify at least one From address and one To address")
	}

	sender, err := e.parseSender()
	if err != nil {
		return err
	}

	raw, err := e.Bytes()
	if err != nil {
		return err
	}

	c, err := smtp.Dial(addr)
	if err != nil {
		return err
	}
	defer c.Close()

	if err = c.Hello("localhost"); err != nil {
		return err
	}

	if ok, _ := c.Extension("STARTTLS"); ok {
		if err = c.StartTLS(t); err != nil {
			return err
		}
	}

	if a != nil {
		if ok, _ := c.Extension("AUTH"); ok {
			if err = c.Auth(a); err != nil {
				return err
			}
		}
	}

	if err = c.Mail(sender); err != nil {
		return err
	}

	for _, addr := range to {
		if err = c.Rcpt(addr); err != nil {
			return err
		}
	}

	w, err := c.Data()
	if err != nil {
		return err
	}

	_, err = w.Write(raw)
	if err != nil {
		return err
	}

	err = w.Close()
	if err != nil {
		return err
	}
	return c.Quit()
}

var MaxLineLength = 76

func base64Wrap(w io.Writer, b []byte) {
	const maxRaw = 57

	buffer := make([]byte, MaxLineLength+len("\r\n"))
	copy(buffer[MaxLineLength:], "\r\n")

	for len(b) >= maxRaw {
		base64.StdEncoding.Encode(buffer, b[:maxRaw])
		w.Write(buffer)
		b = b[maxRaw:]
	}

	if len(b) > 0 {
		out := buffer[:base64.StdEncoding.EncodedLen(len(b))]
		base64.StdEncoding.Encode(out, b)
		out = append(out, "\r\n"...)
		w.Write(out)
	}
}

func headerToBytes(buff io.Writer, header textproto.MIMEHeader) {
	for field, vals := range header {
		for _, subval := range vals {

			io.WriteString(buff, field)
			io.WriteString(buff, ": ")

			switch {
			case field == "Content-Type" || field == "Content-Disposition":
				buff.Write([]byte(subval))
			case field == "From" || field == "To" || field == "Cc" || field == "Bcc":
				participants := strings.Split(subval, ",")
				for i, v := range participants {
					addr, err := mail.ParseAddress(v)
					if err != nil {
						continue
					}
					participants[i] = addr.String()
				}
				buff.Write([]byte(strings.Join(participants, ", ")))
			default:
				buff.Write([]byte(mime.QEncoding.Encode("UTF-8", subval)))
			}
			io.WriteString(buff, "\r\n")
		}
	}
}

var maxBigInt = big.NewInt(math.MaxInt64)

func generateMessageID() (string, error) {
	t := time.Now().UnixNano()
	pid := os.Getpid()

	rint, err := rand.Int(rand.Reader, maxBigInt)
	if err != nil {
		return "", err
	}

	h, err := os.Hostname()
	if err != nil {
		h = "localhost.localdomain"
	}
	return fmt.Sprintf("<%d.%d.%d@%s>", t, pid, rint, h), nil
}

func writeMessage(buff io.Writer, msg []byte, multipart bool, mediaType string, w *multipart.Writer) error {
	if multipart {
		header := textproto.MIMEHeader{
			"Content-Type":              {mediaType + "; charset=UTF-8"},
			"Content-Transfer-Encoding": {"quoted-printable"},
		}
		if _, err := w.CreatePart(header); err != nil {
			return err
		}
	}

	qp := quotedprintable.NewWriter(buff)
	if _, err := qp.Write(msg); err != nil {
		return err
	}
	return qp.Close()
}

type trimReader struct {
	rd      io.Reader
	trimmed bool
}

func (tr *trimReader) Read(buf []byte) (int, error) {
	n, err := tr.rd.Read(buf)
	if err != nil {
		return n, err
	}
	if !tr.trimmed {
		t := bytes.TrimLeftFunc(buf[:n], unicode.IsSpace)
		tr.trimmed = true
		n = copy(buf, t)
	}
	return n, err
}

func handleAddressList(v []string) []string {
	res := []string{}
	for _, a := range v {
		w := strings.Split(a, ",")
		for _, addr := range w {
			decodedAddr, err := (&mime.WordDecoder{}).DecodeHeader(strings.TrimSpace(addr))
			if err == nil {
				res = append(res, decodedAddr)
			} else {
				res = append(res, addr)
			}
		}
	}
	return res
}

var ErrMissingBoundary = errors.New("No boundary found for multipart entity")

const (
	defaultContentType = "text/plain; charset=us-ascii"
)

func parseMIMEParts(hs textproto.MIMEHeader, b io.Reader) ([]*part, error) {
	var ps []*part
	if _, ok := hs["Content-Type"]; !ok {
		hs.Set("Content-Type", defaultContentType)
	}
	ct, params, err := mime.ParseMediaType(hs.Get("Content-Type"))
	if err != nil {
		return ps, err
	}
	if strings.HasPrefix(ct, "multipart/") {
		if _, ok := params["boundary"]; !ok {
			return ps, ErrMissingBoundary
		}
		mr := multipart.NewReader(b, params["boundary"])
		for {
			var buf bytes.Buffer
			p, err := mr.NextPart()
			if err == io.EOF {
				break
			}
			if err != nil {
				return ps, err
			}
			if _, ok := p.Header["Content-Type"]; !ok {
				p.Header.Set("Content-Type", defaultContentType)
			}
			subct, _, err := mime.ParseMediaType(p.Header.Get("Content-Type"))
			if err != nil {
				return ps, err
			}
			if strings.HasPrefix(subct, "multipart/") {
				sps, err := parseMIMEParts(p.Header, p)
				if err != nil {
					return ps, err
				}
				ps = append(ps, sps...)
			} else {
				var reader io.Reader
				reader = p
				const cte = "Content-Transfer-Encoding"
				if p.Header.Get(cte) == "base64" {
					reader = base64.NewDecoder(base64.StdEncoding, reader)
				}
				if _, err := io.Copy(&buf, reader); err != nil {
					return ps, err
				}
				ps = append(ps, &part{body: buf.Bytes(), header: p.Header})
			}
		}
	} else {
		switch hs.Get("Content-Transfer-Encoding") {
		case "quoted-printable":
			b = quotedprintable.NewReader(b)
		case "base64":
			b = base64.NewDecoder(base64.StdEncoding, b)
		}
		var buf bytes.Buffer
		if _, err := io.Copy(&buf, b); err != nil {
			return ps, err
		}
		ps = append(ps, &part{body: buf.Bytes(), header: hs})
	}
	return ps, nil
}

type Attachment struct {
	Filename    string
	ContentType string
	Header      textproto.MIMEHeader
	Content     []byte
	HTMLRelated bool
}

func (at *Attachment) setDefaultHeaders() {
	contentType := "application/octet-stream"
	if len(at.ContentType) > 0 {
		contentType = at.ContentType
	}
	at.Header.Set("Content-Type", contentType)

	if len(at.Header.Get("Content-Disposition")) == 0 {
		disposition := "attachment"
		if at.HTMLRelated {
			disposition = "inline"
		}
		at.Header.Set("Content-Disposition", fmt.Sprintf("%s;\r\n filename=\"%s\"", disposition, at.Filename))
	}
	if len(at.Header.Get("Content-ID")) == 0 {
		at.Header.Set("Content-ID", fmt.Sprintf("<%s>", at.Filename))
	}
	if len(at.Header.Get("Content-Transfer-Encoding")) == 0 {
		at.Header.Set("Content-Transfer-Encoding", "base64")
	}
}
