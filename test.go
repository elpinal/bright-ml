package main

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/pkg/errors"
)

func main() {
	for d, args := range map[string][]string{"typecheck": {"-typecheck"}, "parse": {"-parse"}} {
		n, err := run(d, args)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Test failed: %v\n", err)
			switch x := err.(type) {
			case *Error:
				fmt.Fprint(os.Stderr, x.stderr)
			}
			os.Exit(1)
		}

		fmt.Printf("Test(%s) succeeded: %d cases passed\n", d, n)
	}

	if err := check_parser_conflicts(); err != nil {
		fmt.Fprintf(os.Stderr, "Test failed: %v\n", err)
		switch x := err.(type) {
		case *Error:
			fmt.Fprint(os.Stderr, x.stderr)
		}
		os.Exit(1)
	}
}

type Error struct {
	err    error
	stderr string
}

func (e *Error) Error() string {
	return e.err.Error()
}

func run(d string, args []string) (n int, err error) {
	dir := filepath.Join("tests", d)
	f, err := os.Open(dir)
	if err != nil {
		return n, err
	}
	defer f.Close()

	names, err := f.Readdirnames(0)
	if err != nil {
		return n, err
	}

	for _, name := range names {
		if !strings.HasSuffix(name, ".bml") {
			continue
		}

		var buf bytes.Buffer
		cmd := exec.Command("./bright-ml", append(args, filepath.Join(dir, name))...)
		cmd.Stderr = &buf
		if err := cmd.Run(); err != nil {
			return n, &Error{err: errors.Wrap(err, name), stderr: buf.String()}
		}
		n++
	}
	return n, nil
}

func check_parser_conflicts() error {
	word := "conflict"

	cmd := exec.Command("make", "-B", "make_parser.sml")
	bs, err := cmd.Output()
	if err != nil {
		return err
	}
	if strings.Contains(string(bs), word) {
		return &Error{err: errors.New("ambiguous grammar"), stderr: string(bs)}
	}
	return nil
}
