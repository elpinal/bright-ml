package main

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"io/ioutil"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

var update = flag.Bool("update", false, "update golden files")

func main() {
	flag.Parse()

	for d, args := range map[string][]string{
		"typecheck": {"-typecheck"},
		"parse":     {"-parse"},
		"eval":      {},
	} {
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

	fmt.Println("Test(grammar) succeeded: unambiguous grammar")
}

type Error struct {
	err      error
	stderr   string
	filename string
}

func (e *Error) Error() string {
	if e.filename != "" {
		return fmt.Sprintf("%s: %s", e.filename, e.err.Error())
	}
	return e.err.Error()
}

func run(d string, args []string) (n int, err error) {
	pwd, err := os.Getwd()
	if err != nil {
		return n, err
	}

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
		var output bytes.Buffer
		cmd := exec.Command("./bright-ml", append(args, filepath.Join(dir, name))...)
		cmd.Stderr = &buf
		cmd.Stdout = &output
		cmd.Env = append(os.Environ(), "BML_PATH="+pwd)
		if err := cmd.Run(); err != nil {
			return n, &Error{err: err, filename: name, stderr: buf.String()}
		}
		if d == "eval" {
			golden := filepath.Join(dir, strings.ReplaceAll(name, ".bml", ".golden"))
			if *update {
				err := ioutil.WriteFile(golden, output.Bytes(), 0644)
				if err != nil {
					return n, err
				}
			}
			expected, err := ioutil.ReadFile(golden)
			if err != nil {
				return n, err
			}
			got := output.String()
			if got != string(expected) {
				return n, fmt.Errorf("%s: evaluation result differs from the golden file", filepath.Join(dir, name))
			}
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
