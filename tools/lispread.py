"""A Common Lisp reader sufficient for analyzing Maxima's sources.

Produces Python objects:
  Sym(name)          -- symbol, with name already mapped to the port's
                        convention (unescaped tokens lowercased; |escaped|
                        names case-inverted when uniform)
  int / Fraction / float
  Str(text)
  Char(c)
  list (proper lists) / DottedList(items, tail)
  Quote(kind, form)  -- kind in "quote", "function", "backquote", "comma",
                        "comma-at"
  MaximaExpr(text)   -- #$...$ reader macro
  Vector(items)
Each list carries .line (source line of the open paren) via LList subclass.
"""

from fractions import Fraction
import re


class Sym:
    __slots__ = ("name",)
    _table = {}

    def __new__(cls, name):
        s = cls._table.get(name)
        if s is None:
            s = object.__new__(cls)
            s.name = name
            cls._table[name] = s
        return s

    def __repr__(self):
        return self.name


class Str:
    __slots__ = ("text",)

    def __init__(self, text):
        self.text = text

    def __repr__(self):
        return '"%s"' % self.text


class Char:
    __slots__ = ("c",)

    def __init__(self, c):
        self.c = c

    def __repr__(self):
        return "#\\" + self.c


class LList(list):
    line = 0


class DottedList:
    def __init__(self, items, tail):
        self.items = items
        self.tail = tail
        self.line = 0

    def __repr__(self):
        return "(" + " ".join(map(repr, self.items)) + " . " + repr(self.tail) + ")"


class Quote:
    __slots__ = ("kind", "form")

    def __init__(self, kind, form):
        self.kind = kind
        self.form = form

    def __repr__(self):
        p = {"quote": "'", "function": "#'", "backquote": "`", "comma": ",",
             "comma-at": ",@"}[self.kind]
        return p + repr(self.form)


class MaximaExpr:
    def __init__(self, text):
        self.text = text

    def __repr__(self):
        return "#$" + self.text + "$"


class Vector:
    def __init__(self, items):
        self.items = items

    def __repr__(self):
        return "#(" + " ".join(map(repr, self.items)) + ")"


FEATURES = {"sbcl", "common-lisp", "ansi-cl", "cl", "unix", "x86-64", "64-bit",
            "ieee-floating-point", "darwin", "bsd", "little-endian",
            "mk-deps-complete", "unicode", "sb-unicode", "maxima"}


def invert_case(name):
    letters = [c for c in name if c.isalpha()]
    if letters and all(c.isupper() for c in letters):
        return name.lower()
    if letters and all(c.islower() for c in letters):
        return name.upper()
    return name


class Reader:
    def __init__(self, text, fname=""):
        self.s = text
        self.i = 0
        self.n = len(text)
        self.fname = fname
        self.line = 1

    def err(self, msg):
        raise SyntaxError("%s:%d: %s" % (self.fname, self.line, msg))

    def peek(self):
        return self.s[self.i] if self.i < self.n else ""

    def next(self):
        c = self.s[self.i]
        self.i += 1
        if c == "\n":
            self.line += 1
        return c

    def skip_ws(self):
        while self.i < self.n:
            c = self.s[self.i]
            if c in " \t\r\n\f":
                self.next()
            elif c == ";":
                while self.i < self.n and self.s[self.i] != "\n":
                    self.i += 1
            elif c == "#" and self.i + 1 < self.n and self.s[self.i + 1] == "|":
                depth = 0
                while self.i < self.n:
                    if self.s.startswith("#|", self.i):
                        depth += 1
                        self.i += 2
                    elif self.s.startswith("|#", self.i):
                        depth -= 1
                        self.i += 2
                        if depth == 0:
                            break
                    else:
                        self.next()
            else:
                break

    def read_all(self):
        forms = []
        while True:
            self.skip_ws()
            if self.i >= self.n:
                break
            self.toplevel = True
            self.cur_start_line = self.line
            start = self.cur_start_line
            f = self.read1()
            self.toplevel = False
            if f is not SKIP:
                forms.append((f, start))
        return forms

    def read(self):
        while True:
            self.skip_ws()
            if self.i >= self.n:
                if getattr(self, "toplevel", False):
                    return SKIP
                self.err("unexpected EOF")
            self.cur_start_line = self.line
            f = self.read1()
            if f is not SKIP:
                return f

    def read1(self):
        c = self.peek()
        if c == "(":
            line = self.line
            self.next()
            items = []
            while True:
                self.skip_ws()
                if self.peek() == ")":
                    self.next()
                    l = LList(items)
                    l.line = line
                    return l
                if self.peek() == "" :
                    self.err("EOF in list")
                if self.peek() == "." and self.i + 1 < self.n and self.s[self.i + 1] in " \t\n\r(":
                    self.next()
                    tail = self.read()
                    self.skip_ws()
                    if self.peek() != ")":
                        self.err("bad dotted list")
                    self.next()
                    d = DottedList(items, tail)
                    d.line = line
                    return d
                f = self.read1_ws()
                if f is not SKIP:
                    items.append(f)
        if c == ")":
            self.next()
            self.err("unexpected )")
        if c == "'":
            self.next()
            return Quote("quote", self.read())
        if c == "`":
            self.next()
            return Quote("backquote", self.read())
        if c == ",":
            self.next()
            if self.peek() == "@":
                self.next()
                return Quote("comma-at", self.read())
            if self.peek() == ".":
                self.next()
                return Quote("comma-at", self.read())
            return Quote("comma", self.read())
        if c == '"':
            self.next()
            out = []
            while True:
                ch = self.next()
                if ch == "\\":
                    out.append(self.next())
                elif ch == '"':
                    break
                else:
                    out.append(ch)
            return Str("".join(out))
        if c == "#":
            return self.read_dispatch()
        return self.read_token()

    def read1_ws(self):
        self.skip_ws()
        return self.read1()

    def read_dispatch(self):
        self.next()  # '#'
        c = self.next()
        if c == "'":
            return Quote("function", self.read())
        if c == "\\":
            # character
            ch = self.next()
            name = ch
            while self.i < self.n and (self.s[self.i].isalnum() or self.s[self.i] in "-_") and ch.isalpha():
                name += self.next()
            if len(name) == 1:
                return Char(name)
            names = {"space": " ", "newline": "\n", "tab": "\t", "return": "\r",
                     "linefeed": "\n", "page": "\f", "backspace": "\b",
                     "rubout": "\x7f", "nul": "\0", "null": "\0", "escape": "\x1b",
                     "esc": "\x1b", "bell": "\x07", "altmode": "\x1b"}
            low = name.lower()
            if low in names:
                return Char(names[low])
            if low.startswith("u+") or (low.startswith("u") and all(x in "0123456789abcdef" for x in low[1:]) and len(low) > 1):
                return Char(chr(int(low.lstrip("u+"), 16)))
            # e.g. #\a followed by letters -- treat first char
            return Char(name)
        if c == "+" or c == "-":
            feat = self.read()
            form = self.read()
            ok = self.feature_true(feat)
            if (c == "+") == ok:
                return form
            return SKIP
        if c == "(":
            self.i -= 1
            l = self.read1()
            return Vector(list(l))
        if c == "$":
            # Maxima expression up to the next unescaped '$'
            start = self.i
            while self.s[self.i] != "$":
                if self.s[self.i] == "\\":
                    self.i += 1
                if self.s[self.i] == "\n":
                    self.line += 1
                self.i += 1
            text = self.s[start:self.i]
            self.i += 1
            return MaximaExpr(text)
        if c == ":":
            tok = self.read_token()
            return Sym("#:" + tok.name) if isinstance(tok, Sym) else tok
        if c in "xX":
            tok = self.read_raw_token()
            return int(tok, 16)
        if c in "oO":
            return int(self.read_raw_token(), 8)
        if c in "bB":
            return int(self.read_raw_token(), 2)
        if c in "cC":
            l = self.read()
            return ("complex", l)
        if c == ".":
            form = self.read()
            return ("read-eval", form)
        if c.isdigit():
            num = c
            while self.peek().isdigit():
                num += self.next()
            d = self.next()
            if d in "aA":
                return ("array", self.read())
            if d == "=":
                return self.read()
            if d == "#":
                return Sym("#" + num + "#")
            if d in "rR":
                return int(self.read_raw_token(), int(num))
            self.err("unknown #" + num + d)
        if c == "|":
            self.err("stray #|")
        if c == "p" or c == "P":
            return self.read()
        if c == "*":
            return ("bitvector", self.read_raw_token())
        self.err("unknown dispatch #" + c)

    def feature_true(self, feat):
        if isinstance(feat, Sym):
            n = feat.name.lstrip(":")
            return n in FEATURES
        if isinstance(feat, list):
            op = feat[0].name.lstrip(":")
            args = feat[1:]
            if op == "and":
                return all(self.feature_true(a) for a in args)
            if op == "or":
                return any(self.feature_true(a) for a in args)
            if op == "not":
                return not self.feature_true(args[0])
        if isinstance(feat, tuple) and feat[0] == "read-eval":
            # #+#.(cl:if ...) idiom: assume the feature is present
            return True
        return False

    def read_raw_token(self):
        start = self.i
        while self.i < self.n and self.s[self.i] not in " \t\r\n()'\";`,":
            self.i += 1
        return self.s[start:self.i]

    def read_token(self):
        # read a symbol or number, handling |...| and \ escapes
        out = []
        escaped_any = False
        segments = []  # (text, escaped)
        while self.i < self.n:
            c = self.s[self.i]
            if c in " \t\r\n()'\";`,":
                break
            if c == "|":
                self.i += 1
                buf = []
                while self.s[self.i] != "|":
                    if self.s[self.i] == "\\":
                        self.i += 1
                    if self.s[self.i] == "\n":
                        self.line += 1
                    buf.append(self.s[self.i])
                    self.i += 1
                self.i += 1
                segments.append(("".join(buf), True))
                escaped_any = True
            elif c == "\\":
                self.i += 1
                segments.append((self.s[self.i], True))
                self.i += 1
                escaped_any = True
            else:
                segments.append((c, False))
                self.i += 1
        if not segments:
            self.err("empty token at %r" % self.s[self.i:self.i + 20])
        raw = "".join(t for t, _ in segments)
        if not escaped_any:
            num = parse_number(raw)
            if num is not None:
                return num
            name = raw.upper()
        else:
            name = "".join(t if e else t.upper() for t, e in segments)
        # strip package prefixes
        for pre in ("CL-USER::", "CL::", "CL:", "COMMON-LISP:", "MAXIMA::",
                    "MAXIMA:", "BIGFLOAT::", "BIGFLOAT:", "INTL:", "SB-EXT:",
                    "SB-INT:", "SB-KERNEL:", "SB-IMPL::", "SB-SYS:", "MK:", "MK::",
                    "CL-INFO::", "CL-INFO:", "GETTEXT:", "SB-UNIX:", "SB-ALIEN:",
                    "SB-C:", "SB-DEBUG:", "SB-PROFILE:", "SB-IMPL:", "SB-THREAD:",
                    "F2CL-LIB:", "SLATEC:", "SLATEC::", "COMMAND-LINE:"):
            if name.startswith(pre) and len(name) > len(pre):
                name = name[len(pre):]
                break
        if name.startswith(":"):
            return Sym(":" + invert_case(name[1:]))
        return Sym(invert_case(name))


class _Skip:
    def __repr__(self):
        return "<skip>"


SKIP = _Skip()

_num_re = re.compile(r"^[+-]?(\d+\.?\d*|\.\d+)([eEdDfFsSlL][+-]?\d+)?$")


def parse_number(tok):
    if re.match(r"^[+-]?\d+\.?$", tok):
        return int(tok.rstrip("."))
    if re.match(r"^[+-]?\d+/\d+$", tok):
        a, b = tok.split("/")
        return Fraction(int(a), int(b))
    if _num_re.match(tok) and any(ch in tok for ch in ".eEdDfFsSlL"):
        t = re.sub(r"[dDfFsSlL]", "e", tok)
        try:
            return float(t)
        except ValueError:
            return None
    return None


def read_file(path):
    with open(path, encoding="utf-8", errors="replace") as f:
        text = f.read()
    return Reader(text, path).read_all()
