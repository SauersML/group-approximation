"""Exact arithmetic for Thompson's group V acting on binary words.

An element is given as a product of prefix cycles such as "(00 01)", "(01 10 11)".
A prefix cycle (a_1 ... a_k) of pairwise incomparable binary cylinders maps
a_i w -> a_(i+1) w (indices mod k) and fixes every word outside the cylinders.

Words in generators are lists of (name, exponent) with exponent +1 or -1.
Two conventions are supported for reading a word g_1 g_2 ... g_m:
  "right": x . (g_1 g_2 ... g_m) = (... (x . g_1) ...) . g_m   (apply g_1 first)
  "left":  (g_1 g_2 ... g_m)(x) = g_1(g_2(... g_m(x)))         (apply g_m first)
A word is the identity of V iff it fixes every binary string of a length M that
exceeds every prefix the evaluation needs; eval raises Short if M is too small.
"""
import itertools
import re


class Short(Exception):
    pass


def parse_cycles(spec):
    """'(00 01)(1 000 010)' -> list of cycles, each a list of cylinder strings."""
    cycles = [c.split() for c in re.findall(r"\(([^()]*)\)", spec)]
    for c in cycles:
        for a, b in itertools.combinations(c, 2):
            if a.startswith(b) or b.startswith(a):
                raise ValueError("comparable cylinders in %s" % spec)
    return cycles


def apply_cycles(cycles, s, inverse=False):
    """Apply the product of disjoint prefix cycles (as a function) to string s."""
    for c in cycles:
        k = len(c)
        for i, a in enumerate(c):
            if len(s) < len(a) and a.startswith(s):
                raise Short(s)
            if s.startswith(a):
                j = (i - 1) % k if inverse else (i + 1) % k
                return c[j] + s[len(a):]
    return s


def parse_generator(spec):
    """A generator is a product of factors read left to right (right action).

    spec is either one cycle string '(01 10 11)' (disjoint cycles, one factor) or a
    list of such strings, e.g. ['(00 01)', '(10 110)', '(10 111)'] for
    t_{00,01} t_{10,110} t_{10,111}.  Returns a list of factors (cycle lists).
    """
    if isinstance(spec, str):
        return [parse_cycles(spec)]
    return [parse_cycles(x) for x in spec]


def compile_word(word, gens):
    """gens: name -> list of factors (from parse_generator). word: list of (name, +-1)."""
    out = []
    for n, e in word:
        factors = gens[n]
        if e > 0:
            out.extend((f, 1) for f in factors)
        else:
            out.extend((f, -1) for f in reversed(factors))
    return out


def eval_word(cword, s, convention):
    seq = cword if convention == "right" else list(reversed(cword))
    for cycles, e in seq:
        s = apply_cycles(cycles, s, inverse=(e < 0))
    return s


def is_identity(word, gens, convention, M=14):
    cword = compile_word(word, gens)
    for bits in itertools.product("01", repeat=M):
        s = "".join(bits)
        t = eval_word(cword, s, convention)
        if t != s:
            return False
    return True


def parse_word(text):
    """Parse 'a b^-1 c^2' style words; names are identifiers, exponents integers."""
    out = []
    for tok in text.split():
        m = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_]*)(?:\^(-?\d+))?", tok)
        if not m:
            raise ValueError(tok)
        n, e = m.group(1), int(m.group(2) or 1)
        out.extend([(n, 1 if e > 0 else -1)] * abs(e))
    return out
