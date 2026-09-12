"""Parse group words written in TeX, e.g. 'v^{-1}u(u^{2}v^{-1})^{2}', into letter lists.

Letters are single lowercase characters.  Exponents are ^n or ^{n}.  Parentheses
group, and a parenthesised group may carry an exponent.  A conjugate (w)^{s}
with a word exponent s is written by callers as conj(w, s) instead.
Output: list of (letter, +1 or -1).
"""


def _inv(word):
    return [(x, -e) for x, e in reversed(word)]


def _power(word, n):
    if n >= 0:
        return word * n
    return _inv(word) * (-n)


def parse(tex):
    s = tex.replace(" ", "")
    pos = 0

    def exponent():
        nonlocal pos
        if pos < len(s) and s[pos] == "^":
            pos += 1
            if s[pos] == "{":
                end = s.index("}", pos)
                val = int(s[pos + 1:end])
                pos = end + 1
            else:
                start = pos
                if s[pos] == "-":
                    pos += 1
                while pos < len(s) and s[pos].isdigit():
                    pos += 1
                val = int(s[start:pos])
            return val
        return 1

    def seq():
        nonlocal pos
        out = []
        while pos < len(s) and s[pos] != ")":
            if s[pos] == "(":
                pos += 1
                inner = seq()
                assert s[pos] == ")", tex
                pos += 1
                out += _power(inner, exponent())
            elif s[pos].isalpha():
                letter = s[pos]
                pos += 1
                out += _power([(letter, 1)], exponent())
            else:
                raise ValueError("unexpected %r in %s" % (s[pos], tex))
        return out

    w = seq()
    if pos != len(s):
        raise ValueError("unbalanced: " + tex)
    return w


def conj(w, s):
    """w^s = s^-1 w s."""
    return _inv(s) + w + s


def free_reduce(word):
    out = []
    for x in word:
        if out and out[-1][0] == x[0] and out[-1][1] == -x[1]:
            out.pop()
        else:
            out.append(x)
    return out
