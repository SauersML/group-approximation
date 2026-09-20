#!/usr/bin/env python3
"""Locally constant abelian covers of the Cantor action of G0/<<r5>> versus V.

G0 = <a,b,c | a^2, b^3, (ab)^4, c^2, (ac)^3>, V = G0/<<r5,r6,r7,r8>> (Bleak--Quick (2.4)),
a = (00 01), b = (01 10 11), c = (1 00), maps acting on the right on C = {0,1}^N.

A voltage rule of depth k assigns to each generator x in {a,b,c} and each binary word p of
length k a value phi_x(p) in Z/m.  It defines the skew action (z,s).x = (z.x, s + phi_x(z[:k]))
on C x Z/m, i.e. a lift of a,b,c to the Higman--Thompson-type group of C x Z/m.  The lifted
triple satisfies a relator r (trivial in V) iff the voltage of the r-loop at every point z is 0.
Each such voltage is a linear form in the phi's that depends only on a finite prefix of z, so
the whole condition is a finite linear system.

If the r6 (or r7, r8) loop form at some cylinder is NOT in the span of the r1..r5 loop forms,
there is a rule phi satisfying r1..r5 exactly while r6 acts nontrivially: then r6 is not in the
normal closure of r5 in G0, i.e. G0/<<r5>> != V.  If it IS in the span for all tested (k, m),
no locally constant abelian cover of depth k separates them (inconclusive for the question).
"""
import sys

import numpy as np

def expand(tex):
    """Parse the Bleak--Quick TeX word syntax: letters, (..)^{n}, x^{-1}."""
    import re
    s = tex.replace(" ", "")
    pos = [0]

    def peek():
        return s[pos[0]] if pos[0] < len(s) else ""

    def inv(w):
        return [(g, -e) for g, e in reversed(w)]

    def seq(stop):
        out = []
        while peek() and peek() != stop:
            if peek() == "(":
                pos[0] += 1
                w = seq(")")
                pos[0] += 1
            else:
                w = [(peek(), 1)]
                pos[0] += 1
            while peek() == "^":
                m = re.match(r"\^\{(-?\d+)\}", s[pos[0]:])
                n = int(m.group(1))
                pos[0] += len(m.group(0))
                w = w * n if n >= 0 else inv(w) * (-n)
            out += w
        return out

    w = seq("")
    red = []
    for g, e in w:
        if red and red[-1] == (g, -e):
            red.pop()
        else:
            red.append((g, e))
    return red


TEX = {  # verbatim from Bleak--Quick (2.4), as transcribed in verify_thompson_steinberg_presentation.py
    "a2": "a^{2}", "b3": "b^{3}", "ab4": "(ab)^{4}", "c2": "c^{2}", "ac3": "(ac)^{3}",
    "r5": "(cab^{-1}aba)^{2}cb(cabab^{-1}a)^{2}",
    "r6": "a(cb)^{2}a(b^{-1}c)^{2}bcabcb^{-1}cab^{-1}acb^{-1}(cb)^{2}ab^{-1}",
    "r7": "ab^{-1}cbc(ab^{-1})^{2}cbcb^{-1}a(b^{-1}c)^{2}babcb^{-1}cab^{-1}",
    "r8": "ca(b^{-1}c)^{2}bacabacbc(b^{-1}ca)^{2}b(cb^{-1})^{2}(acb)^{2}cb^{-1}cab^{-1}",
}
WORDS = {name: expand(t) for name, t in TEX.items()}

# Bleak--Quick (2.3) words (R2, split R3, commutators R4a, R4b, R5), parsed with the repo's
# transcription and parser (conjugate X^{W} = W^-1 X W, [X,Y] = X^-1 Y^-1 X Y).
sys.path.insert(0, __import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)),
                                            "..", "nonsofic-certificates", "presentations"))
try:
    import verify_thompson_steinberg_presentation as _vt  # noqa: E402
    for _name, _t in zip(("R2", "Rsplit", "R4a", "R4b", "R5"), _vt.R_WORDS[3:]):
        WORDS[_name] = _vt.parse_tex(_t)
except Exception as _e:  # the leavitt module import may fail outside the certificate dir
    print("note: (2.3) words unavailable:", _e, file=sys.stderr)

# prefix rules: (prefix, replacement) for each generator, right action
RULES = {
    ("a", 1): [("00", "01"), ("01", "00"), ("1", "1")],
    ("b", 1): [("00", "00"), ("01", "10"), ("10", "11"), ("11", "01")],
    ("c", 1): [("1", "00"), ("00", "1"), ("01", "01")],
}
RULES[("a", -1)] = [(q, p) for p, q in RULES[("a", 1)]]
RULES[("b", -1)] = [(q, p) for p, q in RULES[("b", 1)]]
RULES[("c", -1)] = [(q, p) for p, q in RULES[("c", 1)]]
NEED = 2  # digits that always determine the applicable rule


def act(s, letter):
    """Apply a generator to a known prefix s; None if s is too short to decide."""
    for p, q in RULES[letter]:
        if s.startswith(p):
            return q + s[len(p):]
        if p.startswith(s):
            return None
    raise AssertionError((s, letter))


def loop_forms(word, k):
    """Yield (start_prefix, {var: coeff}) for the loop of `word` on every cylinder."""
    out = []
    stack = [""]
    while stack:
        p0 = stack.pop()
        s = p0
        form = {}
        ok = True
        for g, e in word:
            if e == 1:
                if len(s) < max(k, NEED):
                    ok = False
                    break
                var = (g, s[:k])
                t = act(s, (g, 1))
                if t is None:
                    ok = False
                    break
                form[var] = form.get(var, 0) + 1
                s = t
            else:
                t = act(s, (g, -1))
                if t is None or len(t) < max(k, NEED):
                    ok = False
                    break
                var = (g, t[:k])
                form[var] = form.get(var, 0) - 1
                s = t
        if not ok:
            stack.append(p0 + "0")
            stack.append(p0 + "1")
            continue
        assert s == p0, ("relator not trivial in V", word, p0, s)
        out.append((p0, {v: c for v, c in form.items() if c}))
    return out


def rank_mod(rows, p):
    """Row-reduce a list of dense numpy int64 rows mod p; return echelon (pivots, matrix)."""
    if not rows:
        return [], np.zeros((0, 0), dtype=np.int64)
    A = np.array(rows, dtype=np.int64) % p
    piv = []
    r = 0
    nrows, ncols = A.shape
    for col in range(ncols):
        nz = np.nonzero(A[r:, col])[0]
        if len(nz) == 0:
            continue
        i = r + nz[0]
        A[[r, i]] = A[[i, r]]
        inv = pow(int(A[r, col]), p - 2, p) if p > 2 else 1
        A[r] = (A[r] * inv) % p
        others = np.nonzero(A[:, col])[0]
        others = others[others != r]
        if len(others):
            A[others] = (A[others] - np.outer(A[others, col], A[r])) % p
        piv.append(col)
        r += 1
        if r == nrows:
            break
    return piv, A[:r]


def reduce_vec(v, piv, E, p):
    v = v % p
    for i, col in enumerate(piv):
        if v[col]:
            v = (v - v[col] * E[i]) % p
    return v


def run(k, p, base=("a2", "b3", "ab4", "c2", "ac3", "r5"), tests=("r6", "r7", "r8")):
    varlist = [(g, "".join(bits)) for g in "abc" for bits in __import__("itertools").product("01", repeat=k)]
    idx = {v: i for i, v in enumerate(varlist)}
    n = len(varlist)

    def dense(form):
        v = np.zeros(n, dtype=np.int64)
        for var, c in form.items():
            v[idx[var]] += c
        return v % p

    rows = set()
    counts = {}
    for name in base:
        forms = loop_forms(WORDS[name], k)
        counts[name] = len(forms)
        for _, f in forms:
            d = dense(f)
            if d.any():
                rows.add(tuple(d))
    piv, E = rank_mod([list(r) for r in rows], p)
    result = {"k": k, "p": p, "vars": n, "base_rank": len(piv), "cylinders": counts, "separating": {}}
    for name in tests:
        forms = loop_forms(WORDS[name], k)
        bad = []
        for p0, f in forms:
            red = reduce_vec(dense(f), piv, E, p)
            if red.any():
                bad.append(p0)
        result["separating"][name] = (len(forms), len(bad), bad[:5])
    # rank with all eight
    rows_all = set(rows)
    for name in tests:
        for _, f in loop_forms(WORDS[name], k):
            d = dense(f)
            if d.any():
                rows_all.add(tuple(d))
    piv2, _ = rank_mod([list(r) for r in rows_all], p)
    result["all_rank"] = len(piv2)
    return result


if __name__ == "__main__":
    ks = [int(x) for x in sys.argv[1].split(",")] if len(sys.argv) > 1 else [1, 2, 3, 4]
    ps = [int(x) for x in sys.argv[2].split(",")] if len(sys.argv) > 2 else [2, 3]
    base = tuple(sys.argv[3].split(",")) if len(sys.argv) > 3 else ("a2", "b3", "ab4", "c2", "ac3", "r5")
    tests = tuple(sys.argv[4].split(",")) if len(sys.argv) > 4 else ("r6", "r7", "r8")
    for k in ks:
        for p in ps:
            print(run(k, p, base, tests), flush=True)
