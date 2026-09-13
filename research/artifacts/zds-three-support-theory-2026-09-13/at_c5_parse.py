#!/usr/bin/env python3
"""Parse Table tab-C5 of Abdollahi--Taheri (arXiv:1612.00934, main.tex) and
compare its starred relators with the census types of cycle_relators.py."""
import re, sys
from cycle_relators import cred, inv, relator, tuples, tuple_class, classify

tex = open(sys.argv[1]).read()
start = tex.index(r"\label{tab-C5}")
end = tex.index(r"\end{longtable}", start)
body = tex[start:end]

def parse(expr):
    """Parse a LaTeX word like h_2^2h_3^{-1}(h_2^{-1}h_3)^2."""
    pos = 0
    def atom_seq():
        nonlocal pos
        out = []
        while pos < len(expr):
            if expr.startswith("h_2", pos) or expr.startswith("h_3", pos):
                g = 1 if expr[pos + 2] == "2" else 2
                pos += 3
                w = [g]
            elif expr[pos] == "(":
                pos += 1
                w = atom_seq()
                assert expr[pos] == ")", expr
                pos += 1
            elif expr[pos] == ")":
                return out
            else:
                raise ValueError("bad char %r in %s" % (expr[pos], expr))
            k = 1
            if pos < len(expr) and expr[pos] == "^":
                pos += 1
                if expr[pos] == "{":
                    j = expr.index("}", pos)
                    k = int(expr[pos + 1:j])
                    pos = j + 1
                else:
                    k = int(expr[pos])
                    pos += 1
            out.extend(w * k if k > 0 else inv(w) * (-k))
        return out
    return cred(atom_seq())

rows = {}
for m in re.finditer(r"\$(\d+)\$&\$([^$]*)=1(\s*\\ \*)?\$", body):
    n = int(m.group(1))
    rows[n] = (parse(m.group(2).replace(" ", "")), bool(m.group(3)))
print("parsed rows:", len(rows), "starred:", sum(1 for v in rows.values() if v[1]))

def cyclic_forms(u):
    u = cred(u)
    forms = set()
    for v in (u, inv(u)):
        for s in range(len(v)):
            forms.add(tuple(v[s:] + v[:s]))
    return forms

census = {}
for T in tuples(5):
    c = tuple_class(T)
    census.setdefault(c, relator(list(c)))
types = {c: classify(r)[0] for c, r in census.items()}
unmatched = []
stats = {}
for n in sorted(rows):
    r, star = rows[n]
    hits = [c for c, rr in census.items() if cyclic_forms(rr) & cyclic_forms(r)]
    t = types[hits[0]] if hits else "?"
    stats[(star, t)] = stats.get((star, t), 0) + 1
    if not hits:
        unmatched.append(n)
    if star and t not in ("A", "S"):
        print("starred row %d relator %s census type %s" % (n, r, t))
    if (not star) and t in ("A", "S"):
        print("unstarred row %d relator %s census type %s" % (n, r, t))
print("unmatched rows:", unmatched)
print("(starred, census type) counts:", sorted(stats.items()))
