# verify_vtf_cert.py -- lane hl-hyperbolic-rf-2, 2026-09-14. Independent of GAP.
# Checks a certificate written by cert_vtf.g for a Caprace-Conder-Kaluba-Witzel trivalent triangle group
# G_k^{n0,n1,n2} = <a,b,c | a^3, b^3, c^3, R_ab, R_bc, R_ca> (arXiv:2011.09276):
#   (1) the permutations a, b, c satisfy every relator, so they define a homomorphism G -> S_degree;
#   (2) the images of the vertex groups <a,b>, <b,c>, <c,a> have orders 3*n0/2, 3*n1/2, 3*n2/2, the orders
#       of the abstract vertex groups (each acts simply transitively on the 3n/2 edges of its cubic link
#       graph with n vertices), so the homomorphism is injective on every vertex group;
#   (3) the coset graphs Gamma(<x,y>; <x>, <y>) of the images have girths 2r_i with sum 1/r_i < 1.
# Given (1)-(3), Theorem 3.1(iv) of CCKW makes G virtually torsion-free.
# Usage: python3 verify_vtf_cert.py <certfile>
import re, sys
from fractions import Fraction

def load(path):
    f, rels = {}, []
    for line in open(path):
        line = line.strip()
        if not line: continue
        k, v = line.split("=", 1)
        if k == "rel": rels.append(v)
        else: f[k] = v
    return f, rels

def perm(lst):
    return tuple(int(x) - 1 for x in re.findall(r"\d+", lst))

def mul(p, q):  # GAP convention: i^(p*q) = (i^p)^q
    return tuple(q[i] for i in p)

def inv(p):
    r = [0] * len(p)
    for i, j in enumerate(p): r[j] = i
    return tuple(r)

def power(p, k):
    e = tuple(range(len(p)))
    base = p if k >= 0 else inv(p)
    for _ in range(abs(k)): e = mul(e, base)
    return e

def evaluate(word, gens):
    toks = re.findall(r"[abc]|\^-?\d+|[()*]", word)
    if "".join(toks) != word.replace(" ", ""): raise ValueError("unparsed characters in %r" % word)
    pos = 0
    ident = tuple(range(len(gens["a"])))
    def factor():
        nonlocal pos
        t = toks[pos]
        if t == "(":
            pos += 1; val = seq()
            if toks[pos] != ")": raise ValueError("missing ) in %r" % word)
            pos += 1
        elif t in "abc":
            val = gens[t]; pos += 1
        else:
            raise ValueError("unexpected %r in %r" % (t, word))
        if pos < len(toks) and toks[pos].startswith("^"):
            val = power(val, int(toks[pos][1:])); pos += 1
        return val
    def seq():
        nonlocal pos
        val = factor()
        while pos < len(toks) and toks[pos] == "*":
            pos += 1; val = mul(val, factor())
        return val
    val = seq()
    if pos != len(toks): raise ValueError("trailing tokens in %r" % word)
    return val

def closure(gs):
    ident = tuple(range(len(gs[0])))
    seen, frontier = {ident}, [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gs:
                y = mul(x, g)
                if y not in seen: seen.add(y); nxt.append(y)
        frontier = nxt
    return seen

def coset_graph_girth(X, x, y):
    # vertices: right cosets <x>g and <y>g; element g joins <x>g and <y>g
    def coset(sub, g): return frozenset(mul(h, g) for h in sub)
    Sx, Sy = closure([x]), closure([y])
    adj = {}
    for g in X:
        u, v = ("x", coset(Sx, g)), ("y", coset(Sy, g))
        adj.setdefault(u, set()).add(v); adj.setdefault(v, set()).add(u)
    best = None
    for s in adj:
        dist, par, q = {s: 0}, {s: None}, [s]
        for u in q:
            for w in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1; par[w] = u; q.append(w)
                elif par[u] != w:
                    c = dist[u] + dist[w] + 1
                    if best is None or c < best: best = c
    return best

f, rels = load(sys.argv[1])
name = f["name"]
ns = [int(x) for x in re.match(r"G_\d+\^\{(\d+),(\d+),(\d+)\}", name).groups()]
deg = int(f["degree"])
gens = {k: perm(f[k]) for k in "abc"}
assert all(len(gens[k]) == deg for k in "abc"), "degree mismatch"
assert all(sorted(gens[k]) == list(range(deg)) for k in "abc"), "not permutations"
ident = tuple(range(deg))
bad = [w for w in rels if evaluate(w, gens) != ident]
print("name", name, "degree", deg, "relators", len(rels), "failing", bad)
pairs = [("a", "b"), ("b", "c"), ("c", "a")]
orders, girths = [], []
for (s, t), n in zip(pairs, ns):
    X = closure([gens[s], gens[t]])
    orders.append(len(X))
    girths.append(coset_graph_girth(X, gens[s], gens[t]))
expected = [3 * n // 2 for n in ns]
curv = sum(Fraction(2, g) for g in girths)
print("vertex image orders", orders, "expected", expected, "link girths", girths, "sum 1/r_i", curv)
ok = not bad and orders == expected and curv < 1
print("CERTIFICATE", "VALID" if ok else "INVALID")
sys.exit(0 if ok else 1)
