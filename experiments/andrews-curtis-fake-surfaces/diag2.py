#!/usr/bin/env python3
# diag2.py -- map Fagan-Qiu-Wang census rows to our canonical codes; report their rows we lack,
# duplicate rows, and our classes their census lacks.  usage: diag2.py t [nosmall]
import sys, itertools, collections
import fsac
t = int(sys.argv[1]); nosmall = len(sys.argv) > 2
gs = fsac.load_graphs(t); S = [fsac.Surface(A) for A in gs]

def auts(s, A):
    H = len(s.vert); E = H // 2; out = []
    for p in itertools.permutations(range(t)):
        if any(A[p[u]][p[w]] != A[u][w] for u in range(t) for w in range(t)): continue
        phi = [-1]*H; used = [False]*E
        def rec(e):
            if e == E: out.append(list(phi)); return
            for e2 in range(E):
                if used[e2]: continue
                for sgn in (0, 1):
                    a, b = 2*e2+sgn, 2*e2+1-sgn
                    if s.vert[a] != p[s.vert[2*e]] or s.vert[b] != p[s.vert[2*e+1]]: continue
                    phi[2*e], phi[2*e+1] = a, b; used[e2] = True; rec(e+1); used[e2] = False
        rec(0)
    return out
AUT = [auts(S[i], gs[i]) for i in range(len(gs))]

def next_of(s, code):
    nxt = {}
    for e in range(s.E):
        d = code % 6; code //= 6
        for k in range(3): nxt[(2*e, k)] = (2*e+1, fsac.P[d][k]); nxt[(2*e+1, fsac.P[d][k])] = (2*e, k)
    return nxt
def encode(s, nxt):
    code = 0
    for e in reversed(range(s.E)):
        q = tuple(nxt[(2*e, k)][1] for k in range(3)); assert all(nxt[(2*e, k)][0] == 2*e+1 for k in range(3))
        code = code*6 + fsac.P.index(q)
    return code
def canon(gi, code):
    s = S[gi-1]; nxt = next_of(s, code); best = None
    for phi in AUT[gi-1]:
        nn = {}
        for (h, k), (h2, k2) in nxt.items():
            nn[(phi[h], s.oth[phi[h]].index(phi[s.oth[h][k]]))] = (phi[h2], s.oth[phi[h2]].index(phi[s.oth[h2][k2]]))
        c = encode(s, nn); best = c if best is None or c < best else best
    return best

def parse(tok):
    w = []; neg = False; i = 0
    while i < len(tok):
        ch = tok[i]
        if ch == "-": neg = True; i += 1; continue
        if ch == "1" and i+1 < len(tok) and tok[i+1] == "0": v = 10; i += 2
        else: v = int(ch); i += 1
        w.append(-v if neg else v); neg = False
    return w

def row_to_code(gi, disks):
    s = S[gi-1]
    loops = [e for e in range(s.E) if s.vert[2*e] == s.vert[2*e+1]]
    nonloops = [e for e in range(s.E) if e not in loops]
    for flips in itertools.product((0, 1), repeat=len(nonloops)):
        fl = dict(zip(nonloops, flips))
        def ends(a):   # (start half-edge, end half-edge) of letter a under this orientation
            e = abs(a)-1; h0, h1 = 2*e, 2*e+1
            if fl.get(e, 0): h0, h1 = h1, h0
            return (h0, h1) if a > 0 else (h1, h0)
        ok = True; corners = collections.Counter(); nxt = {}
        for w in disks:
            n = len(w)
            for i in range(n):
                _, hend = ends(w[i]); hnext, _ = ends(w[(i+1) % n])
                if s.vert[hend] != s.vert[hnext] or hend == hnext: ok = False; break
                corners[frozenset((hend, hnext))] += 1
            if not ok: break
            for i in range(n):
                hs, he = ends(w[i]); _, hprev_end = ends(w[i-1]); hnext, _ = ends(w[(i+1) % n])
                a = (hs, s.oth[hs].index(hprev_end)); b = (he, s.oth[he].index(hnext))
                if nxt.get(a, b) != b or nxt.get(b, a) != a: ok = False; break
                nxt[a] = b; nxt[b] = a
            if not ok: break
        if ok and len(corners) == 6*t and max(corners.values()) == 1 and len(nxt) == 12*t:
            return encode(s, nxt)
    return None

ours = set()
for line in open(f"classes-t{t}.txt"):
    _, g, code, ml = map(int, line.split())
    if not nosmall or ml > 2: ours.add((g, code))
theirs = collections.Counter(); bad = 0
for line in open("Fake-Surfaces/fakesurfaces.csv"):
    f = line.strip().split(",")
    if int(f[0]) != t: continue
    g = int(f[1]); disks = [parse(f[i]) for i in range(2, len(f), 3) if f[i] != ""]
    c = row_to_code(g, disks)
    if c is None: bad += 1; print("UNMAPPABLE", line.strip()); continue
    theirs[(g, canon(g, c))] += 1
dups = [k for k, v in theirs.items() if v > 1]
print(f"t={t} nosmall={nosmall} ours={len(ours)} their_rows={sum(theirs.values())} their_classes={len(theirs)} unmappable={bad} dup_classes={len(dups)}")
print("their classes not ours:", sorted(set(theirs) - ours)[:10])
extra = sorted(ours - set(theirs)); print("our classes not theirs:", len(extra))
for g, c in extra[:12]: print("  extra", g, c, S[g-1].words(c))
