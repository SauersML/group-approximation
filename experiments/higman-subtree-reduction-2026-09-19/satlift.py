#!/usr/bin/env python3
"""satlift.py -- decide by SAT whether a level-B model of H(n1,n2,n3,n4) (optionally / <<[a,c]^2>>) with
a = (x -> x + 2^J) extends to a level-K model on the binary tree.

Points of level K are x in Z/2^K; bit j of x is the level-(j+1) choice.  A tree automorphism g is given by switch
bits s_g(j, y), y < 2^j:  bit j of g(x) = bit j of x  XOR  s_g(j, x mod 2^j).  Below level B the switches of
b, c, d are those of the base model (a line of `glift ... dump`); the switches at bits B..K-1 are SAT variables.
a is fixed: s_a(j, y) = 1 if j = J, carry(bits J..j-1 of y all 1) if j > J, 0 if j < J.

Every relator is imposed at every point x of level K by walking the word letter by letter (a power g^e is walked
e mod 2^(K+1) steps; cycle lengths divide 2^K).  Low bits (< B) of every path point are constants given by the base
model; bits >= B are literals.  The instance is satisfiable iff the base model has a level-K lift (not up to any
symmetry: this is a pure existence test).  SAT answers are re-checked by direct permutation arithmetic.

usage: satlift.py J K e=n1,n2,n3,n4 [noR] [solver=cd] < dumpfile      (B is read off the dump lines)
"""
import sys
from pysat.solvers import Solver

args = sys.argv[1:]
J, K = int(args[0]), int(args[1])
EX = [3, 3, 3, 3]; USE_R = True; SOLVER = 'cd'
for s in args[2:]:
    if s.startswith('e='): EX = [int(t) for t in s[2:].split(',')]
    elif s == 'noR': USE_R = False
    elif s.startswith('solver='): SOLVER = s[7:]
A, Bg, C, D = 0, 1, 2, 3
MOD = 1 << (K + 1)
# relators as (gen, sign, count): y^-1 x y x^-n
def conj(x, y, n): return [(y, -1, 1), (x, 1, 1), (y, 1, 1), (x, -1, n % MOD)]
RELS = [conj(Bg, A, EX[0]), conj(C, Bg, EX[1]), conj(D, C, EX[2]), conj(A, D, EX[3])]
if USE_R: RELS.append([(A, -1, 1), (C, -1, 1), (A, 1, 1), (C, 1, 1)] * 2)


class CNF:
    def __init__(self): self.n = 0; self.cl = []
    def new(self): self.n += 1; return self.n
    def xor(self, x, y):
        if isinstance(x, bool) and isinstance(y, bool): return x != y
        if isinstance(x, bool): x, y = y, x
        if isinstance(y, bool): return -x if y else x
        o = self.new()
        self.cl += [[-x, -y, -o], [x, y, -o], [x, -y, o], [-x, y, o]]
        return o
    def band(self, x, y):
        if isinstance(x, bool): return y if x else False
        if isinstance(y, bool): return x if y else False
        o = self.new(); self.cl += [[-o, x], [-o, y], [o, -x, -y]]; return o
    def mux(self, sel, table):   # table[u] for u = int of sel bits (sel[0] = lowest)
        cons = [(i, b) for i, b in enumerate(sel) if isinstance(b, bool)]
        sym = [(i, b) for i, b in enumerate(sel) if not isinstance(b, bool)]
        base = sum(1 << i for i, b in cons if b)
        if not sym: return table[base]
        o = self.new()
        for u in range(1 << len(sym)):
            idx = base; sl = []
            for t, (i, b) in enumerate(sym):
                if (u >> t) & 1: idx |= 1 << i; sl.append(-b)
                else: sl.append(b)
            t = table[idx]
            if isinstance(t, bool): self.cl.append(sl + ([o] if t else [-o]))
            else: self.cl += [sl + [-t, o], sl + [t, -o]]
        return o


def solve_base(perms, B):
    """perms: dict g -> list (level-B permutation of Z/2^B) for g in b,c,d."""
    N = 1 << B
    f = CNF()
    S = {g: {j: [f.new() for _ in range(1 << j)] for j in range(B, K)} for g in (Bg, C, D)}
    inv = {g: [0] * N for g in perms}
    for g, p in perms.items():
        for x, y in enumerate(p): inv[g][y] = x

    def step(g, sgn, low, hi):
        if g == A:   # x -> x +- 2^J, switch = carry / borrow
            if sgn > 0: s = low + (1 << J); c = s >= N; nl = s % N
            else: s = low - (1 << J); c = s < 0; nl = s % N
            if J >= B: c = True   # (only J == B possible: the carry enters bit J)
            out = []
            for b in hi:
                out.append(f.xor(b, c))
                c = f.band(c, b if sgn > 0 else (not b if isinstance(b, bool) else -b))
            return nl, out
        if sgn > 0:
            nl = perms[g][low]; out = []
            for t, b in enumerate(hi):
                j = B + t; tab = S[g][j]
                sel_idx = [(low >> i) & 1 == 1 for i in range(B)] + hi[:t]
                out.append(f.xor(b, f.mux(sel_idx, tab)))
            return nl, out
        nl = inv[g][low]; out = []
        for t, b in enumerate(hi):
            j = B + t; tab = S[g][j]
            sel_idx = [(nl >> i) & 1 == 1 for i in range(B)] + out[:t]
            out.append(f.xor(b, f.mux(sel_idx, tab)))
        return nl, out

    for rel in RELS:
        for x in range(1 << K):
            low = x % N; hi = [((x >> j) & 1) == 1 for j in range(B, K)]
            for g, sgn, cnt in rel:
                for _ in range(cnt): low, hi = step(g, sgn, low, hi)
            assert low == x % N, "base model violates a relator"
            for j, b in zip(range(B, K), hi):
                want = ((x >> j) & 1) == 1
                if isinstance(b, bool):
                    if b != want: return False, None, f
                else: f.cl.append([b] if want else [-b])
    with Solver(name=SOLVER, bootstrap_with=f.cl) as sv:
        ok = sv.solve()
        model = set(l for l in sv.get_model() if l > 0) if ok else None
    if not ok: return False, None, f
    # build full level-K permutations and verify directly
    P = {}
    for g in (Bg, C, D):
        P[g] = [0] * (1 << K)
        for x in range(1 << K):
            y = perms[g][x % N]
            for j in range(B, K):
                y |= ((((x >> j) & 1) ^ (S[g][j][x % (1 << j)] in model)) << j)
            P[g][x] = y
    P[A] = [(x + (1 << J)) % (1 << K) for x in range(1 << K)]
    assert verify(P), "SAT model fails direct check"
    return True, P, f


def verify(P):
    n = len(P[A]); invs = {g: [0] * n for g in P}
    for g in P:
        for x, y in enumerate(P[g]): invs[g][y] = x
    for g in P:   # tree automorphism check
        for m in range(1, K + 1):
            for x in range(n):
                if P[g][x] % (1 << m) != P[g][x % (1 << m)] % (1 << m): return False
    for rel in RELS:
        for x in range(n):
            p = x
            for g, sgn, cnt in rel:
                for _ in range(cnt): p = P[g][p] if sgn > 0 else invs[g][p]
            if p != x: return False
    return True


if __name__ == '__main__':
    nsat = nuns = 0
    for line in sys.stdin:
        if not line.startswith('M'): continue
        parts = line.split('|')[1:]
        perms = {g: [int(t) for t in parts[i].split()] for i, g in enumerate((Bg, C, D))}
        B = len(perms[Bg]).bit_length() - 1
        ok, P, f = solve_base(perms, B)
        if ok:
            nsat += 1
            print("EXT", line.strip())
            if nsat == 1:
                print("FIRST SAT base:", line.strip())
                print("model", {g: P[g] for g in P})
        else: nuns += 1
        sys.stdout.flush()
    print(f"J {J} K {K} exps {EX} R {int(USE_R)} : bases {nsat + nuns}, extendable {nsat}, not extendable {nuns}")
