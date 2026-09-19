"""SAT search for one-vertex torsion-free cube complexes whose universal cover is
T_a x T_b x T_c (lattices acting simply transitively on vertices).

Letters of each factor are 0..n-1 with inverse i^1.  A VH-structure on (X,Y) is a
function f(x,y) = (y',x') meaning x y = y' x' in the group; the cube condition says
that rewriting a b c -> c'' b'' a'' gives the same result both ways.
Usage: python3 cubesat.py nA nB nC [count] [nocommute]  -> JSON lines of solutions."""
import sys, json, itertools
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

class Pool:
    def __init__(self): self.n = 0; self.d = {}
    def v(self, *k):
        if k not in self.d:
            self.n += 1; self.d[k] = self.n
        return self.d[k]

def build(nA, nB, nC, nocommute, trans=False):
    P = Pool(); cl = []
    sizes = {'A': nA, 'B': nB, 'C': nC}
    pairs = [('A', 'B'), ('A', 'C'), ('B', 'C')]
    def F(X, Y, x, y, y2, x2): return P.v('F', X, Y, x, y, y2, x2)
    for X, Y in pairs:
        nx, ny = sizes[X], sizes[Y]
        for x in range(nx):
            for y in range(ny):
                lits = [F(X, Y, x, y, y2, x2) for y2 in range(ny) for x2 in range(nx)]
                cl.append(lits)
                for i in range(len(lits)):
                    for j in range(i + 1, len(lits)):
                        cl.append([-lits[i], -lits[j]])
                cl.append([-F(X, Y, x, y, y ^ 1, x ^ 1)])       # no torsion
                if nocommute:
                    cl.append([-F(X, Y, x, y, y, x)])
                for y2 in range(ny):
                    for x2 in range(nx):
                        v = F(X, Y, x, y, y2, x2)
                        cl.append([-v, F(X, Y, x ^ 1, y2, y, x2 ^ 1)])
                        cl.append([-v, F(X, Y, x2, y ^ 1, y2 ^ 1, x)])
                        cl.append([-v, F(X, Y, x2 ^ 1, y2 ^ 1, y ^ 1, x ^ 1)])
    if trans:   # level-1 local actions transitive in all six directions
        for X, Y in pairs:
            nx, ny = sizes[X], sizes[Y]
            for y1 in range(ny):
                for y2 in range(ny):
                    if y1 != y2:   # some x maps y1 to y2 : x y1 = y2 x'
                        cl.append([F(X, Y, x, y1, y2, x2) for x in range(nx) for x2 in range(nx)])
            for x1 in range(nx):
                for x2 in range(nx):
                    if x1 != x2:   # some y maps x1 to x2 : y x1 = x2 y'  i.e. f(x2,y')=(y,x1)
                        cl.append([F(X, Y, x2, yy, y, x1) for y in range(ny) for yy in range(ny)])
    AB = lambda a, b, b2, a2: F('A', 'B', a, b, b2, a2)
    AC = lambda a, c, c2, a2: F('A', 'C', a, c, c2, a2)
    BC = lambda b, c, c2, b2: F('B', 'C', b, c, c2, b2)
    for a in range(nA):
        for b in range(nB):
            for c in range(nC):
                G = lambda comp, val: P.v('G', a, b, c, comp, val)
                for comp, n in (('a', nA), ('b', nB), ('c', nC)):
                    lits = [G(comp, v) for v in range(n)]
                    for i in range(n):
                        for j in range(i + 1, n):
                            cl.append([-lits[i], -lits[j]])
                # way 1: b c -> c1 b1 ; a c1 -> c2 a1 ; a1 b1 -> b2 a2
                for c1 in range(nC):
                    for b1 in range(nB):
                        for c2 in range(nC):
                            for a1 in range(nA):
                                base = [-BC(b, c, c1, b1), -AC(a, c1, c2, a1)]
                                cl.append(base + [G('c', c2)])
                                cl.append(base + [P.v('R1', a, b, c, a1, b1)])
                for a1 in range(nA):
                    for b1 in range(nB):
                        for b2 in range(nB):
                            for a2 in range(nA):
                                base = [-P.v('R1', a, b, c, a1, b1), -AB(a1, b1, b2, a2)]
                                cl.append(base + [G('b', b2)]); cl.append(base + [G('a', a2)])
                # way 2: a b -> b3 a3 ; a3 c -> c3 a4 ; b3 c3 -> c4 b4
                for b3 in range(nB):
                    for a3 in range(nA):
                        for c3 in range(nC):
                            for a4 in range(nA):
                                base = [-AB(a, b, b3, a3), -AC(a3, c, c3, a4)]
                                cl.append(base + [G('a', a4)])
                                cl.append(base + [P.v('R2', a, b, c, b3, c3)])
                for b3 in range(nB):
                    for c3 in range(nC):
                        for c4 in range(nC):
                            for b4 in range(nB):
                                base = [-P.v('R2', a, b, c, b3, c3), -BC(b3, c3, c4, b4)]
                                cl.append(base + [G('c', c4)]); cl.append(base + [G('b', b4)])
    return P, cl, sizes, pairs

def decode(P, model, sizes, pairs):
    m = set(l for l in model if l > 0)
    out = {}
    for k, v in P.d.items():
        if k[0] == 'F' and v in m:
            _, X, Y, x, y, y2, x2 = k
            out.setdefault(X + Y, {})[f"{x},{y}"] = [y2, x2]
    return out

if __name__ == "__main__":
    nA, nB, nC = map(int, sys.argv[1:4])
    count = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    nocommute = len(sys.argv) > 5 and sys.argv[5] == 'nocommute'
    P, cl, sizes, pairs = build(nA, nB, nC, nocommute)
    print(f"# vars={P.n} clauses={len(cl)}", file=sys.stderr)
    fvars = [v for k, v in P.d.items() if k[0] == 'F']
    import random
    seed = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    rng = random.Random(seed)
    fkeys = [k for k in P.d if k[0] == 'F']
    with Cadical153(bootstrap_with=cl) as s:
        found = 0; tries = 0
        while found < count and tries < 50 * count:
            tries += 1
            assum = [P.d[rng.choice(fkeys)] for _ in range(int(sys.argv[7]) if len(sys.argv) > 7 else 0)]
            if not s.solve(assumptions=assum):
                continue
            model = s.get_model()
            sol = decode(P, model, sizes, pairs)
            sol['sizes'] = [nA, nB, nC]
            print(json.dumps(sol)); sys.stdout.flush()
            found += 1
            s.add_clause([-v for v in fvars if model[v - 1] > 0])
        print(f"# found={found}", file=sys.stderr)
