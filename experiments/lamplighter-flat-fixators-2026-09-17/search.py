"""Randomized search for cube lattices all of whose six local automaton actions
have growing level-k orders (k=1,2,3), a proxy for irreducibility of every
2-dimensional sublattice (hence of Lambda).
Usage: python3 search.py nA nB nC seed nassum maxtries out.jsonl"""
import sys, json, random
from pysat.solvers import Cadical153
from sympy.combinatorics import Permutation, PermutationGroup
from cubesat import build, decode
from lattice import Cube

DIRS = [('A', 'B'), ('B', 'A'), ('A', 'C'), ('C', 'A'), ('B', 'C'), ('C', 'B')]

def orders(C, X, Y, kmax=3):
    out = []
    for k in range(1, kmax + 1):
        gens = [Permutation(C.level_perm(((X, i),), Y, k)) for i in range(C.n[X])]
        out.append(PermutationGroup(gens).order())
    return out

if __name__ == "__main__":
    nA, nB, nC, seed, nassum, maxtries = map(int, sys.argv[1:7]); outp = sys.argv[7]
    P, cl, sizes, pairs = build(nA, nB, nC, True, trans=(len(sys.argv) > 8 and sys.argv[8] == "trans"))
    rng = random.Random(seed)
    fkeys = [k for k in P.d if k[0] == 'F']
    fvars = [P.d[k] for k in fkeys]
    good = 0
    with Cadical153(bootstrap_with=cl) as s, open(outp, 'a') as fo:
        for t in range(maxtries):
            assum = [P.d[rng.choice(fkeys)] for _ in range(nassum)]
            if not s.solve(assumptions=assum):
                continue
            model = s.get_model()
            sol = decode(P, model, sizes, pairs); sol['sizes'] = [nA, nB, nC]
            s.add_clause([-v for v in fvars if model[v - 1] > 0])
            C = Cube(sol)
            ords = {}
            ok = True
            for X, Y in DIRS:
                o = orders(C, X, Y, 2)
                ords[X + Y] = o
                if not (o[0] < o[1]):
                    ok = False; break
            print(t, "ok" if ok else "no", ords); sys.stdout.flush()
            if ok:
                sol['orders'] = ords
                fo.write(json.dumps(sol) + "\n"); fo.flush(); good += 1
    print("good", good)
