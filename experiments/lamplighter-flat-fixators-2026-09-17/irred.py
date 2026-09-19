"""Sanity and irreducibility checks for cube lattices.
- normal forms: sorting a random word in order ABC, then re-sorting its normal form
  after a random shuffle of the rewriting (compare via left action on base vertex);
- level-k permutation group orders of each factor's letters on each other tree."""
import sys, random
from sympy.combinatorics import Permutation, PermutationGroup
from lattice import load

def check_assoc(C, trials=300):
    L = [(F, i) for F in 'ABC' for i in range(C.n[F])]
    for _ in range(trials):
        w = [random.choice(L) for _ in range(random.randint(1, 12))]
        n1 = C.normal(w, 'ABC')
        # evaluate as product of two halves
        k = random.randint(0, len(w))
        n2 = C.normal(list(C.normal(w[:k], 'ABC')) + list(C.normal(w[k:], 'ABC')), 'ABC')
        n3 = C.normal(list(C.normal(C.normal(w, 'CBA'), 'BCA')), 'ABC')
        if not (n1 == n2 == n3):
            return False
    return True

def level_orders(C, X, Y, kmax):
    out = []
    for k in range(1, kmax + 1):
        gens = [Permutation(C.level_perm(((X, i),), Y, k)) for i in range(C.n[X])]
        out.append(PermutationGroup(gens).order())
    return out

if __name__ == "__main__":
    path = sys.argv[1]; kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    with open(path) as f:
        nsol = sum(1 for l in f if l.startswith('{'))
    for s in range(nsol):
        C = load(path, s)
        print(f"sol {s} sizes {C.n} assoc_ok={check_assoc(C)}")
        for X, Y in [('A', 'B'), ('B', 'A'), ('A', 'C'), ('C', 'A'), ('B', 'C'), ('C', 'B')]:
            print(f"   {X} on T_{Y.lower()}: level orders {level_orders(C, X, Y, kmax)}")
