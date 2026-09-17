"""Check the Mobius expansion of the local zero-count charge used in
research/count-raising-reversible-automata-rokhlin-deficit-proof.md (part A, steps 1-5),
over G = Z x Z/2, where finite sets can have nontrivial stabilizers.

Binary alphabet, rest symbol 1, count = number of zeros. Random local rules f on
S = {-1,0,1} x Z/2 with f(all ones) = 1. Checks, for each rule:
  (a) q(Z) = |Phi(Z)| - |Z| equals sum_{nonempty V subset Z} Gamma(V) on random finite Z;
  (b) E_{mu_p}[f(x|S) = 0] - p equals sum over translation classes [V] of Gamma(V)/|Stab V| p^|V|,
      evaluated exactly at several rational p.
"""
import itertools, random
from fractions import Fraction

S = [(i, j) for i in (-1, 0, 1) for j in (0, 1)]
def add(g, h): return (g[0] + h[0], (g[1] + h[1]) % 2)
def neg(g): return (-g[0], (-g[1]) % 2)

def run(seed):
    rng = random.Random(seed)
    rule = {}
    for bits in itertools.product((0, 1), repeat=len(S)):
        rule[bits] = 1 if all(bits) else rng.randint(0, 1)
    def f_zero(T):  # T = set of zero sites in S; returns [output is 0]
        return 1 - rule[tuple(0 if s in T else 1 for s in S)]
    subsets = [frozenset(c) for r in range(len(S) + 1) for c in itertools.combinations(S, r)]
    u = {T: f_zero(T) - (1 if (0, 0) in T else 0) for T in subsets}
    v = {U: sum((-1) ** (len(U) - len(W)) * u[W] for W in subsets if W <= U) for U in subsets}
    def translate(V, h): return frozenset(add(h, x) for x in V)
    def Gamma(V):
        V = frozenset(V); tot = 0
        # h^-1 V subset S  <=>  V subset h S ; candidate h = x - s
        cands = {add(x, neg(s)) for x in V for s in S}
        for h in cands:
            W = translate(V, neg(h))
            if W <= set(S): tot += v[W]
        return tot
    # (a)
    for _ in range(40):
        Z = frozenset((rng.randint(-4, 4), rng.randint(0, 1)) for _ in range(rng.randint(0, 6)))
        sites = {add(z, neg(s)) for z in Z for s in S} | set(Z)
        out = sum(f_zero(frozenset(s for s in S if add(h, s) in Z)) for h in sites)
        q = out - len(Z)
        rhs = sum(Gamma(c) for r in range(1, len(Z) + 1) for c in itertools.combinations(sorted(Z), r))
        assert q == rhs, (seed, Z, q, rhs)
    # (b) classes: canonical form = lexicographically least translate containing... normalize by min element
    def canon(V):
        return min(tuple(sorted(translate(V, neg(x)))) for x in V)
    classes = {canon(U) for U in subsets if U}
    def stab_exact(V):
        V = frozenset(V); x0 = min(V)
        return len({add(x, neg(x0)) for x in V if translate(V, add(x, neg(x0))) == V})
    for p in (Fraction(1, 3), Fraction(1, 7), Fraction(2, 5)):
        lhs = sum(p ** len(T) * (1 - p) ** (len(S) - len(T)) * f_zero(T) for T in subsets) - p
        rhs = sum(Fraction(Gamma(V), stab_exact(V)) * p ** len(V) for V in classes)
        assert lhs == rhs, (seed, p, lhs, rhs)
    return max(stab_exact(V) for V in classes)

if __name__ == "__main__":
    for seed in range(12):
        m = run(seed)
    print("ok: 12 random rules; charge expansion and density formula exact; max stabilizer", m)
