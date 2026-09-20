"""Independent verification for the two-bank SFT on F_2 (see bank_sft.py for the definition).

Written from the edge rules directly (no bitmask code from treesft.py).

(1) essential alphabet E: greatest set in which every symbol has an a-successor, a-predecessor,
    b-successor and b-predecessor. Every symbol of E occurs in a point (extend greedily on the tree).

(2) path mixing: least r such that for every reduced word u of length r (hence every length >= r)
    and all s, t in E there is a u-walk from s to t. Layered DP over (reachable set, last letter).

(3) half-tree mixing HM(r): for a vertex v entered from its parent by letter delta, and a globally
    admissible pattern p on a finite set F of the half-tree below v, let W(v) be the set of symbols at
    v that extend p on the half-tree. HM(r): W(v) = E whenever d(v, F) >= r.
    W-sets satisfy W(v) = fix(v) & AND_{eps != delta^-1} Pred_eps(W(v eps)), fix(v) = E or a singleton.
    Family_0[delta] = all achievable W (least fixpoint, empty sets = inadmissible, dropped).
    Family_{k+1}[delta] = {AND_eps Pred_eps(W_eps) : W_eps in Family_k[eps]} (v not in F).
    HM(r) holds iff Family_r[delta] = {E} for all delta.

    HM(r) implies strong irreducibility with gap 2r - 1: if d(F, G) >= 2r - 1, then at every vertex c
    one of p|below c, q|below c has all its sites at distance >= r from c, so its W-set is E, so
    Pred(W_p & W_q) = Pred(W_p) & Pred(W_q). By induction W_{p u q} = W_p & W_q at every vertex; rooting
    at a site of F gives W_{p u q}(root) = W_p(root), which is nonempty.

(4) no finite orbit (exact LP, re-done here with fractions-free integrality not needed): bank count.

Usage: python3 verify_bank.py K c d
"""
import sys
from itertools import product

K, c, d = (int(x) for x in sys.argv[1:4])
SYMS = [(tau, A, B) for tau in "PN" for A in range(K + 1) for B in range(K + 1)]


def a_edge(s, t):
    return (t[0] == "P" and t[1] == min(s[1] + 1, K)) or (t[0] == "N" and s[1] >= c and t[1] == s[1] - c)


def b_edge(s, t):
    return (t[0] == "N" and t[2] == min(s[2] + 1, K)) or (t[0] == "P" and s[2] >= d and t[2] == s[2] - d)


# letters: 0 = a, 1 = a^-1, 2 = b, 3 = b^-1 ; succ[x][s] = symbols t with (s, t) allowed on edge g -> g x
INV = [1, 0, 3, 2]


def build_succ(E):
    succ = [dict() for _ in range(4)]
    for s in E:
        succ[0][s] = frozenset(t for t in E if a_edge(s, t))
        succ[1][s] = frozenset(t for t in E if a_edge(t, s))
        succ[2][s] = frozenset(t for t in E if b_edge(s, t))
        succ[3][s] = frozenset(t for t in E if b_edge(t, s))
    return succ


E = frozenset(SYMS)
while True:
    succ = build_succ(E)
    newE = frozenset(s for s in E if all(succ[x][s] for x in range(4)))
    if newE == E:
        break
    E = newE
print(f"K={K} c={c} d={d}: {len(SYMS)} symbols, essential |E| = {len(E)}")
print("  E =", " ".join(f"{t}{A}{B}" for t, A, B in sorted(E)))

# (2) path mixing
layer = {(frozenset([s]), -1) for s in E}
r_path = None
for L in range(1, 60):
    nxt = set()
    for S, last in layer:
        for x in range(4):
            if last >= 0 and x == INV[last]:
                continue
            T = frozenset().union(*(succ[x][s] for s in S))
            nxt.add((T, x))
    layer = nxt
    if all(S == E for S, _ in layer):
        r_path = L
        break
print("  path-mixing constant r =", r_path)


# (3) half-tree mixing
def pred(x, W):
    return frozenset(s for s in E if succ[x][s] & W)


def combine(delta, fam, fixes):
    """All nonempty fix & AND_{eps != INV[delta]} Pred_eps(W_eps), W_eps in fam[eps]."""
    acc = {E}
    for eps in range(4):
        if eps == INV[delta]:
            continue
        P = {pred(eps, W) for W in fam[eps]}
        acc = {X & Y for X in acc for Y in P if X & Y}
    return {X & f for X in acc for f in fixes if X & f}


fixes0 = [E] + [frozenset([s]) for s in E]
fam = [{E} | {frozenset([s]) for s in E} for _ in range(4)]
while True:
    new = [fam[dl] | combine(dl, fam, fixes0) for dl in range(4)]
    if new == fam:
        break
    fam = new
print("  achievable half-tree W-sets per entry letter:", [len(f) for f in fam])
r_hm = None
famk = fam
seen = {}
for k in range(1, 200):
    famk = [combine(dl, famk, [E]) | {E} for dl in range(4)]
    if all(f == {E} for f in famk):
        r_hm = k
        break
    key = tuple(frozenset(f) for f in famk)
    if key in seen:
        print(f"  Family_k is periodic: Family_{k} = Family_{seen[key]}, sizes", [len(f) for f in famk])
        for dl in range(4):
            W = min((f for f in famk[dl] if f != E), key=len)
            print(f"    entry {'aAbB'[dl]}: a W-set != E at every depth, |W| = {len(W)}, missing",
                  " ".join(f"{t}{A}{B}" for t, A, B in sorted(E - W)))
        break
    seen[key] = k
print("  half-tree mixing constant r_HM =", r_hm,
      "-> strongly irreducible with gap", None if r_hm is None else 2 * r_hm - 1)

# (4) finite orbits: on a finite Schreier graph every a-cycle has #P >= c #N (A-bank returns) and every
# b-cycle #N >= d #P, so if c*d > 1 then #P = #N = 0: impossible on a nonempty graph.
print("  c*d > 1 (no periodic point by bank count):", c * d > 1)
