"""Sanity check for the seed-propagation law (honest-decode-trees-must-be-cut-in-ug-compositions).

Model: an outer game Phi with sites Z (all on one side for simplicity, constraints
are pairs (z1,z2) with a random permutation predicate on labels [R]).  The UG U has
alphabet [K]; each site z owns a block of B vertices; the planted honest labelling
sigma encodes the outer label of z on its block; U-edges inside T_z (a random
spanning tree of the block, plus cross edges) carry the permutations that sigma
satisfies, then a fraction eta' of edges (by weight) is corrupted.

Checks, over random instances:
  (1) whenever T_z is sigma-clean, Dec_z(sigma|D_z) lies in the seed list Lambda_z
      (|Lambda_z| = K);
  (2) Pr_c[T_z1 or T_z2 dirty] <= (kappa1 + kappa2) * eta', with kappa the load;
  (3) the uniformly random list choice has expected value >= p / K^2.
"""
import random

def perm(K, rng):
    p = list(range(K)); rng.shuffle(p); return p

def trial(rng, nZ=40, B=6, K=5, R=5, ncons=120, eta=0.03):
    # outer label of each site, and encoding enc(z, label) -> block labelling
    lab = [rng.randrange(R) for _ in range(nZ)]
    enc_tab = [[[rng.randrange(K) for _ in range(B)] for _ in range(R)] for _ in range(nZ)]
    def dec(z, block):
        best = min(range(R), key=lambda r: sum(a != b for a, b in zip(block, enc_tab[z][r])))
        return best
    sigma = {(z, i): enc_tab[z][lab[z]][i] for z in range(nZ) for i in range(B)}
    # tree edges inside each block: random spanning tree, permutation consistent with sigma
    edges = []  # (u, v, pi) meaning x_v = pi[x_u]
    tree = {z: [] for z in range(nZ)}
    for z in range(nZ):
        order = list(range(B)); rng.shuffle(order)
        for j in range(1, B):
            u = (z, order[rng.randrange(j)]); v = (z, order[j])
            pi = perm(K, rng)
            # make sigma satisfy it
            a, b = sigma[u], sigma[v]
            k = pi.index(b); pi[k], pi[a] = pi[a], pi[k]
            tree[z].append(len(edges)); edges.append([u, v, pi])
    m = len(edges)
    w = [1.0 / m] * m
    # corrupt edges of total weight about eta
    bad = set(rng.sample(range(m), max(1, int(eta * m))))
    for e in bad:
        u, v, pi = edges[e]
        a = sigma[u]; c = rng.randrange(K - 1)
        c = c if c < pi[a] else c + 1
        k = pi.index(c); pi[k], pi[a] = pi[a], pi[k]
    viol = sum(w[e] for e in range(m) if edges[e][2][sigma[edges[e][0]]] != sigma[edges[e][1]])
    # outer constraints: permutation predicates satisfied by lab (completeness 1)
    cons = []
    for _ in range(ncons):
        z1, z2 = rng.sample(range(nZ), 2)
        q = perm(R, rng); k = q.index(lab[z2]); q[k], q[lab[z1]] = q[lab[z1]], q[k]
        cons.append((z1, z2, q))
    # seed lists
    def propagate(z, a):
        root = edges[tree[z][0]][0]
        val = {root: a}; changed = True
        while changed:
            changed = False
            for e in tree[z]:
                u, v, pi = edges[e]
                if u in val and v not in val:
                    val[v] = pi[val[u]]; changed = True
                elif v in val and u not in val:
                    val[u] = pi.index(val[v]); changed = True
        return dec(z, [val[(z, i)] for i in range(B)])
    lists = {z: [propagate(z, a) for a in range(K)] for z in range(nZ)}
    clean = {z: all(edges[e][2][sigma[edges[e][0]]] == sigma[edges[e][1]] for e in tree[z]) for z in range(nZ)}
    ok1 = all(dec(z, [sigma[(z, i)] for i in range(B)]) in lists[z] for z in range(nZ) if clean[z])
    # load: Pr_c[e in T_z1(c)] / w(e), each side
    k1 = max(sum(1 for c in cons if e in tree[c[0]]) / ncons / w[e] for e in range(m))
    k2 = max(sum(1 for c in cons if e in tree[c[1]]) / ncons / w[e] for e in range(m))
    dirty = sum(1 for c in cons if not (clean[c[0]] and clean[c[1]])) / ncons
    ok2 = dirty <= (k1 + k2) * viol + 1e-12
    good = [c for c in cons if clean[c[0]] and clean[c[1]]
            and c[2][dec(c[0], [sigma[(c[0], i)] for i in range(B)])] == dec(c[1], [sigma[(c[1], i)] for i in range(B)])]
    p = len(good) / ncons
    ev = sum(sum(1 for a in lists[c[0]] for b in lists[c[1]] if c[2][a] == b) / K**2 for c in cons) / ncons
    ok3 = ev >= p / K**2 - 1e-12
    return ok1, ok2, ok3, dirty, (k1 + k2) * viol, p, ev

def main():
    rng = random.Random(20260919)
    n = 200; fails = [0, 0, 0]; worst = 0.0
    for _ in range(n):
        r = trial(rng, eta=rng.choice([0.01, 0.03, 0.1, 0.3]))
        for i in range(3):
            fails[i] += (not r[i])
        worst = max(worst, r[3] / r[4] if r[4] > 0 else 0)
    print("trials", n)
    print("list-membership failures", fails[0])
    print("load-bound failures", fails[1])
    print("E[val] >= p/K^2 failures", fails[2])
    print("max dirty/(kappa eta') ratio %.3f" % worst)
    print("PASS" if sum(fails) == 0 else "FAIL")

if __name__ == "__main__":
    main()
