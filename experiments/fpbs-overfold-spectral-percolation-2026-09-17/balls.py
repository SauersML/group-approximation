"""Class kill for closure counting: sets A with F(A) >= |A| at every scale.

A = (disjoint union of Schreier balls X_c of radius r) x (all atom types).
F(A) >= sum_c F(X_c x types), since a hyperedge inside one ball-block is not
inside another.  If F/|A| > 1 for single balls, then prefixes of a greedy
packing give sets A of every size up to the packing's total with
F(A) > |A|, so no upper bound on F can contradict Lemma 1 of the (W) proof
(F(C) >= |C| - |S|) at any stage mu = |C|/n <= total.
Also reports the lawful-layer analogue F_LLL(X)/|X| (it stays < 1).
Usage: python3 balls.py j n radius seed
"""
import sys
import random
from hyper import build, instantiate, random_level, act_tables


def ball(act, q0, r):
    seen = {q0}
    fr = [q0]
    for _ in range(r):
        nf = []
        for q in fr:
            for k in range(4):
                x = act[k][q]
                if x not in seen:
                    seen.add(x)
                    nf.append(x)
        fr = nf
    return seen


def main():
    j, n, r, seed = (int(x) for x in sys.argv[1:5])
    rng = random.Random(seed)
    M = build(j)
    R = M['R']
    PA, PB = random_level(n, rng)
    act = act_tables(PA, PB)
    H = instantiate(M, PA, PB)
    law = M['lawful'].index(True)
    label = [-1] * n
    sizes = []
    order = list(range(n))
    rng.shuffle(order)
    for q0 in order:
        B = ball(act, q0, r)
        if any(label[x] >= 0 for x in B):
            continue
        for x in B:
            label[x] = len(sizes)
        sizes.append(len(B))
    F = [0] * len(sizes)
    FL = [0] * len(sizes)
    for (u, v, w) in H:
        c = label[u // R]
        if c >= 0 and label[v // R] == c and label[w // R] == c:
            F[c] += 1
            if u % R == law and v % R == law and w % R == law:
                FL[c] += 1
    tree = 1 + sum(4 * 3 ** (i - 1) for i in range(1, r + 1))
    tb = [c for c in range(len(sizes)) if sizes[c] == tree]
    print('j %d n %d radius %d R %d  balls %d (tree-shaped %d, size %d)'
          % (j, n, r, R, len(sizes), len(tb), tree))
    if tb:
        vals = sorted(set(F[c] for c in tb))
        print('F(ball x types) over tree-shaped balls:', vals,
              ' ratio F/|A| =', [round(v / (tree * R), 4) for v in vals])
        print('lawful layer F_LLL/|X| over tree-shaped balls:',
              sorted(set(round(FL[c] / tree, 4) for c in tb)))
    Atot = sum(sizes) * R
    print('whole packing: |A|/n = %.3f, F(A)/|A| = %.4f'
          % (Atot / n, sum(F) / Atot))


if __name__ == '__main__':
    main()
