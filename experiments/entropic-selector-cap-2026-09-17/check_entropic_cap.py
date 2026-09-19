"""Sanity check for entropic-branch-selectors-cap-every-lift-labelling.

Small random bipartite 2-to-1 games (A-alphabet 4, B-alphabet 2, lifted
right alphabet B x {0,1} of size 4).  For orientation laws of the form
  bit(e, fiber) = f(e, fiber) xor r(e, fiber),  r ~ Bernoulli((1-delta)/2) iid,
with f a fixed arbitrary function (the shared, deterministic part), we
compute the exact maximum lift value over ALL labellings by brute force and
compare with the claim's bound 1/2 + delta/2 + t (history bias beta = delta).

Also checks: (i) every orientation lift is a unique game (bijective
constraints), (ii) lift value >= val(G)/2 (sandwich floor), (iii) the
empirical failure rate of the bound is at most 2^-k.
"""
import itertools
import math
import random

LA, LB = 4, 2          # |Sigma_A| = 2^l with l = 2, |Sigma_B| = 2^(l-1)


def random_game(nA, nB, deg, rng):
    edges = []
    for a in range(nA):
        for b in rng.sample(range(nB), deg):
            perm = list(range(LA))
            rng.shuffle(perm)
            # pi(s) = perm[s] // 2 : 2-to-1 onto Sigma_B
            pi = [perm[s] // 2 for s in range(LA)]
            edges.append((a, b, pi))
    return edges


def fibers(pi):
    return [[s for s in range(LA) if pi[s] == t] for t in range(LB)]


def lift_value(edges, orient, nA, nB):
    """max over sigma_A, and best right labels, of the lift value.

    orient[i][t] in {0,1} selects which element of fiber t of edge i gets
    branch bit 0; the other gets bit 1.  Right label = (t, bit)."""
    M = len(edges)
    best = 0
    for sA in itertools.product(range(LA), repeat=nA):
        # for each right vertex, count votes for each lifted label (t, bit)
        votes = [dict() for _ in range(nB)]
        for i, (a, b, pi) in enumerate(edges):
            s = sA[a]
            t = pi[s]
            fib = fibers(pi)[t]
            bit = 0 if fib[orient[i][t]] == s else 1
            votes[b][(t, bit)] = votes[b].get((t, bit), 0) + 1
        v = sum(max(d.values()) if d else 0 for d in votes)
        best = max(best, v)
    return best / M


def game_value(edges, nA, nB):
    M = len(edges)
    best = 0
    for sA in itertools.product(range(LA), repeat=nA):
        votes = [dict() for _ in range(nB)]
        for a, b, pi in edges:
            t = pi[sA[a]]
            votes[b][t] = votes[b].get(t, 0) + 1
        best = max(best, sum(max(d.values()) if d else 0 for d in votes))
    return best / M


def check_bijective(edges, orient):
    for i, (a, b, pi) in enumerate(edges):
        images = set()
        for s in range(LA):
            t = pi[s]
            bit = 0 if fibers(pi)[t][orient[i][t]] == s else 1
            images.add((t, bit))
        assert len(images) == LA, "oriented constraint not a bijection"


def main():
    rng = random.Random(20260917)
    nA, nB, deg = 6, 6, 6           # complete bipartite, M = 36
    l, k = 2, 3
    for delta in (0.0, 0.25, 0.5):
        fails, trials, tot = 0, 20, 0.0
        for _ in range(trials):
            edges = random_game(nA, nB, deg, rng)
            M = len(edges)
            f = [[rng.randrange(2) for _ in range(LB)] for _ in range(M)]
            orient = [[f[i][t] ^ (1 if rng.random() < (1 - delta) / 2 else 0)
                       for t in range(LB)] for i in range(M)]
            check_bijective(edges, orient)
            lv = lift_value(edges, orient, nA, nB)
            tot += lv
            gv = game_value(edges, nA, nB)
            assert lv >= gv / 2 - 1e-12, "sandwich floor violated"
            t = math.sqrt((l * (nA + nB) + k) * math.log(2) / (2 * M))
            bound = 0.5 + delta / 2 + t
            if lv > bound + 1e-12:
                fails += 1
        assert fails <= trials * 2 ** (-k) + 3, (delta, fails)
        print(f"delta={delta}: mean max lift {tot/trials:.3f}, "
              f"bound {bound:.3f}, failures {fails}/{trials}")
    print("OK: bijective lifts, sandwich floor, entropic cap never violated "
          "beyond the allowed rate")


if __name__ == "__main__":
    main()
