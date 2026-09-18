"""Single-generator detour packing for a stage pair of Gamma_mal.

H = <a, w> in F(a,b) with w = b_n written in the basis {a, b_m}; t ranges over short
words with <H, t> = F(a,b) and t not in H b^{+-1} H.  A detour for the t-edge at
the root 1 is a simple coset cycle 1 -t-> t -h_1-> . -t^{e_1}-> ... with s further
t-edges, returning to the coset H.  Its support is the set of points at which the
further t-edges start.  The finite packing lemma ((2.1) of
research/artifacts/fpbs/small-cancellation-family.md, read for arbitrary detour
words) certifies relC(F; H) <= q + (1-q) prod_i (1 - q^{s_i}) for any family with
pairwise disjoint supports not containing the root.

Output per t: counts of simple detours with s = 1, 2 (syllables of length <= L),
greedy disjoint family sizes, and the best certificate value over a q grid.
"""
import itertools
import math
import sys

from fg import Subgroup, red, inv, reduced_words


def w_stage(d):
    """b_{m-d} as a word in a, b = b_m (b_{j-1} = b_j a b_j^-2)."""
    w = "b"
    for _ in range(d):
        w = red(w + "a" + inv(w) + inv(w))
    return w


def detours(H, Hel, t, s, L):
    """Simple detours with s further t-edges; the last syllable is searched to length L2."""
    T = {1: t, -1: inv(t)}
    out = []
    for eps in itertools.product((1, -1), repeat=s):
        for hs in itertools.product(Hel, repeat=s - 1):
            P = [t]
            ok = True
            pts = []
            prev = 1
            for h, e in zip(hs, eps[:-1]):
                if h == "" and e == -prev:
                    ok = False
                    break
                Q = red(P[-1] + h)
                pts.append(Q if e == 1 else red(Q + T[-1]))
                P.append(red(Q + T[e]))
                prev = e
            if not ok:
                continue
            c = P[-1]
            e = eps[-1]
            if not H.in_double_coset(T[-e], c):
                continue
            for h in Hel:
                if h == "" and e == -prev:
                    continue
                Q = red(c + h)
                end = red(Q + T[e])
                if H.contains(end):
                    ptsx = pts + [Q if e == 1 else end]
                    Pall = P + [end]
                    # simple: cosets P_0 H .. P_s H distinct (P_s H = H)
                    cos = Pall
                    simple = all(not H.contains(red(inv(cos[i]) + cos[j]))
                                 for i in range(len(cos)) for j in range(i + 1, len(cos)))
                    if simple and "" not in ptsx and len(set(ptsx)) == len(ptsx):
                        out.append((eps, hs + (h,), frozenset(ptsx)))
                    break
    return out


def greedy(fam):
    used, chosen = set(), []
    for eps, hs, pts in sorted(fam, key=lambda d: (len(d[2]), sum(map(len, d[1])))):
        if used.isdisjoint(pts):
            used |= pts
            chosen.append(len(pts))
    return chosen


def certificate(sizes):
    best = (1.0, 1.0)
    for i in range(1, 1000):
        q = i / 1000
        val = q + (1 - q) * math.prod(1 - q ** s for s in sizes)
        best = min(best, (val, q))
    return best


def main(d, tlen, L):
    w = w_stage(d)
    H = Subgroup(["a", w])
    Hel = H.elements(L)
    print(f"# d={d} w={w} |H-elements <= {L}|={len(Hel)}")
    for t in reduced_words(tlen):
        if not H.generates_F2_with(t):
            continue
        dc = H.in_double_coset("b", t) or H.in_double_coset("B", t)
        f1 = detours(H, Hel, t, 1, L)
        f2 = detours(H, Hel, t, 2, L)
        g = greedy(f1 + f2)
        val, q = certificate(g)
        print(f"t={t:10s} |t|={len(t)} bdc={int(dc)} s1={len(f1)} s2={len(f2)} "
              f"greedy={len(g)} cert={val:.4f} q={q:.3f}")
        sys.stdout.flush()


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
