#!/usr/bin/env python3
"""Search for a single homomorphism phi: G -> Q, Q in H torsion-free, that is nontrivial on the
top and bottom edge elements of a span-2 Magnus rewrite.  Such a phi certifies EVERY segment step
of G at once (see research/mapping-torus-targets-fail-rank-2-window-one-relators.md, item 5).

G = <a, t | r'(a_0, a_1, a_2)>, a_i = t^-i a t^i, with r' the Magnus rewrite computed exactly as
experiments/amalgam-segment-steps-2026-09-17/frontier_check.py does.  phi is given by
A = phi(a), T = phi(t), words over a, A, b, B in the target (groups.py).

Usage: target_search.py TARGET LA LT WORD ...      TARGET in BG2, BG3, BS23, ...
Prints, per word, the first (A, T) found (shortest A first), with the images of the edge
elements, or 'none'.
"""
import itertools, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "amalgam-segment-steps-2026-09-17"))
sys.path.insert(0, HERE)
import frontier_check as fc  # noqa: E402
from groups import BG, BS, is_trivial, inv_word, reduce_word  # noqa: E402

LET = "aAbB"


def reduced_words(n):
    """Freely reduced words of length exactly n."""
    if n == 0:
        yield ""
        return
    for w in reduced_words(n - 1):
        for c in LET:
            if w and w[-1] == c.swapcase():
                continue
            yield w + c


def words_upto(n):
    for k in range(1, n + 1):
        yield from reduced_words(k)


def edges_bottom(r):
    """(x, y) with r = a_0^-1 x a_0 y cyclically, or None (mirror of fc.edges)."""
    idx = [i for i, ((_, p), _) in enumerate(r) if p == 0]
    if len(idx) != 2:
        return None
    n = len(r)
    i = next(j for j in idx if r[j][1] == -1)
    w = r[i:] + r[:i]
    j = next(k for k in range(1, n) if w[k][0][1] == 0)
    return w[1:j], w[j + 1:]


def word_of(r, imgs):
    out = []
    for (_, p), e in r:
        out.append(imgs[p] if e == 1 else inv_word(imgs[p]))
    return "".join(out)


def target(name):
    if name.startswith("BG"):
        return BG(int(name[2:]))
    if name.startswith("BS"):
        return BS(int(name[2]), int(name[3]))
    raise SystemExit("unknown target " + name)


def bexp(w):
    return w.count("b") - w.count("B")


def search(Q, r, LA, LT):
    top, bot = fc.edges(r), edges_bottom(r)
    probes = [top[0], bot[0]] if top and bot else None
    As = [w for w in words_upto(LA) if bexp(w) == 0]
    Ts = list(words_upto(LT))
    for A in As:
        for T in Ts:
            imgs = [A, inv_word(T) + A + T, inv_word(T) * 2 + A + T * 2]
            if not is_trivial(Q, word_of(r, imgs)):
                continue
            if probes is None or all(not is_trivial(Q, word_of(e, imgs)) for e in probes):
                return A, T, probes
    return None


def main():
    Q = target(sys.argv[1])
    LA, LT = int(sys.argv[2]), int(sys.argv[3])
    for s in sys.argv[4:]:
        r, ev = fc.magnus(s)
        if r is None:
            print(s, "no span-2 zero-end rewrite")
            continue
        res = search(Q, r, LA, LT)
        if res is None:
            print("%-16s r'=%-20s %s none (A<=%d, T<=%d)" % (s, fc.sc.show(r), Q.name, LA, LT))
        else:
            A, T, probes = res
            print("%-16s r'=%-20s %s A=%s T=%s edges=%s" % (
                s, fc.sc.show(r), Q.name, A, T, [fc.sc.show(e) for e in probes] if probes else "?"))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
