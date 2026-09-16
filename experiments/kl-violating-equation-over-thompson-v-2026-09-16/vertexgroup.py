"""Normalization-invariant coefficient subgroup (star-graph vertex group) filter for the
KL census over Thompson's group V.

For w = g_0 t^(e_0) ... g_(n-1) t^(e_(n-1)) (cyclic, corner i between t^(e_(i-1)) and t^(e_i)),
the automorphism t -> s u of V * <t> (u in V) fixes V and rewrites the label at corner i as

    h_i(u) = [u if e_(i-1) = +1] * g_i * [u^-1 if e_i = -1].

Choose u so that one same-sign corner k gets label 1:
    (+,+) corner: u = g_k^-1 ;   (-,-) corner: u = g_k.
Then L = <h_i(u)> is the smallest coefficient subgroup over all normalizations
(every other normalization v gives <L, v'> for some v').  If L is finite the word injects V
(localization + hyperlinear theorem).  Finiteness is certified by an exact closure
that terminates below the bound.

Usage: vertexgroup.py IN OUT [BOUND]
Input lines: "<id> <word> ..." ; output "<id> <word> VFINITE order=<N> u=<g> labels=<...>" or
"<id> <word> VNONE".
"""
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "kl-thompson-v-census"))
import vgroup as V
from certify import parse, E

ID = V.identity()


def labels_after_normalization(signs, coeffs):
    n = len(signs)
    k = None
    for i in range(n):
        if signs[i - 1] == signs[i]:
            k = i
            break
    if k is None:
        return None, None
    g = E[coeffs[k]]
    u = g.inverse() if signs[k] > 0 else g
    ui = u.inverse()
    out = []
    for i in range(n):
        h = E[coeffs[i]]
        if signs[i - 1] > 0:
            h = u * h
        if signs[i] < 0:
            h = h * ui
        out.append(h)
    assert out[k] == ID
    return (coeffs[k], signs[k]), out


def closure_order(gens, bound):
    gens = [x for x in gens if x != ID]
    seen = {ID.key()}
    frontier = [ID]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = x * g
                ky = y.key()
                if ky not in seen:
                    seen.add(ky)
                    if len(seen) > bound:
                        return None
                    nxt.append(y)
        frontier = nxt
    return len(seen)


def main():
    inp, outp = sys.argv[1], sys.argv[2]
    bound = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
    stats = {}
    with open(inp) as f, open(outp, "w") as out:
        for line in f:
            parts = line.split()
            wid, word = parts[0], parts[1]
            signs, coeffs = parse(word)
            which, labs = labels_after_normalization(signs, coeffs)
            order = closure_order(labs, bound)
            if order is not None:
                tag = "VFINITE"
                extra = " order=%d" % order
            else:
                tag = "VNONE"
                extra = ""
            stats[tag] = stats.get(tag, 0) + 1
            out.write("%s %s %s%s\n" % (wid, word, tag, extra))
    print(stats, flush=True)


if __name__ == "__main__":
    main()
