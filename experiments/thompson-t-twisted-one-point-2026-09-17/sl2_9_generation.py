"""Order of the subgroup <a, b> of SL(2,9) for each exact twisted pair of sl2_twisted.py with r_2 = I.

Pairs: a over conjugacy-class representatives with a^4 = -I, b over all order-3 elements with (ba)^5 = I.
Prints, for each (r_1, r_2) outcome, the multiset of |<a, b>|.
"""
import json

import sl2_twisted as S


def closure(mm, I, gens):
    seen = {I}
    frontier = [I]
    while frontier:
        nxt = []
        for g in frontier:
            for s in gens:
                h = mm(g, s)
                if h not in seen:
                    seen.add(h)
                    nxt.append(h)
        frontier = nxt
    return len(seen)


def main():
    F = S.Fq(3, 2)
    mm, inv, I, mI = S.make(F)
    G = S.sl2(F)
    A8 = [g for g in G if S.power(mm, g, 4, I) == mI]
    B3 = [g for g in G if g != I and S.power(mm, g, 3, I) == I]
    reps, seen = [], set()
    for a in A8:
        if a in seen:
            continue
        reps.append(a)
        for g in G:
            seen.add(mm(mm(g, a), inv(g)))
    out = {}
    for a in reps:
        J = mm(a, a)
        for b in B3:
            if S.power(mm, mm(b, a), 5, I) != I:
                continue
            X = mm(mm(b, a), b)
            Y1 = mm(mm(J, X), inv(J))
            r1 = mm(mm(X, Y1), mm(inv(X), inv(Y1)))
            W = mm(mm(J, mm(b, b)), J)
            Y2 = mm(mm(W, X), inv(W))
            r2 = mm(mm(X, Y2), mm(inv(X), inv(Y2)))
            key = f"r1={'I' if r1 == I else 'other'},r2={'I' if r2 == I else 'other'}"
            o = closure(mm, I, [a, b])
            out.setdefault(key, {})
            out[key][str(o)] = out[key].get(str(o), 0) + 1
    print(json.dumps({"q": 9, "order_SL2": len(G), "subgroup_orders_by_outcome": out}))
    json.dump(out, open("out_sl2_9_generation.json", "w"), indent=1)


if __name__ == "__main__":
    main()
