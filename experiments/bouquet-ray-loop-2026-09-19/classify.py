#!/usr/bin/env python3
"""Final classification of the 472 linear bouquet recursions by the loop group H = <S, T>.

Computed here (exact): whether S and T commute (R.trivial of the commutator) and the orders of
S and T (exact_order / infinite_order of same_point_screen.py).  Read from the other outputs:
sigma = tau = 1 (ray_loop_hyp.out), infinite-order certificates (h_inf.out, h_inf6.out) and
presentation certificates (h_present.out).  Classes:
  KILL-a   commuting, ord S < inf: H finite abelian, G contracting, not fp
  KILL-b   presentation certificate: H finite, G contracting, not fp
  SURVIVE  commuting, ord S = inf: H = Z x C_k, b_1(G) = 1, not FP_10, fp open
  OPEN-inf non-commuting, H infinite (certificate): G not contracting, fp open
  OPEN-und no certificate either way
Run: nice -n 10 timeout 1200 python3 classify.py > classify.out
"""
from bouquets import bouquets
from loopgraph import inv, reduce
from same_point_screen import infinite_order, exact_order

def read(path, key):
    out = {}
    for l in open(path):
        if " | " not in l: continue
        head, rest = l.rstrip("\n").split(" | ", 1)
        name = head.split(" ", 1)[1] if head.split(" ", 1)[0].isdigit() else head
        if key(rest): out[name] = rest
    return out

def order(R, w):
    if infinite_order(R, w): return "inf"
    return exact_order(R, w) or "?"

if __name__ == "__main__":
    facts = []
    for k, (name, R, I) in enumerate(bouquets()):
        S, T = I["S"], I["T"]
        try: comm = R.trivial(reduce(inv(S) + inv(T) + S + T))
        except RuntimeError: comm = "?"
        facts.append((k, name, comm, order(R, S), order(R, T)))
    triv = {l.split(" | z = ")[0]: l.rstrip().endswith("True") for l in open("ray_loop_hyp.out") if " | z = " in l}
    inf = read("h_inf.out", lambda r: r.startswith("infinite"))
    inf.update(read("h_inf6.out", lambda r: r.startswith("infinite")))
    fin = read("h_present.out", lambda r: r.startswith("FINITE"))
    tally = {}
    for k, name, comm, oS, oT in facts:
        if comm is True and oS != "inf" and oS != "?" and oT not in ("inf", "?"):
            c, info = "KILL-a", f"|H| divides {oS * oT}"
        elif name in fin:
            c, info = "KILL-b", fin[name]
        elif comm is True and oS == "inf":
            c, info = "SURVIVE", "H = Z x C_11" if triv[name] else "H = Z x C_k"
        elif name in inf:
            c, info = "OPEN-inf", inf[name]
        else:
            c, info = "OPEN-und", ""
        assert not (c.startswith("KILL") and (name in inf or "inf" in (oS, oT))), name
        key = (c, comm, triv[name])
        tally[key] = tally.get(key, 0) + 1
        print(k, name, "|", c, "| commute", comm, "| ord S", oS, "| ord T", oT,
              "| sigma=tau=1", triv[name], "|", info, flush=True)
    print("\nclass, commute, sigma = tau = 1 : count")
    for key, n in sorted(tally.items()): print(" ", key, ":", n)
    by = {}
    for (c, _, _), n in tally.items(): by[c] = by.get(c, 0) + n
    print("totals:", by)
