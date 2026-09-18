"""Print the generating vertex pairs of Delta_d with their missing half-edges."""
import sys
from fg import Subgroup, red, inv
from packing import w_stage
from vertex_pairs import spanning_words

for d in range(1, int(sys.argv[1]) + 1):
    H = Subgroup(["a", w_stage(d)])
    g = H.g
    o = g.at("o")
    gw = spanning_words(g, o)
    deg = {}
    for v in gw:
        deg[v] = len([x for x in "aAbB" if (v, x) in g.adj])
    print("d", d, "vertices", len(gw), "degree histogram",
          {k: list(deg.values()).count(k) for k in (1, 2, 3, 4)})
    for p in gw:
        for q in gw:
            if p != q and H.generates_F2_with(red(gw[p] + inv(gw[q]))):
                print("  pair", repr(gw[p]), repr(gw[q]),
                      "missing at p:", [x for x in "aAbB" if (p, x) not in g.adj],
                      "at q:", [x for x in "aAbB" if (q, x) not in g.adj])
