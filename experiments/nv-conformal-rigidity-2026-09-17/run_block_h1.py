"""Run block_h1 on the PG(2,2) Robertson-Steger examples and on two one-vertex controls.

control: the product of two full 4-shifts as a vertex-labelled 2-graph
  (tiles (i,j), colour-1 edges (i,j)->(i',j), colour-2 edges (i,j)->(i,j'), all squares);
  its groupoid is G_4 x G_4 and H^1 contains H^1(G_4) (infinite rank): H^1 must grow in k.
Usage: python3 run_block_h1.py KMAX [NEXAMPLES]
"""
import json, sys, time, os
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, "..", "nv-brick-coding-2026-09-17"))
import rs2graph, tp
from block_h1 import h1_level, cells, h1_fast

SLOW_MAX = int(os.environ.get("SLOW_MAX", "1"))  # cross-check h1_level vs h1_fast up to this k


def run(name, G, kmax):
    for k in range(kmax + 1):
        t = time.time()
        fast = h1_fast(*cells(*G, k))
        line = f"{name} k={k} {fast} {time.time() - t:.1f}s"
        if k <= SLOW_MAX:
            slow = h1_level(*G, k)
            assert slow["h1_upper"] == fast["h1_upper"], (slow, fast)
            line += " (cross-checked)"
        print(line, flush=True)


def product_control(m=4):
    tiles = [(i, j) for i in range(m) for j in range(m)]
    ix = {t: n for n, t in enumerate(tiles)}
    E1 = [(ix[(i, j)], ix[(i2, j)]) for (i, j) in tiles for i2 in range(m)]
    E2 = [(ix[(i, j)], ix[(i, j2)]) for (i, j) in tiles for j2 in range(m)]
    e1 = {e: n for n, e in enumerate(E1)}
    e2 = {e: n for n, e in enumerate(E2)}
    sq = []
    for (i, j) in tiles:
        for i2 in range(m):
            for j2 in range(m):
                a, b, c, d = ix[(i, j)], ix[(i2, j)], ix[(i, j2)], ix[(i2, j2)]
                sq.append((e1[(a, b)], e2[(b, d)], e2[(a, c)], e1[(c, d)]))
    return tiles, E1, E2, sq


def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    nex = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    ex = json.load(open(os.path.join(here, "..", "nv-brick-coding-2026-09-17", "tp_q2.json")))["examples"]
    if nex == 0:
        run("product", product_control(), kmax)
        return
    for n, (lam, T, _) in enumerate(ex[:nex]):
        T = [tuple(t) for t in T]
        tp.check(T, lam)
        run(f"T{n}", rs2graph.build(T), kmax)


if __name__ == "__main__":
    main()
