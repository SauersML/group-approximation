"""Read off the dumbbell shape of Delta_d: a-loop at the base, bridge beta_d, loop lambda_d."""
import sys
from fg import Subgroup
from packing import w_stage


def shape(d):
    H = Subgroup(["a", w_stage(d)])
    g = H.g
    o = g.at("o")
    nbrs = {}
    for (u, x), v in g.adj.items():
        nbrs.setdefault(u, []).append((x, v))
    deg3 = [v for v in nbrs if len(nbrs[v]) == 3]
    # walk from base along b
    bridge, cur, prev_letter = "", o, None
    x = "b"
    cur = g.adj[(o, "b")]
    bridge = "b"
    while len(nbrs[cur]) == 2:
        (x1, v1), (x2, v2) = nbrs[cur]
        inv = {"a": "A", "A": "a", "b": "B", "B": "b"}
        nxt = (x1, v1) if x1 != inv[bridge[-1]] else (x2, v2)
        bridge += nxt[0]
        cur = nxt[1]
    v = cur
    # loop at v: leave by a letter not on the bridge
    inv = {"a": "A", "A": "a", "b": "B", "B": "b"}
    start = [(x, u) for (x, u) in nbrs[v] if x != inv[bridge[-1]]][0]
    loop, cur = start[0], start[1]
    while cur != v:
        (x1, v1), (x2, v2) = nbrs[cur]
        nxt = (x1, v1) if x1 != inv[loop[-1]] else (x2, v2)
        loop += nxt[0]
        cur = nxt[1]
    return len(nbrs), deg3, bridge, loop


for d in range(1, int(sys.argv[1]) + 1):
    n, deg3, bridge, loop = shape(d)
    print(f"d={d} |V|={n} bridge={bridge} |loop|={len(loop)} loop={loop[:40]}{'...' if len(loop) > 40 else ''}")


def check_recurrence(dmax):
    """beta_{d+1} = beta_d lambda_d, lambda_{d+1} = beta_d^{-1} a beta_d lambda_d^{-1} (loop up to orientation)."""
    from fg import inv
    prev = shape(1)
    for d in range(1, dmax):
        cur = shape(d + 1)
        _, _, b0, l0 = prev
        _, _, b1, l1 = cur
        assert b1 == b0 + l0 or b1 == b0 + inv(l0), d
        lam0 = l0 if b1 == b0 + l0 else inv(l0)
        lam1 = inv(b0) + "a" + b0 + inv(lam0)
        assert l1 in (lam1, inv(lam1)), d
        cur = (cur[0], cur[1], b1, lam1)
        prev = cur
    print(f"dumbbell recurrence verified for d = 1..{dmax}")


if len(sys.argv) > 2:
    check_recurrence(int(sys.argv[2]))
