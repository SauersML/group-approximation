"""Independent certificates for GAP lines printed by malpair.py / randchains.py.

For each gap (A, B, PA, PB, witness):
- deep <= |witness|: the fold closure of the witness seeds contains ker m
  (exact closure, foldlib);
- law >= h_p := dim_{F_p} coker( H_1(Gamma_A(Q)) -> H_1(m(Gamma_A(Q))) ), p = 2,3,5,7.
  Proof: lawful seeds have lawful fold consequences, so a lawful family whose
  closure contains ker m has closure exactly ker m, and the quotient is the
  folded image m(Gamma_A(Q)).  Each merge adds one edge before folding, and
  folding is onto on H_1, so each lawful seed raises the image by <= 1.
Prints: certified deep upper bound, max_p h_p, and whether m is onto Gamma_B(Q).
Usage: python3 verify_gaps.py file
"""
import ast
import re
import sys
from chains import pair_graphs
from foldlib import closure, contains_kernel


def oriented_edges(G):
    return [(v, l, u) for v in range(G.V) for (l, e), u in G.nb[v].items() if e == 1]


def cycles(G, E):
    """Fundamental cycles as dicts edge_index -> +-1."""
    adj = [[] for _ in range(G.V)]
    for i, (v, l, u) in enumerate(E):
        adj[v].append((u, i, 1))
        adj[u].append((v, i, -1))
    par, pe = [None] * G.V, [None] * G.V
    tree = set()
    for r in range(G.V):
        if par[r] is not None:
            continue
        par[r] = r
        st = [r]
        while st:
            v = st.pop()
            for (u, i, s) in adj[v]:
                if par[u] is None:
                    par[u], pe[u] = v, (i, s)
                    tree.add(i)
                    st.append(u)

    def path(v):  # chain from root to v
        c = {}
        while par[v] != v:
            i, s = pe[v]
            c[i] = c.get(i, 0) + s
            v = par[v]
        return c
    out = []
    for i, (v, l, u) in enumerate(E):
        if i in tree:
            continue
        c = path(v)
        for k, x in path(u).items():
            c[k] = c.get(k, 0) - x
        c[i] = c.get(i, 0) + 1
        out.append({k: x for k, x in c.items() if x})
    return out


def rank_mod(rows, p):
    rows = [dict((k, x % p) for k, x in r.items() if x % p) for r in rows]
    piv = {}
    r = 0
    for row in rows:
        row = dict(row)
        while row:
            k = max(row)
            if k in piv:
                prow = piv[k]
                f = row[k] * pow(prow[k], p - 2, p) % p
                for kk, x in prow.items():
                    y = (row.get(kk, 0) - f * x) % p
                    if y:
                        row[kk] = y
                    else:
                        row.pop(kk, None)
            else:
                piv[k] = row
                r += 1
                break
    return r


def certify(A, B, PA, PB, wit):
    GB, GA, m = pair_graphs(PA, PB, A, B)
    ok = contains_kernel(GA, closure(GA, [tuple(s) for s in wit]), m)
    EA = oriented_edges(GA)
    EB = oriented_edges(GB)
    idx = {(v, l): i for i, (v, l, u) in enumerate(EB)}
    used = sorted({idx[(m[v], l)] for (v, l, u) in EA})
    onto = len(used) == len(EB)
    # image subgraph: edges `used`, vertices = m-image
    verts = sorted(set(m))
    vid = {v: i for i, v in enumerate(verts)}

    class Sub:
        pass
    S = Sub()
    S.V = len(verts)
    SE = [(vid[EB[i][0]], EB[i][1], vid[EB[i][2]]) for i in used]
    sidx = {i: k for k, i in enumerate(used)}
    cycI = cycles(S, SE)
    cycA = cycles(GA, EA)
    img = []
    for c in cycA:
        x = {}
        for i, s in c.items():
            v, l, u = EA[i]
            k = sidx[idx[(m[v], l)]]
            x[k] = x.get(k, 0) + s
        img.append(x)
    h = max(len(cycI) - rank_mod(img, p) for p in (2, 3, 5, 7))
    return ok, len(wit), h, onto


def main():
    for line in open(sys.argv[1]):
        if not line.startswith('GAP'):
            continue
        A = ast.literal_eval(re.search(r" A (\[.*?\]) B", line).group(1))
        B = ast.literal_eval(re.search(r" B (\[.*?\]) PA", line).group(1))
        PA = ast.literal_eval(re.search(r"PA (\[.*?\])", line).group(1))
        PB = ast.literal_eval(re.search(r"PB (\[.*?\])", line).group(1))
        W = ast.literal_eval(re.search(r"witness (\[.*\])", line).group(1))
        ok, d, h, onto = certify(A, B, PA, PB, W)
        law = re.search(r"law (\S+)", line).group(1)
        print('closure_ok', ok, 'deep<=', d, 'law_exact', law, 'law>=h', h,
              'certified_gap', ok and h > d, 'm_onto', onto)


if __name__ == '__main__':
    main()
