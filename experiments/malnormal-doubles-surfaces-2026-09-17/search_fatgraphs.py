"""Multi-boundary fatgraph certificates for closed surface subgroups in D(F_2, C).

Certificate (Lemma 6 of research/malnormal-free-doubles-surface-certificates-proof.md):
a folded ribbon graph Y over F_2 of rank r >= 2 whose boundary components
w_1..w_k each read a closed path at some vertex c_j of Gamma_C, with the
component of (start_j, c_j) in Y x Gamma_C of rank 1.  Then the double of the
thickened surface S(Y) along all k boundary circles, a closed orientable
surface of Euler characteristic 2(1 - r), i.e. genus r, embeds in
D(F_2, C) = F_2 *_C F_2.

If C is malnormal, every edge word has length <= K(C) (bounded-segment lemma,
which covers the multi-boundary case), so for fixed rank the search below with
L = K(C) is COMPLETE: its negatives are exact.

Shapes: all connected multigraphs (loops allowed) with r - 1 + n edges on n
vertices, degrees in {3, 4}; all rotation systems; all labellings by reduced
words of length <= L readable in Gamma_C, with backtracking on faces.

Usage: python3 search_fatgraphs.py <rank> <C words...>          (single C)
       python3 search_fatgraphs.py batch <rank> <n> <lo> <hi>    (random batch, seed 20260917)
"""
import itertools
import random
import sys
from stallings import INV, Graph, word, show, fold_subgroup, read, product_component_rank, is_malnormal, offdiag_depth, infinite_index, rank


def inv(w):
    return [INV(x) for x in reversed(w)]


# ---------- shapes and rotation systems ----------

def shapes(r):
    out = []
    for n in range(1, 2 * r - 1):
        m = n + r - 1
        pairs = [(i, j) for i in range(n) for j in range(i, n)]
        for E in itertools.combinations_with_replacement(pairs, m):
            deg = [0] * n
            for i, j in E:
                deg[i] += 1
                deg[j] += 1
            if any(d < 3 or d > 4 for d in deg):
                continue
            # connected
            seen, st = {0}, [0]
            while st:
                u = st.pop()
                for i, j in E:
                    for a, b in ((i, j), (j, i)):
                        if a == u and b not in seen:
                            seen.add(b)
                            st.append(b)
            if len(seen) == n:
                out.append((n, E))
    return out


def rotations(n, E):
    """Half-edges: (e, 0) leaves E[e][0] along the edge, (e, 1) leaves E[e][1] backwards."""
    at = [[] for _ in range(n)]
    for e, (i, j) in enumerate(E):
        at[i].append((e, 0))
        at[j].append((e, 1))
    choices = []
    for v in range(n):
        h = at[v]
        choices.append([tuple([h[0]] + list(p)) for p in itertools.permutations(h[1:])])
    for rot in itertools.product(*choices):
        nxt = {}
        for cyc in rot:
            for i, h in enumerate(cyc):
                nxt[h] = cyc[(i + 1) % len(cyc)]
        yield rot, nxt


def faces(E, nxt):
    """Boundary cycles: from half-edge h traverse its edge, arrive at the end, take the
    rotation-successor of the reverse half-edge."""
    hs = [(e, s) for e in range(len(E)) for s in (0, 1)]
    seen, out = set(), []
    for h in hs:
        if h in seen:
            continue
        cyc, cur = [], h
        while cur not in seen:
            seen.add(cur)
            cyc.append(cur)
            e, s = cur
            cur = nxt[(e, 1 - s)]
        out.append(cyc)
    return out


# ---------- labels ----------

def readable_words(C, L):
    ws = set()
    for v in range(C.nv()):
        stack = [(v, [])]
        while stack:
            u, w = stack.pop()
            if w:
                ws.add(tuple(w))
            if len(w) == L:
                continue
            for x, u2 in C.adj[u].items():
                if w and x == INV(w[-1]):
                    continue
                stack.append((u2, w + [x]))
    return [list(w) for w in sorted(ws, key=lambda t: (len(t), t))]


def action(C, w):
    return tuple(read(C, c, w) for c in range(C.nv()))


def compose(p, q):
    return tuple(None if a is None else q[a] for a in p)


def half_label(lab, h):
    e, s = h
    return lab[e] if s == 0 else inv(lab[e])


def build_Y(n, E, lab):
    G = Graph()
    for _ in range(n):
        G.new()
    for e, (i, j) in enumerate(E):
        cur = i
        w = lab[e]
        for k, x in enumerate(w):
            nx = j if k == len(w) - 1 else G.new()
            if x in G.adj[cur] or INV(x) in G.adj[nx]:
                return None
            G.adj[cur][x] = nx
            G.adj[nx][INV(x)] = cur
            cur = nx
    return G


def component_id(Y, v, C, c):
    seen = {(v, c)}
    st = [(v, c)]
    while st:
        a, b = st.pop()
        for x, a2 in Y.adj[a].items():
            b2 = C.adj[b].get(x)
            if b2 is not None and (a2, b2) not in seen:
                seen.add((a2, b2))
                st.append((a2, b2))
    return min(seen)


def primitive_root_free(w):
    n = len(w)
    return all(not (n % d == 0 and w == w[:d] * (n // d)) for d in range(1, n))


def search(C, r, L, first_only=True):
    W = readable_words(C, L)
    acts = [action(C, w) for w in W]
    certs = []
    for n, E in shapes(r):
        m = len(E)
        for rot, nxt in rotations(n, E):
            F = faces(E, nxt)
            # order edges; a face is checkable once all its edges are labelled
            face_edges = [set(e for e, s in f) for f in F]
            ready = [[k for k in range(len(F)) if max(face_edges[k]) == e] for e in range(m)]
            lab, labact = [None] * m, [None] * m

            def closed_ok(k):
                act = None
                for h in F[k]:
                    e, s = h
                    a = labact[e] if s == 0 else inv_act[e]
                    act = a if act is None else compose(act, a)
                return any(act[c] == c for c in range(C.nv()))

            inv_act = [None] * m

            def rec(e):
                if e == m:
                    Y = build_Y(n, E, lab)
                    if Y is None:
                        return None
                    comps, info = set(), []
                    for f in F:
                        w = []
                        for h in f:
                            w += half_label(lab, h)
                        if not primitive_root_free(w):
                            return None
                        v0 = E[f[0][0]][0] if f[0][1] == 0 else E[f[0][0]][1]
                        good = None
                        for c in range(C.nv()):
                            if read(C, c, w) == c and product_component_rank(Y, v0, C, c)[0] == 1:
                                good = c
                                break
                        if good is None:
                            return None
                        cid = component_id(Y, v0, C, good)
                        if cid in comps:
                            return None
                        comps.add(cid)
                        info.append((show(w), good))
                    return (n, E, rot, [show(x) for x in lab], info)
                i, j = E[e]
                for idx, w in enumerate(W):
                    # folding at the endpoints: first letters of half-edges at a vertex distinct
                    lab[e] = w
                    ok = True
                    for v in {i, j}:
                        letters = []
                        for e2, (a, b) in enumerate(E[:e + 1]):
                            if a == v:
                                letters.append(lab[e2][0])
                            if b == v:
                                letters.append(INV(lab[e2][-1]))
                        if len(set(letters)) != len(letters):
                            ok = False
                            break
                    if not ok:
                        continue
                    labact[e] = acts[idx]
                    inv_act[e] = tuple(None for _ in range(C.nv()))
                    ia = [None] * C.nv()
                    for c, d in enumerate(acts[idx]):
                        if d is not None:
                            ia[d] = c
                    inv_act[e] = tuple(ia)
                    if all(closed_ok(k) for k in ready[e]):
                        res = rec(e + 1)
                        if res:
                            return res
                lab[e] = None
                return None

            res = rec(0)
            if res:
                certs.append(res)
                if first_only:
                    return certs
    return certs


def genus_of(res):
    n, E, rot, lab, info = res
    r = len(E) - n + 1
    k = len(info)
    g = (2 - (1 - r) - k) // 2  # chi(Y) = 1 - r = 2 - 2g - k
    return g, k


def random_word(L, rng):
    w = []
    while len(w) < L:
        x = rng.randrange(4)
        if w and w[-1] == INV(x):
            continue
        w.append(x)
    return w


def batch(r, N, lo, hi, seed=20260917):
    rng = random.Random(seed)
    tried = certified = 0
    seen = set()
    while tried < N:
        g1 = random_word(rng.randint(lo, hi), rng)
        g2 = random_word(rng.randint(lo, hi), rng)
        C = fold_subgroup([g1, g2])
        if rank(C) != 2 or not infinite_index(C) or not is_malnormal(C):
            continue
        key = (show(g1), show(g2))
        if key in seen:
            continue
        seen.add(key)
        tried += 1
        K = offdiag_depth(C)
        certs = search(C, r, K)
        if certs:
            certified += 1
            print("CERT", key, "V", C.nv(), "K", K, "genus,boundaries of Y", genus_of(certs[0]), certs[0])
        else:
            print("NONE", key, "V", C.nv(), "K", K)
        sys.stdout.flush()
    print("batch rank", r, "lengths", lo, hi, "seed", seed, ":", certified, "/", tried, "certified")


if __name__ == "__main__":
    if sys.argv[1] == "batch":
        batch(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
    else:
        r = int(sys.argv[1])
        C = fold_subgroup([word(g) for g in sys.argv[2:]])
        mal = is_malnormal(C)
        K = offdiag_depth(C) if mal else 3
        print("C", sys.argv[2:], "malnormal", mal, "K", K, "shapes", len(shapes(r)))
        certs = search(C, r, K)
        print("certificates:", [(genus_of(c), c) for c in certs] if certs else "NONE (exhaustive for rank %d)" % r)
