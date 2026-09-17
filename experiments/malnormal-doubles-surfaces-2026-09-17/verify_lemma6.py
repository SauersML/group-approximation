"""Independent verification of the Lemma 6 certificates printed by search_pairs.py.

This file does not import the search code.  It uses its own folding, fibre products and
rotation systems.  For each certificate (C, n, E, labels, boundary words with Gamma_C vertices):
  1. builds Gamma_C by union-find folding, checks rank(C) = 2, infinite index, malnormal;
  2. builds Y from (n, E, labels) and checks it is folded;
  3. finds a rotation system on Y whose boundary cycles read exactly the listed words;
  4. rank(Y) >= 2; for each boundary w_j: w_j cyclically reduced and not a proper power, closed at c_j, component of (v_j, c_j) in
     Y x Gamma_C of rank 1; components pairwise distinct;
  5. brute force: every reduced word of length <= |w_j| + 8 closed at v_j in Y and at c_j in
     Gamma_C is a power of w_j;
  6. reports the genus r of the closed surface subgroup of D(F_2, C) (Lemma 6).
Usage: python3 verify_lemma6.py out_pairs_r2.txt out_pairs_r3.txt out_pairs_r4_residual.txt
  The Gamma_C vertices c_j are re-found by this script (the search numbers vertices differently).
"""
import ast
import itertools
import sys

LET = "aAbB"


def w_of(s):
    return [LET.index(ch) for ch in s]


def s_of(w):
    return "".join(LET[x] for x in w)


def inv_letter(x):
    return x ^ 1


def inv_word(w):
    return [inv_letter(x) for x in reversed(w)]


def stallings(gens):
    """Union-find folding of the bouquet of loops of the generators."""
    edges, nv = [], 1
    for g in gens:
        g = w_of(g)
        v = 0
        for i, x in enumerate(g):
            u = 0 if i == len(g) - 1 else nv
            if u == nv:
                nv += 1
            edges.append((v, x, u))
            v = u
    parent = list(range(nv))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    changed = True
    while changed:
        changed = False
        out = {}
        for (v, x, u) in edges:
            for key, tgt in (((find(v), x), find(u)), ((find(u), inv_letter(x)), find(v))):
                if key in out and find(out[key]) != tgt:
                    parent[find(out[key])] = tgt
                    changed = True
                else:
                    out.setdefault(key, tgt)
    roots = sorted({find(v) for v in range(nv)})
    idx = {r: i for i, r in enumerate(roots)}
    adj = [dict() for _ in roots]
    for (v, x, u) in edges:
        a, b = idx[find(v)], idx[find(u)]
        adj[a][x] = b
        adj[b][inv_letter(x)] = a
    return adj


def read(adj, v, w):
    for x in w:
        v = adj[v].get(x)
        if v is None:
            return None
    return v


def component(G, g0, H, h0):
    seen, st, half = {(g0, h0)}, [(g0, h0)], 0
    while st:
        g, h = st.pop()
        for x, g2 in G[g].items():
            h2 = H[h].get(x)
            if h2 is None:
                continue
            half += 1
            if (g2, h2) not in seen:
                seen.add((g2, h2))
                st.append((g2, h2))
    return frozenset(seen), half // 2 - len(seen) + 1


def malnormal(adj):
    n = len(adj)
    for p in range(n):
        for q in range(n):
            if p != q:
                comp, rk = component(adj, p, adj, q)
                if rk != 0:
                    return False
    return True


def build_Y(n, E, labels):
    adj = [dict() for _ in range(n)]
    for (i, j), s in zip(E, labels):
        w = w_of(s)
        cur = i
        for k, x in enumerate(w):
            nx = j if k == len(w) - 1 else len(adj)
            if nx == len(adj):
                adj.append(dict())
            if x in adj[cur] or inv_letter(x) in adj[nx]:
                return None
            adj[cur][x] = nx
            adj[nx][inv_letter(x)] = cur
            cur = nx
    return adj


def boundary_cycles(n, E, labels, rot):
    nxt = {}
    for cyc in rot:
        for i, h in enumerate(cyc):
            nxt[h] = cyc[(i + 1) % len(cyc)]
    seen, out = set(), []
    for e in range(len(E)):
        for s in (0, 1):
            h = (e, s)
            if h in seen:
                continue
            cyc = []
            while h not in seen:
                seen.add(h)
                cyc.append(h)
                h = nxt[(h[0], 1 - h[1])]
            out.append(cyc)
    return out


def all_rotations(n, E):
    at = [[] for _ in range(n)]
    for e, (i, j) in enumerate(E):
        at[i].append((e, 0))
        at[j].append((e, 1))
    per_vertex = [[tuple([h[0]] + list(p)) for p in itertools.permutations(h[1:])] for h in at]
    return itertools.product(*per_vertex)


def not_proper_power(w):
    n = len(w)
    return all(not (n % d == 0 and w == w[:d] * (n // d)) for d in range(1, n))


def verify(gens, cert):
    n, E, labels, info = cert[:4]
    C = stallings(gens)
    rankC = sum(len(d) for d in C) // 2 - len(C) + 1
    inf_index = any(len(d) < 4 for d in C)
    mal = malnormal(C)
    Y = build_Y(n, E, labels)
    if Y is None:
        return False, "Y not folded"
    words = [(w_of(s), c) for s, c in info]
    r = len(E) - n + 1
    for rot in all_rotations(n, E):
        cycles = boundary_cycles(n, E, labels, rot)
        if len(cycles) != len(words):
            continue
        faces = []
        for cyc in cycles:
            w = []
            for (e, s) in cyc:
                w += w_of(labels[e]) if s == 0 else inv_word(w_of(labels[e]))
            faces.append((w, E[cyc[0][0]][cyc[0][1]]))
        # match listed words to faces, up to cyclic rotation
        remaining = list(range(len(faces)))
        match = []
        for (w, c) in words:
            # the listed word may start at any letter of the face; every letter position is a
            # vertex of the subdivided graph Y, so rotate and move the start vertex along
            hit = None
            for k in remaining:
                fw, fv = faces[k]
                if len(fw) != len(w):
                    continue
                o = next((o for o in range(len(fw)) if fw[o:] + fw[:o] == w), None)
                if o is not None:
                    hit = (k, read(Y, fv, fw[:o]))
                    break
            if hit is None:
                break
            remaining.remove(hit[0])
            match.append((w, hit[1], c))
        if len(match) != len(words):
            continue
        # The Gamma_C vertex numbers printed by the search come from a different folding, so they
        # are not reused: for each boundary w_j we try every vertex c of Gamma_C and look for a
        # choice with w_j closed at c, rank-1 components, pairwise distinct (backtracking).
        options = []
        for (w, v, _c) in match:
            opts = []
            cyc_red = all(w[i] != inv_letter(w[(i + 1) % len(w)]) for i in range(len(w)))
            if r >= 2 and cyc_red and not_proper_power(w) and read(Y, v, w) == v:
                for c in range(len(C)):
                    if read(C, c, w) == c:
                        comp, rk = component(Y, v, C, c)
                        if rk == 1:
                            opts.append((c, comp))
            options.append(opts)
        choice = []

        def pick(j, used):
            if j == len(match):
                return True
            for c, comp in options[j]:
                if comp not in used:
                    choice.append(c)
                    if pick(j + 1, used | {comp}):
                        return True
                    choice.pop()
            return False

        ok = pick(0, frozenset())
        detail = []
        if ok:
            for (w, v, _c), c in zip(match, choice):
                # brute force: reduced loops at v in Y of length <= |w|+8 closing at c are powers of w
                L = len(w) + 8
                bad = 0
                stack = [(v, c, [])]
                powers = {tuple(w * k) for k in range(1, L // len(w) + 1)} | {tuple(inv_word(w) * k) for k in range(1, L // len(w) + 1)}
                while stack:
                    y, z, p = stack.pop()
                    if p and y == v and z == c and tuple(p) not in powers:
                        bad += 1
                    if len(p) == L:
                        continue
                    for x, y2 in Y[y].items():
                        if p and x == inv_letter(p[-1]):
                            continue
                        z2 = C[z].get(x)
                        if z2 is not None:
                            stack.append((y2, z2, p + [x]))
                ok = ok and bad == 0
                detail.append("%s@%d rank1=True brute-bad=%d" % (s_of(w), c, bad))
        if ok:
            return rankC == 2 and inf_index and mal, "rank(C)=%d inf-index=%s malnormal=%s | Y rank %d, %d boundaries | %s => closed genus-%d surface in D(F2,C)" % (
                rankC, inf_index, mal, r, len(words), "; ".join(detail), r)
    return False, "no rotation system reproduces the boundary words with the hypotheses"


def parse(path):
    out = []
    cur_gens = None
    for line in open(path):
        if line.startswith("CERT"):
            head, rest = line.split(" V ", 1)
            gens = ast.literal_eval(head.split(" ", 2)[2])
            cert = ast.literal_eval(rest.split("Y genus,boundaries ", 1)[1].split(" ", 2)[2])
            out.append((gens, cert))
        elif line.startswith("C ["):
            cur_gens = ast.literal_eval(line[2:line.index("]") + 1])
        elif line.startswith("certificates: [("):
            lst = ast.literal_eval(line[len("certificates: "):])
            out.append((tuple(cur_gens), lst[0][1]))
    return out


if __name__ == "__main__":
    total = passed = 0
    for path in sys.argv[1:]:
        for gens, cert in parse(path):
            total += 1
            ok, msg = verify(gens, cert)
            passed += ok
            print(path, gens, "CERTIFIED" if ok else "FAIL", msg)
            sys.stdout.flush()
    print("verified", passed, "/", total)
