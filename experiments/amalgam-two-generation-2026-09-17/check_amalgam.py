#!/usr/bin/env python3
"""Checks for the single-amalgam two-generation upgrade.

Q = (P * <s>) *_{C1 = C2} F(a,b),
  C1 = < s^(m+1), p_k s^k (k=1..m) >,   C2 = < a, y_k = b^-k a b^(k+1) (k=1..m) >,
  s^(m+1) <-> a,  p_k s^k <-> y_k.

1. Stallings graph of C2: folded, rank m+1, not a covering (infinite index, b not in C2).
2. Weak malnormality witness: g in F(a,b) with C2 cap g C2 g^-1 = 1 (product graph component is a tree).
3. Certificate: G0 = <s,b | b^-k s^(m+1) b^(k+1) = s^k, k=1..m> is trivial (this is Q/<<P>>).
Words are strings over 'aAbBsS' (capital = inverse).
"""
import itertools, sys

INV = {c: c.swapcase() for c in "aAbBsS"}

def inv(w):
    return "".join(INV[c] for c in reversed(w))

def y(k):
    return "B" * k + "a" + "b" * (k + 1)

# ---------- Stallings graphs ----------
def stallings(gens):
    # edges: dict (v, letter) -> v, letters lowercase with inverse edges stored as uppercase
    parent = {}
    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v
    edges = set()
    nv = [1]
    parent[0] = 0
    for w in gens:
        cur = 0
        for i, c in enumerate(w):
            if i == len(w) - 1:
                nxt = 0
            else:
                nxt = nv[0]; parent[nxt] = nxt; nv[0] += 1
            edges.add((cur, c, nxt)); edges.add((nxt, INV[c], cur))
            cur = nxt
    changed = True
    while changed:
        changed = False
        out = {}
        for (u, c, v) in list(edges):
            u2, v2 = find(u), find(v)
            key = (u2, c)
            if key in out and out[key] != v2:
                a, b = find(out[key]), v2
                if a != b:
                    parent[a] = b
                    changed = True
            else:
                out[key] = v2
        edges = {(find(u), c, find(v)) for (u, c, v) in edges}
    verts = {find(v) for v in parent}
    return find(0), verts, edges

def rank(verts, edges):
    return len(edges) // 2 - len(verts) + 1

def product_component_rank(G1, G2):
    b1, V1, E1 = G1; b2, V2, E2 = G2
    out1, out2 = {}, {}
    for (u, c, v) in E1: out1[(u, c)] = v
    for (u, c, v) in E2: out2[(u, c)] = v
    start = (b1, b2); seen = {start}; stack = [start]; ecount = 0
    while stack:
        (p, q) = stack.pop()
        for c in "aAbB":
            if (p, c) in out1 and (q, c) in out2:
                ecount += 1
                nxt = (out1[(p, c)], out2[(q, c)])
                if nxt not in seen:
                    seen.add(nxt); stack.append(nxt)
    return ecount // 2 - len(seen) + 1

def reduce_word(w):
    st = []
    for c in w:
        if st and st[-1] == INV[c]: st.pop()
        else: st.append(c)
    return "".join(st)

def main(m):
    gens = ["a"] + [y(k) for k in range(1, m + 1)]
    G = stallings(gens)
    base, V, E = G
    out = {}
    for (u, c, v) in E:
        assert (u, c) not in out or out[(u, c)] == v
        out[(u, c)] = v
    r = rank(V, E)
    full = all((v, c) in out for v in V for c in "aAbB")
    b_in = (base, "b") in out and out[(base, "b")] == base
    print(f"m={m}: C2 Stallings graph |V|={len(V)} rank={r} (expected {m+1}) covering={full} b-loop-at-base={b_in}")
    assert r == m + 1 and not full and not b_in
    # weak malnormality witness search
    found = None
    for L in range(1, 5):
        for g in itertools.product("aAbB", repeat=L):
            g = reduce_word("".join(g))
            if len(g) != L: continue
            conj = [reduce_word(g + w + inv(g)) for w in gens]
            H = stallings(conj)
            if product_component_rank(G, H) == 0:
                found = g; break
        if found: break
    print(f"  witness g with C2 cap g C2 g^-1 = 1: {found}")
    assert found
    return found

# ---------- Normal-closure certificate for Q/<<P>> = 1 ----------
def certificate(m):
    """G0 = <s,b | r_k = b^-k s^N b^(k+1) s^-k, k=1..m>, N=m+1, m>=3.
    Free-group identities (checked by free reduction):
      X_k := b^k r_k b^-k = s^N b^(k+1) s^-k b^-k
      Y_k := b^-k X_k^-1 X_(k+1) b^k = s^k b s^-(k+1) b^-1         (k=1,2)
      s    = b^-1 Y_1^-1 (s Y_1^-1 s^-1) Y_2 b
      b    = s^-N ... : r_1 with s := 1 reads b, i.e. b = r_1 modulo <<s>>.
    Hence s and b lie in the normal closure of the relators."""
    N = m + 1
    r = {k: "B" * k + "s" * N + "b" * (k + 1) + "S" * k for k in range(1, m + 1)}
    X = {k: reduce_word("b" * k + r[k] + "B" * k) for k in range(1, 4)}
    for k in range(1, 4):
        assert X[k] == reduce_word("s" * N + "b" * (k + 1) + "S" * k + "B" * k)
    Y = {k: reduce_word("B" * k + inv(X[k]) + X[k + 1] + "b" * k) for k in (1, 2)}
    for k in (1, 2):
        assert Y[k] == reduce_word("s" * k + "b" + "S" * (k + 1) + "B"), (k, Y[k])
    W = reduce_word("B" + inv(Y[1]) + "s" + inv(Y[1]) + "S" + Y[2] + "b")
    assert W == "s", W
    # r_1 with every s deleted freely reduces to b
    assert reduce_word(r[1].replace("s", "").replace("S", "")) == "b"
    return True

if __name__ == "__main__":
    for m in range(1, 7):
        main(m)
    for m in range(3, 9):
        assert certificate(m)
        print(f"m={m}: normal-closure certificate: s and b are trivial in Q/<<P>>")
    print("ALL CHECKS PASSED")
