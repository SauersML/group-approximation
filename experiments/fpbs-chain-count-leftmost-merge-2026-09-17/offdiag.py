# Off-diagonal fibre product of the Stallings core of K = <a, b a b^-2> with itself.
# A common subtree of two distinct hull translates immerses into it, because
# a common vertex has different core types in the two hulls.
E = [(0, 'a', 0), (0, 'b', 1), (1, 'a', 2), (1, 'b', 2)]
V = [0, 1, 2]
P = [(u, v) for u in V for v in V if u != v]
PE = [((u, v), s, (u2, v2)) for (u, s, u2) in E for (v, t, v2) in E
      if s == t and (u, v) in P and (u2, v2) in P]
adj = {p: set() for p in P}
for (x, s, y) in PE:
    adj[x].add(y)
    adj[y].add(x)
seen = set()
for p in P:
    if p in seen:
        continue
    comp, st = [], [p]
    seen.add(p)
    while st:
        q = st.pop()
        comp.append(q)
        for r in adj[q]:
            if r not in seen:
                seen.add(r)
                st.append(r)
    ne = sum(1 for (x, s, y) in PE if x in comp)
    print("component", sorted(comp), "vertices", len(comp), "edges", ne,
          "tree" if ne == len(comp) - 1 else "NOT TREE")
