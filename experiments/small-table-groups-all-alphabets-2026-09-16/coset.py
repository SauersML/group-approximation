#!/usr/bin/env python3
"""Todd--Coxeter coset enumeration over the trivial subgroup (HLT strategy with the
standard coincidence routine, Holt--Eick--O'Brien, Handbook of Computational Group
Theory, Section 5.1).  If the enumeration closes, the group is finite of the order
returned.  The closed table is then re-checked independently: every generator acts
as a permutation, every relator fixes every coset, and the action is transitive.
"""


def col(x):
    return 2 * (abs(x) - 1) + (0 if x > 0 else 1)


def todd_coxeter(ngens, rels, max_cosets=20000):
    letters = [s * g for g in range(1, ngens + 1) for s in (1, -1)]
    table = [[None] * (2 * ngens)]
    parent = [0]

    def rep(k):
        root = k
        while parent[root] != root:
            root = parent[root]
        while parent[k] != root:
            parent[k], k = root, parent[k]
        return root

    def define(c, x):
        d = len(table)
        if d >= max_cosets:
            raise OverflowError
        table.append([None] * (2 * ngens))
        parent.append(d)
        table[c][col(x)] = d
        table[d][col(-x)] = c

    def merge(k, l, q):
        k, l = rep(k), rep(l)
        if k == l:
            return
        if k > l:
            k, l = l, k
        parent[l] = k
        q.append(l)

    def coincidence(a, b):
        q = []
        merge(a, b, q)
        i = 0
        while i < len(q):
            e = q[i]
            i += 1
            for x in letters:
                f = table[e][col(x)]
                if f is None:
                    continue
                table[f][col(-x)] = None
                e1, f1 = rep(e), rep(f)
                if table[e1][col(x)] is not None:
                    merge(f1, table[e1][col(x)], q)
                elif table[f1][col(-x)] is not None:
                    merge(e1, table[f1][col(-x)], q)
                else:
                    table[e1][col(x)] = f1
                    table[f1][col(-x)] = e1

    def scan_and_fill(c, w):
        f = b = c
        i, j = 0, len(w) - 1
        while True:
            while i <= j and table[f][col(w[i])] is not None:
                f = table[f][col(w[i])]
                i += 1
            if i > j:
                if f != b:
                    coincidence(f, b)
                return
            while j >= i and table[b][col(-w[j])] is not None:
                b = table[b][col(-w[j])]
                j -= 1
            if j < i:
                coincidence(f, b)
                return
            if i == j:
                table[f][col(w[i])] = b
                table[b][col(-w[i])] = f
                return
            define(f, w[i])

    c = 0
    while c < len(table):
        if parent[c] == c:
            for r in rels:
                if parent[c] != c:
                    break
                scan_and_fill(c, r)
            if parent[c] == c:
                for x in letters:
                    if table[c][col(x)] is None:
                        define(c, x)
        c += 1
    live = [k for k in range(len(table)) if parent[k] == k]
    idx = {k: n for n, k in enumerate(live)}
    perms = [[idx[rep(table[k][col(g)])] for k in live] for g in range(1, ngens + 1)]
    return len(live), perms


def verify_action(n, perms, rels):
    """Independent check of a closed table: permutations, relators trivial,
    transitive.  Returns True iff all hold."""
    for p in perms:
        if sorted(p) != list(range(n)):
            return False
    invs = []
    for p in perms:
        q = [0] * n
        for i, j in enumerate(p):
            q[j] = i
        invs.append(q)
    for r in rels:
        for k in range(n):
            y = k
            for x in r:
                y = perms[x - 1][y] if x > 0 else invs[-x - 1][y]
            if y != k:
                return False
    seen, stack = {0}, [0]
    while stack:
        k = stack.pop()
        for p in perms + invs:
            if p[k] not in seen:
                seen.add(p[k])
                stack.append(p[k])
    return len(seen) == n


if __name__ == "__main__":
    tests = [
        ("S3", 2, [(1, 1), (2, 2, 2), (1, 2, 1, 2)], 6),
        ("Q8", 2, [(1, 1, 1, 1), (1, 1, -2, -2), (1, 2, 1, -2)], 8),
        ("A5", 2, [(1, 1), (2, 2, 2), (1, 2) * 5], 60),
        ("Z3", 1, [(1, 1, 1)], 3),
        ("trivial", 2, [(1, 2, -1, -2, -2), (2, 1, -2, -1, -1)], 1),
    ]
    for name, ng, rels, expect in tests:
        n, perms = todd_coxeter(ng, rels)
        print(name, n, expect, "OK" if n == expect and verify_action(n, perms, rels) else "BAD")
