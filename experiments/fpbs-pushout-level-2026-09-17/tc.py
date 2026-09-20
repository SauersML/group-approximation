"""Minimal Todd-Coxeter (HLT with coincidence processing) for 2-generator presentations.

Generator letters: 0=a, 1=A, 2=b, 3=B (A = a^-1, B = b^-1).
enumerate_cosets(rels, subgens, maxcos) returns the index of <subgens> in
<a,b | rels>, or None if more than maxcos cosets were ever defined.
"""
INV = [1, 0, 3, 2]


def free_reduce(w):
    out = []
    for x in w:
        if out and out[-1] == INV[x]:
            out.pop()
        else:
            out.append(x)
    # cyclic reduction is not needed for correctness
    return out


def enumerate_cosets(rels, subgens, maxcos=200000):
    table = [[-1] * 4]
    p = [0]  # union-find parent (coincidence forwarding)

    def find(x):
        while p[x] != x:
            p[x] = p[p[x]]
            x = p[x]
        return x

    def define(c, x):
        if len(table) >= maxcos:
            raise OverflowError
        d = len(table)
        table.append([-1] * 4)
        p.append(d)
        table[c][x] = d
        table[d][INV[x]] = c
        return d

    def coincidence(c1, c2):
        queue = [(c1, c2)]
        while queue:
            u, v = queue.pop()
            u, v = find(u), find(v)
            if u == v:
                continue
            if u > v:
                u, v = v, u
            p[v] = u
            for x in range(4):
                w = table[v][x]
                if w == -1:
                    continue
                table[v][x] = -1
                wi = find(w)
                # remove back-edge from w
                if table[w][INV[x]] == v:
                    table[w][INV[x]] = -1
                uu = find(u)
                if table[uu][x] == -1:
                    table[uu][x] = wi
                    if table[wi][INV[x]] == -1:
                        table[wi][INV[x]] = uu
                    elif find(table[wi][INV[x]]) != uu:
                        queue.append((table[wi][INV[x]], uu))
                else:
                    queue.append((table[uu][x], wi))
                    if table[wi][INV[x]] == -1:
                        table[wi][INV[x]] = uu

    def scan_and_fill(c, w):
        # trace word w from c, defining cosets as needed, closing with deduction/coincidence
        n = len(w)
        while True:
            c = find(c)
            f, i = c, 0
            while i < n:
                nx = table[f][w[i]]
                if nx == -1:
                    break
                f = find(nx)
                i += 1
            if i == n:
                if f != c:
                    coincidence(f, c)
                return
            b_, j = c, n - 1
            while j >= i:
                nx = table[b_][INV[w[j]]]
                if nx == -1:
                    break
                b_ = find(nx)
                j -= 1
            if j < i:
                coincidence(f, b_)
                return
            if j == i:
                table[f][w[i]] = b_
                table[b_][INV[w[i]]] = f
                return
            define(f, w[i])

    try:
        for s in subgens:
            scan_and_fill(0, s)
        c = 0
        while c < len(table):
            if find(c) == c:
                for r in rels:
                    if find(c) != c:
                        break
                    scan_and_fill(c, r)
                if find(c) == c:
                    for x in range(4):
                        if table[c][x] == -1:
                            define(c, x)
            c += 1
    except OverflowError:
        return None
    live = [c for c in range(len(table)) if find(c) == c]
    return len(live)


if __name__ == "__main__":
    # sanity: <a,b | a^2, b^3, (ab)^5> = A5, index of trivial subgroup = 60
    A5 = [[0, 0], [2, 2, 2], [0, 2] * 5]
    print("A5 order", enumerate_cosets(A5, []))
    # S3 from the fold pair with Kbar = Z/2: <a,b | a^2, a (bab^-2)^-1>
    S3 = [[0, 0], free_reduce([0] + [2, 2, 1, 3])]
    print("S3 order", enumerate_cosets(S3, []))
    print("S4 order", enumerate_cosets([[0, 0], [2, 2, 2], [0, 2] * 4], []))
