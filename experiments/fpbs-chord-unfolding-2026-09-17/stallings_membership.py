"""Stallings folding: which chord label sets H satisfy <K, H> = F(a, b),
K = <a, b a b^-2>?  A pure-chord graphing with labels in H can generate R_L
over R_K only if <K, H> = L (every pair it produces is in R_{<K,H>}).
Exact double-coset b-lengths are in coset_b_length.py."""
INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def folded(words):
    E, nv = [], [1]
    for w in words:
        cur = 0
        for i, x in enumerate(w):
            if i == len(w) - 1:
                nxt = 0
            else:
                nxt = nv[0]
                nv[0] += 1
            E.append((cur, x, nxt) if x in 'ab' else (nxt, INV[x], cur))
            cur = nxt
    par = list(range(nv[0]))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    changed = True
    while changed:
        changed = False
        out, inn = {}, {}
        for (u, x, v) in E:
            u, v = f(u), f(v)
            for key, val, d in (((u, x), v, out), ((v, x), u, inn)):
                if key in d and f(d[key]) != f(val):
                    par[f(val)] = f(d[key])
                    changed = True
                else:
                    d[key] = val
    tab = {}
    for (u, x, v) in E:
        tab[(f(u), x)] = f(v)
        tab[(f(v), INV[x])] = f(u)
    return f(0), tab


def member(words, g):
    base, tab = folded(words)
    cur = base
    for x in g:
        if (cur, x) not in tab:
            return False
        cur = tab[(cur, x)]
    return cur == base


K = ['a', 'baBB']
if __name__ == '__main__':
    for H in (['bab'], ['bAb'], ['bab', 'bAb'], ['bab', 'bAb', 'baab', 'bAAb'],
              ['babab'], ['bb'], ['bb', 'bab'], ['b'], ['bbb'], ['bbbb'],
              ['bbb', 'bb'], ['bbab'], ['babb'], ['bAbb']):
        print('H =', H, ' <K,H> = L:', member(K + H, 'b'))
