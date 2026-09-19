# Fast Stallings folding: edges are inserted into an always-folded graph; a clash queues a vertex merge.
class SG:
    def __init__(s):
        s.par = [0]; s.out = [dict()]
    def new(s):
        s.par.append(len(s.par)); s.out.append(dict()); return len(s.par) - 1
    def f(s, v):
        p = s.par; r = v
        while p[r] != r: r = p[r]
        while p[v] != r: p[v], v = r, p[v]
        return r
    def add_loop(s, u, base=0):
        # read as much of u as possible from both ends, then add the middle path
        v = s.f(base); i = 0
        while i < len(u) and u[i] in s.out[v]: v = s.f(s.out[v][u[i]]); i += 1
        if i == len(u):
            if v != s.f(base): s._merge(v, base)
            return
        w = s.f(base); j = len(u)
        while j > i and u[j - 1].swapcase() in s.out[w]: w = s.f(s.out[w][u[j - 1].swapcase()]); j -= 1
        if j == i: s._merge(v, w); return
        cur = v
        for k in range(i, j):
            t = w if k == j - 1 else s.new()
            s.edge(cur, u[k], t); cur = s.f(t)
    def edge(s, v, c, t):
        s.q = [(v, c, t)]
        while s.q:
            v, c, t = s.q.pop(); v = s.f(v); t = s.f(t)
            ok = True
            for (a, lab, b) in ((v, c, t), (t, c.swapcase(), v)):
                a = s.f(a); b = s.f(b)
                if lab in s.out[a]:
                    o = s.f(s.out[a][lab])
                    if o != b: s._merge(o, b); ok = False; break
            if ok:
                v = s.f(v); t = s.f(t)
                s.out[v][c] = t; s.out[t][c.swapcase()] = v
    def _merge(s, a, b):
        pend = [(a, b)]
        while pend:
            a, b = pend.pop(); a = s.f(a); b = s.f(b)
            if a == b: continue
            if len(s.out[a]) > len(s.out[b]): a, b = b, a
            s.par[a] = b
            da = s.out[a]; s.out[a] = {}
            for lab, t in da.items():
                t = s.f(t); db = s.out[b]
                if lab in db:
                    o = s.f(db[lab])
                    if o != t: pend.append((o, t))
                else:
                    db[lab] = t
        # clean inverse pointers lazily via f()
    def verts(s): return [v for v in range(len(s.par)) if s.f(v) == v]
    def stats(s):
        V = s.verts()
        E = 0
        for v in V:
            for lab, t in s.out[v].items():
                assert s.f(s.out[s.f(t)][lab.swapcase()]) == v, 'inconsistent'
            E += len(s.out[v])
        return len(V), E // 2, E // 2 - len(V) + 1
    def member(s, u, base=0):
        v = s.f(base)
        for c in u:
            if c not in s.out[v]: return False
            v = s.f(s.out[v][c])
        return v == s.f(base)
    def fold(s): pass
