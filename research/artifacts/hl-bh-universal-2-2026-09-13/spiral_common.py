import os
RMAX = int(os.environ.get('RMAX', '150'))

def spiral(rmax):
    pts = [(0, 0)]
    for r in range(1, rmax + 1):
        x, y = r, -r + 1
        while y <= r:
            pts.append((x, y)); y += 1
        y = r; x = r - 1
        while x >= -r:
            pts.append((x, y)); x -= 1
        x = -r; y = r - 1
        while y >= -r:
            pts.append((x, y)); y -= 1
        y = -r; x = -r + 1
        while x <= r:
            pts.append((x, y)); x += 1
    return pts

pts = spiral(RMAX)
nu = {p: i for i, p in enumerate(pts)}

def rad(p):
    return max(abs(p[0]), abs(p[1]))

def ring(r):
    return [p for p in pts if rad(p) == r]

def sig(p):
    i = nu[p] + 1
    return pts[i] if i < len(pts) else None

def sig_inv(p):
    i = nu[p] - 1
    return pts[i] if i >= 0 else None

def L(g):
    return lambda p: (p[0] + g[0], p[1] + g[1])

def compose(*fs):
    def h(p):
        for f in reversed(fs):
            if p is None or p not in nu:
                return None
            p = f(p)
        return p if (p is None or p in nu) else None
    return h

def sigpow(k):
    fs = [sig] * k if k >= 0 else [sig_inv] * (-k)
    return compose(*fs) if fs else (lambda p: p)

E = {'e1': (1, 0), 'e2': (0, 1), '-e1': (-1, 0), '-e2': (0, -1)}
X = {k: compose(sig_inv, L(g), sig) for k, g in E.items()}
Y = {k: compose(sig, L(g), sig_inv) for k, g in E.items()}
