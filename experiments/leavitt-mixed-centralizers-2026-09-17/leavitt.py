"""Leavitt algebra L_{F_2}(1,2) in normal form, with bounded-window centralizers.

Elements are sets of basis keys (w, v) meaning s_w t_v (coefficients in F_2, so an
element is the set of keys with coefficient 1).  s_w = s_{w1}...s_{wn},
t_v = (s_v)^*.  Normal form: drop keys with w and v both ending in '1', using
s_{w'1} t_{v'1} = s_{w'} t_{v'} + s_{w'0} t_{v'0}  (char 2).
"""


def add_key(acc, key):
    if key in acc:
        acc.remove(key)
    else:
        acc.add(key)


def normalize_key(w, v, acc):
    # reduce s_w t_v into acc (symmetric difference)
    while w and v and w[-1] == '1' and v[-1] == '1':
        add_key(acc, (w[:-1] + '0', v[:-1] + '0'))
        w, v = w[:-1], v[:-1]
    add_key(acc, (w, v))


def mul_keys(k1, k2, acc):
    w, v = k1
    x, y = k2
    if x.startswith(v):
        normalize_key(w + x[len(v):], y, acc)
    elif v.startswith(x):
        normalize_key(w, y + v[len(x):], acc)


def mul(A, B):
    acc = set()
    for k1 in A:
        for k2 in B:
            mul_keys(k1, k2, acc)
    return frozenset(acc)


def add(A, B):
    return frozenset(set(A) ^ set(B))


def elt(*keys):
    acc = set()
    for w, v in keys:
        normalize_key(w, v, acc)
    return frozenset(acc)


ONE = elt(('', ''))


def words(maxlen):
    out = ['']
    frontier = ['']
    for _ in range(maxlen):
        frontier = [f + c for f in frontier for c in '01']
        out += frontier
    return out


def window(R):
    ws = words(R)
    return [(w, v) for w in ws for v in ws
            if not (w and v and w[-1] == '1' and v[-1] == '1')]


def kernel_F2(images, n):
    """images[i] = set of output keys for unknown i. Return basis of kernel as
    lists of unknown indices."""
    index = {}
    pivots = {}  # pivot bit -> (row int, tag int)
    kern = []
    for i in range(n):
        row = 0
        for key in images[i]:
            j = index.setdefault(key, len(index))
            row ^= 1 << j
        tag = 1 << i
        while row:
            p = row.bit_length() - 1
            if p in pivots:
                r2, t2 = pivots[p]
                row ^= r2
                tag ^= t2
            else:
                pivots[p] = (row, tag)
                break
        if not row:
            kern.append(tag)
    return kern


def centralizer(a, R):
    W = window(R)
    images = []
    for key in W:
        x = frozenset([key])
        images.append(add(mul(a, x), mul(x, a)))
    kern = kernel_F2(images, len(W))
    out = []
    for tag in kern:
        out.append(frozenset(W[i] for i in range(len(W)) if tag >> i & 1))
    return out


def degrees(A):
    return sorted({len(w) - len(v) for w, v in A})
