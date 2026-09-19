# exec'd by regular_search.py: enumerate homs A_K -> S_n with u1 up to conjugacy.
import numpy as _np


def _rel_ok(n, a, B, m):
    k = B.shape[0]
    x = _np.tile(_np.arange(n, dtype=_np.int16), (k, 1))
    y = x.copy()
    for s in range(m):
        if s % 2 == 0:
            x = x[:, a]
            y = _np.take_along_axis(y, B, 1)
        else:
            x = _np.take_along_axis(x, B, 1)
            y = y[:, a]
    return _np.all(x == y, axis=1)


def _cycle_type(p):
    n = len(p)
    seen = [False] * n
    ct = []
    for i in range(n):
        if not seen[i]:
            c = 0
            j = i
            while not seen[j]:
                seen[j] = True
                j = p[j]
                c += 1
            ct.append(c)
    return tuple(sorted(ct))


def enumerate_homs(n, perms):
    reps = {}
    for i, p in enumerate(perms):
        ct = _cycle_type(p)
        if ct not in reps:
            reps[ct] = i
    homs = []
    for ct, i1 in reps.items():
        a = perms[i1]
        for i2 in _np.nonzero(_rel_ok(n, a, perms, 2))[0]:
            b = perms[i2]
            okv1 = _rel_ok(n, a, perms, 4) & _rel_ok(n, b, perms, 4)
            v2base = _rel_ok(n, b, perms, 4) & _rel_ok(n, a, perms, 6)
            for j1 in _np.nonzero(okv1)[0]:
                c = perms[j1]
                okv2 = v2base & _rel_ok(n, c, perms, 2)
                for j2 in _np.nonzero(okv2)[0]:
                    homs.append((i1, int(i2), int(j1), int(j2)))
    return homs
