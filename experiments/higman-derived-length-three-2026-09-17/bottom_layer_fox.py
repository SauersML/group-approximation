"""Fox-derivative check for higman-b-side-bottom-layer-spans-are-infinite, Step 3.

P is free on c_j; words are lists of (j, +-1).  D_j(w) mod P' lives in Z[Z^(Z)], stored as
{exponent-vector (frozenset of (index, exp)): coeff}.  We check that w = [z, z^alpha] with
z = c_0^-m c_(-m)^m and z^alpha = c_(-m)^-m c_(-2m)^m has a nonzero Fox derivative mod P', so
w is not in P''; and that its gamma-conjugates give D(gamma^i w gamma^-i) = x_0^(mi) D(w).
"""
from collections import defaultdict

def mono_mul(a, b):
    d = defaultdict(int)
    for k, v in list(a) + list(b):
        d[k] += v
    return frozenset((k, v) for k, v in d.items() if v)

def fox(word, j):
    out = defaultdict(int)
    prefix = frozenset()
    for (i, e) in word:
        if i == j:
            if e == 1:
                out[prefix] += 1
            else:
                out[mono_mul(prefix, {(i, -1)})] -= 1
        prefix = mono_mul(prefix, {(i, e)})
    return {k: v for k, v in out.items() if v}, prefix

def inv(w):
    return [(i, -e) for (i, e) in reversed(w)]

def comm(u, v):
    return inv(u) + inv(v) + u + v

def pw(j, n):
    return [(j, 1 if n > 0 else -1)] * abs(n)

lines = []
for m in (1, 2, 3):
    z = pw(0, -m) + pw(-m, m)
    za = pw(-m, -m) + pw(-2 * m, m)
    w = comm(z, za)
    derivs = {j: fox(w, j)[0] for j in (0, -m, -2 * m)}
    assert fox(w, 0)[1] == frozenset()
    assert any(derivs.values())
    g = pw(0, m)
    for i in range(1, 4):
        wi = pw(0, m * i) + w + pw(0, -m * i)
        d0 = fox(wi, 0)[0]
        shifted = {mono_mul(k, {(0, m * i)}): v for k, v in derivs[0].items()}
        assert d0 == shifted, (m, i)
    lines.append(f"m={m}: D_0([z,z^alpha]) has {len(derivs[0])} terms (nonzero); D_0(gamma^i w gamma^-i) = x_0^(mi) D_0(w), i=1..3")
print("\n".join(lines))
