# Model test for the riffle shuffle on the flat tuple model at arity 2m.
# A tuple is a tuple of degrees (the sign bookkeeping sees nothing else); a "face" lowers one slot by 1.
import itertools
from collections import defaultdict
def add(acc, t, c):
    acc[t] += c
def clean(v): return {k: c for k, c in v.items() if c}
def pre(t, k): return sum(t[:k])
def D(v):
    out = defaultdict(int)
    for t, c in v.items():
        for k in range(len(t)):
            if t[k] >= 1:
                s = list(t); s[k] -= 1
                add(out, tuple(s), c * (-1) ** pre(t, k))
    return clean(out)
def rot(t): return t[1:] + t[:1]
def T(v):
    out = defaultdict(int)
    for t, c in v.items():
        add(out, rot(t), c * (-1) ** (t[0] * (sum(t) - t[0])))
    return clean(out)
def eps(t, m):
    x, y = t[:m], t[m:]
    return sum(y[j] * sum(x[j + 1:]) for j in range(m))
def riffle_idx(t, m):
    x, y = t[:m], t[m:]
    return tuple(z for pair in zip(x, y) for z in pair)
def R(v, m):
    out = defaultdict(int)
    for t, c in v.items():
        add(out, riffle_idx(t, m), c * (-1) ** eps(t, m))
    return clean(out)
def B(v, m):
    out = defaultdict(int)
    for t, c in v.items():
        x, y = t[:m], t[m:]
        e = x[0] * (sum(x) - x[0]) + y[0] * (sum(y) - y[0])
        add(out, rot(x) + rot(y), c * (-1) ** e)
    return clean(out)
bad = 0; checked = 0
for m in range(1, 4):
    for t in itertools.product(range(4), repeat=2 * m):
        v = {t: 1}
        checked += 1
        if R(D(v), m) != D(R(v, m)): bad += 1; print("chain FAIL", m, t)
        if R(B(v, m), m) != T(T(R(v, m))): bad += 1; print("conj FAIL", m, t)
# negative control: drop the Koszul sign and the chain-map test must fail somewhere
def R0(v, m):
    return {riffle_idx(t, m): c for t, c in v.items()}
ctrl = sum(1 for m in (2, 3) for t in itertools.product(range(3), repeat=2 * m)
           if R0(D({t: 1}), m) != D(R0({t: 1}, m)))
print("checked", checked, "failures", bad, "unsigned-riffle chain failures (control, must be > 0):", ctrl)
