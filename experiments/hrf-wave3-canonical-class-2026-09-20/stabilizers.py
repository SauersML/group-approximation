"""Exact finite vertex-kernel certificate for the canonical K7 class.

Standard-library integer arithmetic only. Matrix equality is modulo seven.
"""
import json
from pathlib import Path

P = 7
I = tuple(int(i == j) for i in range(4) for j in range(4))


def mul(a, b):
    return tuple(sum(a[4*i+k] * b[4*k+j] for k in range(4)) % P
                 for i in range(4) for j in range(4))


def power(a, n):
    out = I
    for _ in range(n):
        out = mul(out, a)
    return out


def comm(a, b):
    return mul(mul(power(a, 6), power(b, 6)), mul(a, b))


def matrix(entries):
    out = list(I)
    for i, j, value in entries:
        out[4*i+j] = (out[4*i+j] + value) % P
    return tuple(out)


def closure(gens):
    seen = {I}
    queue = [I]
    for g in queue:
        for x in gens:
            h = mul(g, x)
            if h not in seen:
                seen.add(h)
                queue.append(h)
    return seen


a = matrix([(0, 3, 1), (1, 2, 1)])
b = matrix([(1, 0, 1), (2, 3, -1)])
c = matrix([(3, 1, 1)])
results = []
for name, x, y, expected in [('X0', a, b, 343),
                              ('X1', c, b, 2401),
                              ('X2', c, a, 2401)]:
    # Enumerating with a character label also checks that x,y -> 1 in C7
    # is well-defined on the entire finite vertex group.
    labels = {I: 0}
    queue = [I]
    for g in queue:
        for z in (x, y):
            h = mul(g, z)
            value = (labels[g] + 1) % P
            if h in labels:
                assert labels[h] == value
            else:
                labels[h] = value
                queue.append(h)
    assert len(labels) == expected
    kernel = {g for g, value in labels.items() if value == 0}
    u, v = mul(x, power(y, 6)), comm(x, y)
    assert closure([u, v]) == kernel
    assert all(power(g, 7) == I for g in kernel)
    # Normal closure of [u,v] under the kernel generators is the derived
    # subgroup of this two-generator kernel.
    derived = closure([comm(u, v)])
    while True:
        extra = {mul(mul(power(z, 6), d), z)
                 for z in (u, v) for d in derived}
        enlarged = closure(list(derived | extra))
        if enlarged == derived:
            break
        derived = enlarged
    assert len(kernel) // len(derived) == 49
    results.append({'vertex': name, 'order': len(labels),
                    'kernel_order': len(kernel),
                    'kernel_generators': [list(u), list(v)],
                    'derived_order': len(derived),
                    'abelianization_order': 49,
                    'all_kernel_elements_seventh_power_identity': True})

result = {'prime': P, 'vertices': results,
          'conclusion': 'Each K7 vertex stabilizer has abelianization C7^2.'}
Path(__file__).with_name('stabilizers.json').write_text(
    json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
