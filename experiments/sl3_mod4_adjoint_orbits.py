#!/usr/bin/env python3
"""Enumerate SL3(Z/4)-adjoint orbits on sl3(Z/4), using 6 elementary generators."""

from collections import Counter, deque
import json


MOD = 4


def matmul(a, b):
    return tuple(
        sum(a[3 * i + k] * b[3 * k + j] for k in range(3)) % MOD
        for i in range(3)
        for j in range(3)
    )


def elementary(i, j, t):
    a = [0] * 9
    for k in range(3):
        a[3 * k + k] = 1
    a[3 * i + j] = t % MOD
    return tuple(a)


def decode(n):
    c = []
    for _ in range(8):
        c.append(n % MOD)
        n //= MOD
    # coordinates: six off-diagonals, then d11,d22; d33=-d11-d22
    a = [0] * 9
    for x, (i, j) in zip(c[:6], ((0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1))):
        a[3 * i + j] = x
    a[0], a[4], a[8] = c[6], c[7], (-c[6] - c[7]) % MOD
    return tuple(a)


def encode(a):
    c = [a[1], a[2], a[3], a[5], a[6], a[7], a[0], a[4]]
    n = 0
    for x in reversed(c):
        n = MOD * n + x
    return n


GENS = []
for i in range(3):
    for j in range(3):
        if i != j:
            g = elementary(i, j, 1)
            gi = elementary(i, j, -1)
            GENS.append((g, gi))


def conjugates(code):
    x = decode(code)
    for g, gi in GENS:
        yield encode(matmul(matmul(g, x), gi))


def main():
    total = MOD**8
    seen = bytearray(total)
    orbit_sizes = []
    representatives = []
    for seed in range(total):
        if seen[seed]:
            continue
        seen[seed] = 1
        q = deque([seed])
        size = 0
        while q:
            x = q.popleft()
            size += 1
            for y in conjugates(x):
                if not seen[y]:
                    seen[y] = 1
                    q.append(y)
        orbit_sizes.append(size)
        representatives.append(seed)
    out = {
        "module_size": total,
        "orbit_count": len(orbit_sizes),
        "orbit_size_distribution": dict(sorted(Counter(orbit_sizes).items())),
        "representatives": representatives,
    }
    print(json.dumps(out, sort_keys=True))


if __name__ == "__main__":
    main()
