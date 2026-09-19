#!/usr/bin/env python3
"""Numerically recover small dyadic Iwahori branching tables.

Run on MSI, not locally.  The class-algebra computation is exact up to the
final simultaneous diagonalization; all reported multiplicities are rounded
only after a residual check.
"""

import argparse
from collections import deque

import numpy as np


def mul(x, y, n):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % n, (a * f + b * h) % n,
            (c * e + d * g) % n, (c * f + d * h) % n)


def inv(x, n):
    a, b, c, d = x
    return (d % n, (-b) % n, (-c) % n, a % n)


def sl2(n):
    return [(a, b, c, d) for a in range(n) for b in range(n)
            for c in range(n) for d in range(n)
            if (a * d - b * c) % n == 1]


def subgroup(gens, n):
    one = (1, 0, 0, 1)
    gens = gens + [inv(g, n) for g in gens]
    seen = {one}
    todo = deque([one])
    while todo:
        x = todo.popleft()
        for g in gens:
            y = mul(x, g, n)
            if y not in seen:
                seen.add(y)
                todo.append(y)
    return sorted(seen)


class CharacterTable:
    def __init__(self, elements, gens, n):
        self.elements = elements
        self.index = {g: i for i, g in enumerate(elements)}
        self.n = n
        assert all(g in self.index for g in gens)
        conjugators = gens + [inv(g, n) for g in gens]
        unseen = set(elements)
        classes = []
        while unseen:
            seed = next(iter(unseen))
            orbit = {seed}
            todo = [seed]
            while todo:
                x = todo.pop()
                for g in conjugators:
                    y = mul(mul(g, x, n), inv(g, n), n)
                    if y not in orbit:
                        orbit.add(y)
                        todo.append(y)
            unseen.difference_update(orbit)
            classes.append(sorted(orbit))
        classes.sort(key=lambda c: (0 if (1, 0, 0, 1) in c else 1, len(c), c[0]))
        self.classes = classes
        self.class_of = {g: i for i, c in enumerate(classes) for g in c}
        k = len(classes)
        sizes = np.array([len(c) for c in classes], dtype=float)
        left = np.zeros((k, k, k), dtype=np.complex128)
        for i, ci in enumerate(classes):
            counts = np.zeros((k, k), dtype=np.int64)
            for x in ci:
                for j, cj in enumerate(classes):
                    for y in cj:
                        counts[j, self.class_of[mul(x, y, n)]] += 1
            for j in range(k):
                for q in range(k):
                    if counts[j, q]:
                        coeff = counts[j, q] / len(classes[q])
                        left[i, q, j] = coeff * np.sqrt(sizes[q] / sizes[j])
        rng = np.random.default_rng(20260823 + n + len(elements))
        combo = np.zeros((k, k), dtype=np.complex128)
        inverse_class = [self.class_of[inv(c[0], n)] for c in classes]
        for i in range(k):
            combo += rng.normal() * (left[i] + left[inverse_class[i]]) / 2
            combo += rng.normal() * (left[i] - left[inverse_class[i]]) / (2j)
        combo = (combo + combo.conj().T) / 2
        _, vecs = np.linalg.eigh(combo)
        lambdas = np.empty((k, k), dtype=np.complex128)
        for r in range(k):
            v = vecs[:, r]
            lambdas[r] = np.array([np.vdot(v, left[i] @ v) for i in range(k)])
        dims = np.sqrt(len(elements) /
                       np.sum(np.abs(lambdas) ** 2 / sizes[None, :], axis=1))
        self.dims = np.rint(dims).astype(int)
        if np.max(np.abs(dims - self.dims)) > 2e-5:
            raise RuntimeError(f"dimension recovery failed: {dims}")
        self.chars = self.dims[:, None] * lambdas / sizes[None, :]
        gram = np.empty((k, k), dtype=np.complex128)
        for r in range(k):
            for s in range(k):
                gram[r, s] = np.sum(sizes * self.chars[r] * self.chars[s].conj()) / len(elements)
        if np.max(np.abs(gram - np.eye(k))) > 2e-5:
            raise RuntimeError(f"character orthogonality failed: {np.max(np.abs(gram-np.eye(k)))}")

    def value(self, irrep, g):
        return self.chars[irrep, self.class_of[g]]


ORBITS = {
    "O0": [(0, 0, 0)],
    "OF": [(1, 1, 1)],
    "OA": [(1, 0, 0), (1, 0, 1), (1, 1, 0)],
    "OB": [(0, 1, 0), (0, 1, 1), (0, 0, 1)],
}


def kernel_element(level, abc):
    n = 2 ** level
    t = 2 ** (level - 1)
    a, b, c = abc
    return ((1 + t * a) % n, (t * b) % n, (t * c) % n, (1 + t * a) % n)


def sector(table, irrep, level):
    dim = table.dims[irrep]
    observed = []
    for abc in [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0)]:
        observed.append(table.value(irrep, kernel_element(level, abc)) / dim)
    for name, orbit in ORBITS.items():
        expected = []
        for abc in [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0)]:
            expected.append(sum((-1) ** sum(x * y for x, y in zip(mu, abc))
                                for mu in orbit) / len(orbit))
        if max(abs(x - y) for x, y in zip(observed, expected)) < 2e-5:
            return name
    return "?"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("a", type=int, choices=[2, 3])
    args = parser.parse_args()
    a = args.a
    n0, n1 = 2 ** a, 2 ** (a + 1)
    u0, l0, minus0 = (1, 1, 0, 1), (1, 0, 1, 1), ((-1) % n0, 0, 0, (-1) % n0)
    u1, l1, minus1 = (1, 1, 0, 1), (1, 0, 1, 1), ((-1) % n1, 0, 0, (-1) % n1)
    g0 = sl2(n0)
    g1 = sl2(n1)
    hgens = [(1, 2, 0, 1), l1, minus1]
    h = subgroup(hgens, n1)
    assert len(h) == len(g1) // 3, (len(h), len(g1))
    print(f"orders G{a}={len(g0)} G{a+1}={len(g1)} H={len(h)}", flush=True)
    t0 = CharacterTable(g0, [u0, l0, minus0], n0)
    t1 = CharacterTable(g1, [u1, l1, minus1], n1)
    th = CharacterTable(h, hgens, n1)
    print(f"class counts {len(t0.classes)} {len(t1.classes)} {len(th.classes)}", flush=True)

    def to_source(x):
        aa, bb, cc, dd = x
        assert bb % 2 == 0
        return (aa % n0, (bb // 2) % n0, (2 * cc) % n0, dd % n0)

    source_restriction = np.zeros((len(t0.dims), len(th.dims)), dtype=int)
    target_restriction = np.zeros((len(t1.dims), len(th.dims)), dtype=int)
    for i in range(len(t0.dims)):
        for k in range(len(th.dims)):
            z = sum(t0.value(i, to_source(x)) * th.value(k, x).conjugate()
                    for x in h) / len(h)
            source_restriction[i, k] = int(round(z.real))
            if abs(z - source_restriction[i, k]) > 3e-5:
                raise RuntimeError(("source restriction", i, k, z))
    for j in range(len(t1.dims)):
        for k in range(len(th.dims)):
            z = sum(t1.value(j, x) * th.value(k, x).conjugate()
                    for x in h) / len(h)
            target_restriction[j, k] = int(round(z.real))
            if abs(z - target_restriction[j, k]) > 3e-5:
                raise RuntimeError(("target restriction", j, k, z))

    rows = []
    for i in range(len(t0.dims)):
        si = sector(t0, i, a)
        if si != "OF":
            continue
        for j in range(len(t1.dims)):
            sj = sector(t1, j, a + 1)
            if sj != "OB":
                continue
            common = sum(min(source_restriction[i, k], target_restriction[j, k]) * th.dims[k]
                         for k in range(len(th.dims)))
            if common:
                rows.append((i, int(t0.dims[i]), j, int(t1.dims[j]), int(common)))
    print("OF->OB rows (source id,dim,target id,dim,common physical dim):")
    for row in rows:
        print(*row)


if __name__ == "__main__":
    main()
