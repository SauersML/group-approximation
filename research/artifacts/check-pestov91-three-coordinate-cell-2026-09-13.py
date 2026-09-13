"""Finite checks of the bilateral compression cell, not of compression itself.

Run on MSI. Finite cyclic models test the displayed local identities over
several characteristics; they deliberately fail the infinite one-sided
compression inclusion. No matrix approximation claim follows from this test.
"""
import json
import time

started = time.monotonic()
checks = 0


def identity(size):
    return {(i, i): 1 for i in range(size)}


def mul(a, b, prime):
    rows = {}
    for (i, j), value in b.items():
        rows.setdefault(i, []).append((j, value))
    out = {}
    for (i, k), value in a.items():
        for j, other in rows.get(k, ()):
            out[i, j] = (out.get((i, j), 0) + value * other) % prime
    return {key: value for key, value in out.items() if value}


def add_entry(a, i, j, value, prime):
    out = dict(a)
    out[i, j] = (out.get((i, j), 0) + value) % prime
    if not out[i, j]:
        del out[i, j]
    return out


def check(actual, expected):
    global checks
    assert actual == expected, (actual, expected)
    checks += 1


for period in (11, 13, 17):
    size = 3 * period
    ident = identity(size)

    def point(color, level):
        return color * period + level % period

    for prime in (2, 3, 5, 7):
        def root(row_color, row_level, col_color, col_level, value=1):
            return add_entry(ident, point(row_color, row_level),
                             point(col_color, col_level), value, prime)

        def comm(a, b, ai, bi):
            return mul(mul(mul(a, b, prime), ai, prime), bi, prime)

        # Construct r by its permutation action, independently of the formula.
        mapping = {i: i for i in range(size)}
        for source, target in ((-1, -2), (-2, -3), (-3, -1)):
            mapping[point(2, source)] = point(2, target)
        r = {(target, source): 1 for source, target in mapping.items()}
        r_formula = dict(ident)
        for level in (-1, -2, -3):
            r_formula = add_entry(r_formula, point(2, level), point(2, level), -1, prime)
        for source, target in ((-1, -2), (-2, -3), (-3, -1)):
            r_formula = add_entry(r_formula, point(2, target), point(2, source), 1, prime)
        check(r, r_formula)
        shift = {(point(color, level + 1), point(color, level)): 1
                 for color in range(3) for level in range(period)}
        w = mul(shift, r, prime)
        wi = {(j, i): value for (i, j), value in w.items()}
        check(mul(w, wi, prime), ident)
        c, ci = root(0, -1, 2, -2), root(0, -1, 2, -2, -1)
        y, yi = root(2, -1, 1, 0), root(2, -1, 1, 0, -1)
        z, zi = root(2, -1, 2, -2), root(2, -1, 2, -2, -1)
        positive = range(period // 2 + 1)
        ell, elli = dict(ident), dict(ident)
        for level in positive:
            ell = add_entry(ell, point(1, level), point(0, level), 1, prime)
            elli = add_entry(elli, point(1, level), point(0, level), -1, prime)
        conjugate = mul(mul(w, c, prime), wi, prime)
        conjugate_i = mul(mul(w, ci, prime), wi, prime)
        check(conjugate, root(0, 0, 2, -2))
        delta = comm(conjugate, ell, conjugate_i, elli)
        check(delta, root(1, 0, 2, -2, -1))
        check(comm(y, delta, yi, root(1, 0, 2, -2)), zi)
        check(mul(mul(w, z, prime), wi, prime), z)
        check(mul(z, c, prime), mul(c, z, prime))
        check(mul(z, y, prime), mul(y, z, prime))
        power = dict(ident)
        for _ in range(prime):
            power = mul(power, z, prime)
        check(power, ident)
        assert z != ident
        a, ai = root(2, -2, 0, 0), root(2, -2, 0, 0, -1)
        first = comm(z, a, zi, ai)
        check(first, root(2, -1, 0, 0))
        b, bi = root(1, 0, 2, -1), root(1, 0, 2, -1, -1)
        check(comm(b, first, bi, root(2, -1, 0, 0, -1)), root(1, 0, 0, 0))

        # Constant, forward and backward coefficient roots on the positive part.
        for row in range(3):
            for col in range(3):
                if row == col:
                    continue
                for displacement in (-1, 0, 1):
                    generator = dict(ident)
                    for level in positive:
                        if level + displacement in positive:
                            generator = add_entry(generator, point(row, level + displacement),
                                                  point(col, level), 1, prime)
                    check(mul(c, generator, prime), mul(generator, c, prime))
                    check(mul(z, generator, prime), mul(generator, z, prime))

        # A finite cycle cannot realize the proper compression. Check the boundary.
        finite_compressed = mul(mul(w, ell, prime), wi, prime)
        outside = point(1, period // 2 + 1), point(0, period // 2 + 1)
        assert finite_compressed.get(outside) == 1
        checks += 1

# Independent finite-block checks of simultaneous involution localization.
localizations = 0
for size in range(4, 25):
    for old_size in range(1, size // 2 + 1):
        old = list(range(old_size))
        fresh = list(range(size - old_size, size))
        permutation = list(range(size))
        for source, target in zip(old, fresh):
            permutation[source], permutation[target] = target, source
        assert all(permutation[permutation[i]] == i for i in range(size))
        assert set(permutation[i] for i in old) <= set(fresh)
        for row in old:
            for col in old:
                assert permutation[row] in fresh and permutation[col] in fresh
        localizations += 1

print(json.dumps({
    'cell_identity_checks': checks,
    'finite_cycle_lengths': [11, 13, 17],
    'characteristics': [2, 3, 5, 7],
    'involution_localization_blocks': localizations,
    'finite_compression_boundary_detected': True,
    'seconds': round(time.monotonic() - started, 6),
    'scope': 'Finite identities and coordinate placement only; no infinite compression or Lean verification.',
}, indent=2))
