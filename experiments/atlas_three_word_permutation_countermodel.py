#!/usr/bin/env python3
"""Exact 12-point permutation countermodel to the three-word A4 atlas gap.

The three candidate words at tree indices 6910, 6940 and collision 19243 only
see a C6 subgroup in chart one and an S3 subgroup in chart two.  This script
verifies that support reduction directly from the published 4x4 F2 matrices,
then exhausts a 12-point core and finds exact permutation solutions of all
three words.  The witness amplifies to every original regular-A8 multiplicity.

No floating point arithmetic or third-party package is used.
"""

N = 12
ID = tuple(range(N))


def compose(p, q):
    """Permutation product p*q, matching permutation-matrix multiplication."""
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p):
    out = [0] * len(p)
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)


def power(p, n):
    if n < 0:
        return power(inverse(p), -n)
    out = tuple(range(len(p)))
    base = p
    while n:
        if n & 1:
            out = compose(base, out)
        base = compose(base, base)
        n //= 2
    return out


def cycles(p):
    seen = set()
    out = []
    for i in range(len(p)):
        if i in seen:
            continue
        cyc = []
        j = i
        while j not in seen:
            seen.add(j)
            cyc.append(j)
            j = p[j]
        if len(cyc) > 1:
            out.append(tuple(cyc))
    return out


def cycle_string(p):
    return "".join("(" + " ".join(map(str, c)) + ")" for c in cycles(p)) or "()"


def fixed_c6(step):
    # Two regular C6 orbits.  r=+2 has order 3; c=+3 has order 2.
    return tuple(copy * 6 + ((i + step) % 6) for copy in range(2) for i in range(6))


def perfect_matchings(n):
    """All fixed-point-free involutions on n points."""
    used = [False] * n
    p = [None] * n

    def rec():
        i = next((i for i in range(n) if not used[i]), None)
        if i is None:
            yield tuple(p)
            return
        used[i] = True
        for j in range(i + 1, n):
            if used[j]:
                continue
            used[j] = True
            p[i] = j
            p[j] = i
            yield from rec()
            used[j] = False
        used[i] = False

    yield from rec()


def orbit(start, generators):
    seen = {start}
    todo = [start]
    while todo:
        i = todo.pop()
        for g in generators:
            j = g[i]
            if j not in seen:
                seen.add(j)
                todo.append(j)
    return seen


# --- Exact F2 support audit -------------------------------------------------
def decode4(hex_string):
    data = bytes.fromhex(hex_string)
    assert len(data) == 16 and set(data) <= {0, 1}
    return tuple(tuple(data[4 * i + j] for j in range(4)) for i in range(4))


I4 = tuple(tuple(int(i == j) for j in range(4)) for i in range(4))


def mul4(a, b):
    return tuple(
        tuple(sum(a[i][k] * b[k][j] for k in range(4)) % 2 for j in range(4))
        for i in range(4)
    )


def pow4(a, n):
    out = I4
    for _ in range(n):
        out = mul4(out, a)
    return out


def subgroup4(generators):
    seen = {I4}
    todo = [I4]
    while todo:
        x = todo.pop()
        for g in generators:
            y = mul4(x, g)
            if y not in seen:
                seen.add(y)
                todo.append(y)
    return seen


# The two packet contexts and collision 19243, copied from the canonical data.
b = decode4("01000000010100000000010000000001")
a = decode4("01010000010000000000010000000001")
bv = decode4("01010000000100000000010000000001")
av = decode4("00010000010100000000010000000001")
c4 = decode4("01000000000100000000010100000001")
q_factor2 = [
    decode4("01010000010000000000010000000001"),
    decode4("01000000010100000000010000000001"),
    decode4("00010000010100000000010000000001"),
    decode4("01010000000100000000010000000001"),
]

assert pow4(a, 3) == I4 and pow4(b, 2) == I4
assert av == pow4(a, 2)
assert bv == mul4(b, a)
assert q_factor2 == [a, b, pow4(a, 2), mul4(b, a)]
assert pow4(c4, 2) == I4 and mul4(a, c4) == mul4(c4, a)
assert len(subgroup4([a, c4])) == 6  # C3 x C2 = C6
assert len(subgroup4([a, b])) == 6   # S3


# --- 12-point exact core ----------------------------------------------------
r = fixed_c6(2)
c = fixed_c6(3)
r_inv = inverse(r)

# Exact u=(y r)^3 and v=(z r^-1)^3 force y,z into these finite lists.
y_candidates = [y for y in perfect_matchings(N) if power(compose(y, r), 3) == ID]
z_candidates = [z for z in perfect_matchings(N) if power(compose(z, r_inv), 3) == ID]
assert len(y_candidates) == 162 == len(z_candidates)

solutions = []
for y in y_candidates:
    for z in z_candidates:
        # In S3 notation z=y*x, hence x=y*z.
        x = compose(y, z)
        if power(x, 3) != ID:
            continue
        # q = x c y c x^-1 c z c.
        q = compose(
            compose(
                compose(
                    compose(
                        compose(
                            compose(
                                compose(x, c), y
                            ), c
                        ), inverse(x)
                    ), c
                ), z
            ), c
        )
        if q != ID:
            continue
        # Two 6-point orbits mean the S3 action is 2 Reg(S3), not a quotient.
        remaining = set(range(N))
        orbits = []
        while remaining:
            o = orbit(min(remaining), [x, y])
            orbits.append(o)
            remaining -= o
        if sorted(map(len, orbits)) != [6, 6]:
            continue
        solutions.append((x, y, z, orbits))

assert len(solutions) == 72
x, y, z, orbits = solutions[0]
assert power(compose(y, r), 3) == ID
assert power(compose(z, r_inv), 3) == ID
q = compose(compose(compose(compose(compose(compose(compose(x, c), y), c), inverse(x)), c), z), c)
assert q == ID

print("support: chart1=<a,c> is C6; chart2=<a,b> is S3")
print("exact 12-point solutions:", len(solutions))
print("r =", cycle_string(r))
print("c =", cycle_string(c))
print("x =", cycle_string(x))
print("y =", cycle_string(y))
print("z =", cycle_string(z))
print("S3 orbit sizes:", sorted(map(len, orbits)))
print("u=v=q=identity: yes")
print("amplification: repeat this core 1680*k times to reach dimension 20160*k")
