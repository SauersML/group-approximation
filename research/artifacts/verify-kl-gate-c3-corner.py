#!/usr/bin/env python3
"""Exact bounded audit of the transported KL gate in the C3 corner.

An element of L_F2(1,2) is stored as a finite XOR-set of pairs (u,v),
representing s_u t_v.  Equality is decided in Bergman normal form by the
oriented rule s_1 t_1 -> 1+s_0 t_0.  Group-ring elements are XOR-sets of
these canonical units.
"""

def xor(*sets):
    out = set()
    for values in sets:
        out.symmetric_difference_update(values)
    return out


def canon(a):
    # Bergman normal form with s_1 t_1 rewritten as 1+s_0 t_0.
    # Thus no surviving monomial has both words ending in 1.
    def monomial(u, v):
        if u and v and u[-1] == "1" and v[-1] == "1":
            short = monomial(u[:-1], v[:-1])
            zero_child = monomial(u[:-1] + "0", v[:-1] + "0")
            return xor(short, zero_child)
        return {(u, v)}

    out = set()
    for u, v in a:
        out.symmetric_difference_update(monomial(u, v))
    return frozenset(out)


def add(*args):
    return canon(xor(*args))


def mul_monomial(left, right):
    u, v = left
    x, y = right
    if x.startswith(v):
        return (u + x[len(v):], y)
    if v.startswith(x):
        return (u, y + v[len(x):])
    return None


def mul(a, b):
    out = set()
    for left in a:
        for right in b:
            term = mul_monomial(left, right)
            if term is not None:
                if term in out:
                    out.remove(term)
                else:
                    out.add(term)
    return canon(out)


ZERO = frozenset()
ONE = canon({("", "")})
S0 = canon({("0", "")})
S1 = canon({("1", "")})
T0 = canon({("", "0")})
T1 = canon({("", "1")})
assert mul(T0, S0) == ONE and mul(T1, S1) == ONE
assert mul(T0, S1) == ZERO and mul(T1, S0) == ZERO
assert add(mul(S0, T0), mul(S1, T1)) == ONE


def mat(a, b, c, d):
    return ((a, b), (c, d))


def theta2(m):
    out = ZERO
    for i in range(2):
        for j in range(2):
            for u, v in m[i][j]:
                out = add(out, canon({(str(i) + u, str(j) + v)}))
    return out


def gr_add(*args):
    return xor(*args)


def gr_mul(a, b):
    out = set()
    for left in a:
        for right in b:
            term = mul(left, right)
            if term in out:
                out.remove(term)
            else:
                out.add(term)
    return out


def singleton(unit):
    return {unit}


def prefix(i):
    return "1" * (i - 1) + "0" if i < 20 else "1" * 19


def root(i, coefficient, j):
    out = ONE
    for u, v in coefficient:
        out = add(out, canon({(prefix(i) + u, prefix(j) + v)}))
    return out


def permutation_cycle():
    return canon({(prefix(i % 20 + 1), prefix(i)) for i in range(1, 21)})


g = theta2(mat(ZERO, ONE, ONE, ONE))
g2 = mul(g, g)
u = theta2(mat(ZERO, ONE, ONE, ZERO))
v = theta2(mat(ONE, ZERO, ONE, ONE))
w = theta2(mat(ONE, ONE, ZERO, ONE))
e = {g, g2}
k = {u, v, w}

U1 = theta2(mat(ONE, ZERO, T1, ONE))
U2 = theta2(mat(add(T0, ONE), ONE, ONE, ZERO))
U3 = g
V1 = theta2(mat(ONE, S1, ZERO, ONE))
V2 = theta2(mat(add(S0, ONE), ONE, ONE, ZERO))
V3 = g
t_lift = {U1, U2, U3}
s_lift = {V1, V2, V3}


def packet(x, x_inverse):
    return gr_mul(
        gr_mul(gr_mul(gr_mul(e, singleton(x)), k), singleton(x_inverse)), e
    )


def defect(x, x_inverse):
    p = packet(x, x_inverse)
    p_inverse = packet(x_inverse, x)
    return gr_add(
        gr_mul(gr_add(gr_mul(gr_mul(e, t_lift), e), p),
               gr_add(gr_mul(gr_mul(e, s_lift), e), p_inverse)),
        e,
    )


def power(a, n):
    out = ONE
    for _ in range(n):
        out = mul(out, a)
    return out


q = mul(root(3, S1, 4), root(11, T0, 12))
pcycle = permutation_cycle()
assert mul(q, q) == ONE
assert power(pcycle, 20) == ONE

candidates = []
for j in range(20):
    pj = power(pcycle, j)
    pinv = power(pcycle, (20 - j) % 20)
    qj = mul(mul(pj, q), pinv)
    assert mul(qj, qj) == ONE
    candidates.append((f"q_{j}", qj))

for name, candidate in candidates:
    residue = defect(candidate, candidate)
    assert ONE in residue
    print(name, "SOLVES" if not residue else f"fails: {len(residue)} odd units")

root_results = []
for i in range(1, 21):
    for j in range(1, 21):
        if i == j:
            continue
        candidate = root(i, ONE, j)
        assert mul(candidate, candidate) == ONE
        residue = defect(candidate, candidate)
        assert ONE in residue
        root_results.append((i, j, len(residue)))

solving_roots = [(i, j) for i, j, size in root_results if size == 0]
residue_sizes = sorted({size for _, _, size in root_results})
print("coefficient-one roots:", len(root_results), "tested")
print("coefficient-one root solutions:", solving_roots)
print("coefficient-one root residue sizes:", residue_sizes)
print("identity unit is an odd fiber in all 400 failed candidates")

# First audit the anchored family q_0 q_d, then all ordered products.  We do
# not assume that cyclic coordinate conjugation fixes the corner lifts A,B.
two_gate_results = []
q0 = candidates[0][1]
corner_a = gr_mul(gr_mul(e, t_lift), e)
corner_b = gr_mul(gr_mul(e, s_lift), e)
base_delta = gr_add(gr_mul(corner_a, corner_b), e)
assert ONE in base_delta
for d in range(1, 20):
    qd = candidates[d][1]
    candidate = mul(q0, qd)
    candidate_inverse = mul(qd, q0)
    assert mul(candidate, candidate_inverse) == ONE
    p_x = packet(candidate, candidate_inverse)
    p_x_inverse = packet(candidate_inverse, candidate)
    identity_correction_bits = (
        ONE in gr_mul(corner_a, p_x_inverse),
        ONE in gr_mul(p_x, corner_b),
        ONE in gr_mul(p_x, p_x_inverse),
    )
    assert identity_correction_bits == (False, False, False)
    residue = defect(candidate, candidate_inverse)
    two_gate_results.append((d, len(residue), ONE in residue))

print("two-gate orbit representatives (distance, odd units, identity odd):")
print(two_gate_results)
print("two-gate identity formula: 1(base)+(0+0+0)(corrections)=1")

all_two_gate_results = []
for i in range(20):
    qi = candidates[i][1]
    for j in range(20):
        if i == j:
            continue
        qj = candidates[j][1]
        candidate = mul(qi, qj)
        candidate_inverse = mul(qj, qi)
        p_x = packet(candidate, candidate_inverse)
        p_x_inverse = packet(candidate_inverse, candidate)
        correction_bits = (
            ONE in gr_mul(corner_a, p_x_inverse),
            ONE in gr_mul(p_x, corner_b),
            ONE in gr_mul(p_x, p_x_inverse),
        )
        residue = defect(candidate, candidate_inverse)
        all_two_gate_results.append(
            (i, j, len(residue), correction_bits, ONE in residue)
        )

assert all(identity_odd for _, _, _, _, identity_odd in all_two_gate_results)
print("all ordered two-gate products tested:", len(all_two_gate_results))
print("all ordered two-gate residue sizes:",
      sorted({size for _, _, size, _, _ in all_two_gate_results}))
print("all ordered correction-bit triples:",
      sorted({bits for _, _, _, bits, _ in all_two_gate_results}))


def cyclic_orbit(candidate):
    orbit = []
    for j in range(20):
        pj = power(pcycle, j)
        pinv = power(pcycle, (20 - j) % 20)
        moved = mul(mul(pj, candidate), pinv)
        assert mul(moved, moved) == ONE
        orbit.append(moved)
    return orbit


a_candidates = cyclic_orbit(root(1, S0, 2))
e_candidates = cyclic_orbit(root(1, T1, 2))


def audit_distinct_type(label, left_family, right_family):
    results = []
    for i, left in enumerate(left_family):
        for j, right in enumerate(right_family):
            candidate = mul(left, right)
            candidate_inverse = mul(right, left)
            assert mul(candidate, candidate_inverse) == ONE
            p_x = packet(candidate, candidate_inverse)
            p_x_inverse = packet(candidate_inverse, candidate)
            correction_bits = (
                ONE in gr_mul(corner_a, p_x_inverse),
                ONE in gr_mul(p_x, corner_b),
                ONE in gr_mul(p_x, p_x_inverse),
            )
            residue = defect(candidate, candidate_inverse)
            results.append(
                (i, j, len(residue), correction_bits, ONE in residue)
            )
    print(label, "tested:", len(results))
    print(label, "residue sizes:", sorted({row[2] for row in results}))
    print(label, "correction-bit triples:", sorted({row[3] for row in results}))
    print(label, "identity-odd count:", sum(row[4] for row in results))
    assert all(row[3] == (False, False, False) for row in results)
    assert all(row[4] for row in results)
    return results


distinct_type_results = {
    "q*a": audit_distinct_type("q*a", [unit for _, unit in candidates], a_candidates),
    "q*e": audit_distinct_type("q*e", [unit for _, unit in candidates], e_candidates),
    "a*q": audit_distinct_type("a*q", a_candidates, [unit for _, unit in candidates]),
    "e*q": audit_distinct_type("e*q", e_candidates, [unit for _, unit in candidates]),
}
