#!/usr/bin/env python3
"""Search a six-generator mixed-central packet with two endpoint shears.

Coordinates are (x0,z0,x1,z1,x2,z2).  The total K=J=- form is the
three-qubit Pauli form.  T1 and T2 are the two CNOT shears

    x0 -> x0+xi,   zi -> z0+zi

for i=1,2.  We enumerate quadratic J-forms fixed by both shears and ask for
rank(J)=4 while rank(J+K)=6, so switching K adds exactly one Pauli qubit.
"""
from __future__ import annotations

from itertools import combinations, product

N = 6
PAIRS = tuple(combinations(range(N), 2))
Vector = tuple[int, ...]
Matrix = tuple[Vector, ...]
Form = tuple[int, ...]


def basis(index: int) -> Vector:
    return tuple(int(index == row) for row in range(N))


def add(left: Vector, right: Vector) -> Vector:
    return tuple(a ^ b for a, b in zip(left, right))


def rank(rows: list[Vector]) -> int:
    work = [list(row) for row in rows]
    pivot = 0
    for column in range(N):
        found = next((row for row in range(pivot, len(work)) if work[row][column]), None)
        if found is None:
            continue
        work[pivot], work[found] = work[found], work[pivot]
        for row in range(len(work)):
            if row != pivot and work[row][column]:
                work[row] = [a ^ b for a, b in zip(work[row], work[pivot])]
        pivot += 1
    return pivot


def pairing(left: Vector, right: Vector, form: Form) -> int:
    return sum(
        value * ((left[i] & right[j]) ^ (left[j] & right[i]))
        for value, (i, j) in zip(form, PAIRS)
    ) & 1


def square(vector: Vector, form: Form) -> int:
    return sum(value * vector[i] * vector[j] for value, (i, j) in zip(form, PAIRS)) & 1


def preserves(columns: Matrix, form: Form) -> bool:
    return all(
        pairing(columns[i], columns[j], form) == pairing(basis(i), basis(j), form)
        for i in range(N)
        for j in range(N)
    ) and all(square(column, form) == 0 for column in columns)


def form_rank(form: Form) -> int:
    rows = [[0] * N for _ in range(N)]
    for value, (i, j) in zip(form, PAIRS):
        rows[i][j] = rows[j][i] = value
    return rank([tuple(row) for row in rows])


def cnot(target: int) -> Matrix:
    columns = [basis(i) for i in range(N)]
    columns[0] = add(columns[0], basis(2 * target))
    columns[2 * target + 1] = add(basis(1), columns[2 * target + 1])
    return tuple(columns)


def rank3(columns: tuple[tuple[int, ...], ...]) -> int:
    work = [list(row) for row in zip(*columns)]
    pivot = 0
    for column in range(3):
        found = next((row for row in range(pivot, 3) if work[row][column]), None)
        if found is None:
            continue
        work[pivot], work[found] = work[found], work[pivot]
        for row in range(3):
            if row != pivot and work[row][column]:
                work[row] = [a ^ b for a, b in zip(work[row], work[pivot])]
        pivot += 1
    return pivot


def dot3(left: tuple[int, ...], right: tuple[int, ...]) -> int:
    return sum(a & b for a, b in zip(left, right)) & 1


def endpoint_lift(z_columns: tuple[tuple[int, ...], ...]) -> Matrix:
    vectors3 = tuple(product((0, 1), repeat=3))
    x_columns = tuple(
        next(
            vector
            for vector in vectors3
            if all(dot3(vector, z_columns[k]) == int(j == k) for k in range(3))
        )
        for j in range(3)
    )
    columns = []
    for j in range(3):
        x_image = [0] * N
        z_image = [0] * N
        for i in range(3):
            x_image[2 * i] = x_columns[j][i]
            z_image[2 * i + 1] = z_columns[j][i]
        columns.extend((tuple(x_image), tuple(z_image)))
    return tuple(columns)


def square_mask(vector: Vector) -> int:
    return sum((vector[i] & vector[j]) << bit for bit, (i, j) in enumerate(PAIRS))


def pairing_mask(left: Vector, right: Vector) -> int:
    return sum(
        ((left[i] & right[j]) ^ (left[j] & right[i])) << bit
        for bit, (i, j) in enumerate(PAIRS)
    )


def invariance_constraints(columns: Matrix) -> tuple[int, ...]:
    equations = [square_mask(column) for column in columns]
    for bit, (i, j) in enumerate(PAIRS):
        equations.append(pairing_mask(columns[i], columns[j]) ^ (1 << bit))
    return tuple(equation for equation in equations if equation)


def audit() -> None:
    t1, t2 = cnot(1), cnot(2)
    total = tuple(int(pair in {(0, 1), (2, 3), (4, 5)}) for pair in PAIRS)
    assert preserves(t1, total) and preserves(t2, total)
    assert form_rank(total) == 6

    invariant_by_rank: dict[int, list[Form]] = {}
    for mask in range(1 << len(PAIRS)):
        j_form = tuple((mask >> bit) & 1 for bit in range(len(PAIRS)))
        if not preserves(t1, j_form) or not preserves(t2, j_form):
            continue
        invariant_by_rank.setdefault(form_rank(j_form), []).append(j_form)

    print(f"invariant J forms by rank={dict(sorted((r, len(v)) for r, v in invariant_by_rank.items()))}")
    solutions = invariant_by_rank.get(4, [])
    if not solutions:
        print("the two prescribed independent shears admit no one-qubit rank jump")
    else:
        solutions.sort(key=lambda form: (sum(form), form))
        chosen = solutions[0]
        k_form = tuple(a ^ b for a, b in zip(total, chosen))
        profiles = {
            (k, j): form_rank(tuple((k & a) ^ (j & b) for a, b in zip(k_form, chosen)))
            for k in (0, 1)
            for j in (0, 1)
        }
        assert profiles[(0, 1)] == 4 and profiles[(1, 1)] == 6

        print(f"invariant rank-four J forms={len(solutions)}")
        print(f"pair order={PAIRS}")
        print(f"chosen J form={chosen} weight={sum(chosen)}")
        print(f"induced K form={k_form} weight={sum(k_form)}")
        print(f"central-character ranks={profiles}")
        print("endpoint actions: z1->z0+z1, z2->z0+z2")

    vectors3 = tuple(product((0, 1), repeat=3))[1:]
    endpoint_matrices = [
        columns
        for columns in product(vectors3, repeat=3)
        if rank3(columns) == 3
    ]
    assert len(endpoint_matrices) == 168
    endpoint_lifts = [(columns, endpoint_lift(columns)) for columns in endpoint_matrices]
    assert all(preserves(lift, total) for _, lift in endpoint_lifts)

    rank_four_masks = []
    for mask in range(1 << len(PAIRS)):
        form = tuple((mask >> bit) & 1 for bit in range(len(PAIRS)))
        if form_rank(form) == 4:
            rank_four_masks.append(mask)

    constrained_actions = [
        (columns, invariance_constraints(lift))
        for columns, lift in endpoint_lifts
    ]
    stabilizers = []
    for mask in rank_four_masks:
        actions = [
            columns
            for columns, constraints in constrained_actions
            if all((mask & equation).bit_count() % 2 == 0 for equation in constraints)
        ]
        stabilizers.append((len(actions), mask.bit_count(), mask, actions))
    stabilizers.sort(key=lambda item: (-item[0], item[1], item[2]))
    size, _, best_mask, actions = stabilizers[0]
    best_j = tuple((best_mask >> bit) & 1 for bit in range(len(PAIRS)))
    best_k = tuple(a ^ b for a, b in zip(total, best_j))
    best_profiles = {
        (k, j): form_rank(tuple((k & a) ^ (j & b) for a, b in zip(best_k, best_j)))
        for k in (0, 1)
        for j in (0, 1)
    }
    print(f"maximum endpoint-linear stabilizer on rank-four J form={size}")
    print(f"best J form={best_j} weight={sum(best_j)}")
    print(f"best K form={best_k} weight={sum(best_k)}")
    print(f"best central-character ranks={best_profiles}")
    print(f"best endpoint actions={actions}")

    mixing_stabilizers = []
    endpoint_vectors = tuple(product((0, 1), repeat=3))[1:]
    for size, weight, mask, candidate_actions in stabilizers:
        j_form = tuple((mask >> bit) & 1 for bit in range(len(PAIRS)))
        radical_endpoints = []
        for endpoint in endpoint_vectors:
            vector = tuple(
                endpoint[index // 2] if index % 2 else 0
                for index in range(N)
            )
            if all(pairing(vector, basis(index), j_form) == 0 for index in range(N)):
                radical_endpoints.append(endpoint)
        for relative_endpoint in radical_endpoints:
            orbit = {
                tuple(
                    sum(columns[column][row] * relative_endpoint[column] for column in range(3)) & 1
                    for row in range(3)
                )
                for columns in candidate_actions
            }
            if len(orbit) >= 3:
                mixing_stabilizers.append(
                    (size, weight, mask, candidate_actions, orbit, relative_endpoint)
                )
    if not mixing_stabilizers:
        print("no rank-four J form has a three-point orbit of the relative endpoint")
        return
    mixing_stabilizers.sort(key=lambda item: (-item[0], item[1], item[2]))
    mix_size, _, mix_mask, mix_actions, mix_orbit, relative_endpoint = mixing_stabilizers[0]
    mix_j = tuple((mix_mask >> bit) & 1 for bit in range(len(PAIRS)))
    mix_k = tuple(a ^ b for a, b in zip(total, mix_j))
    mix_profiles = {
        (k, j): form_rank(tuple((k & a) ^ (j & b) for a, b in zip(mix_k, mix_j)))
        for k in (0, 1)
        for j in (0, 1)
    }
    assert mix_size == 6
    assert mix_j == (1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1)
    assert mix_k == (0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0)
    assert mix_orbit == {(0, 1, 1), (1, 0, 1), (1, 1, 0)}
    print(f"maximum stabilizer moving the relative endpoint={mix_size}")
    print(f"mixed J form={mix_j} weight={sum(mix_j)}")
    print(f"mixed K form={mix_k} weight={sum(mix_k)}")
    print(f"mixed central-character ranks={mix_profiles}")
    print(f"relative radical endpoint={relative_endpoint}")
    print(f"relative endpoint orbit={sorted(mix_orbit)}")
    print(f"mixed endpoint actions={mix_actions}")


if __name__ == "__main__":
    audit()
