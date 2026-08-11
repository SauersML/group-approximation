"""Compute the Ash--Grayson--Green cuspidal function lattice on P^2(F_p).

For prime level p, top-degree cuspidal cohomology of Gamma_0(p) is the
space of functions on projective points satisfying the four relations quoted
in Theorem A.16 of Gunnells' computational appendix.  The first relation is a
signed symmetry.  Quotienting it with a signed disjoint-set structure before
linear algebra makes the remaining exact integer kernel very small.

The output is an integral kernel basis in projective-point coordinates and a
JSON certificate containing its Gram matrix and exact residual checks.
"""

import argparse
import hashlib
import json
from math import gcd

from sage.all import ZZ, is_prime, matrix


class SignedDisjointSet:
    """Maintain relations value(a) = sign * value(b), sign in {+1,-1}."""

    def __init__(self, size):
        self.parent = list(range(size))
        self.sign = [1] * size
        self.zero = [False] * size

    def find(self, item):
        parent = self.parent[item]
        if parent == item:
            return item, 1
        root, upper_sign = self.find(parent)
        self.sign[item] *= upper_sign
        self.parent[item] = root
        return root, self.sign[item]

    def equate(self, left, relation_sign, right):
        left_root, left_sign = self.find(left)
        right_root, right_sign = self.find(right)
        required = relation_sign * right_sign * left_sign
        if left_root == right_root:
            if required == -1:
                self.zero[left_root] = True
            return
        self.parent[left_root] = right_root
        self.sign[left_root] = required
        self.zero[right_root] = self.zero[right_root] or self.zero[left_root]

    def mark_zero(self, item):
        root, _sign = self.find(item)
        self.zero[root] = True

    def normalized(self, item):
        root, sign = self.find(item)
        return root, sign, self.zero[root]


def inverse(value, prime):
    return pow(int(value) % prime, prime - 2, prime)


def canonical(point, prime):
    reduced = tuple(int(value) % prime for value in point)
    for value in reduced:
        if value:
            scale = inverse(value, prime)
            return tuple((scale * coordinate) % prime for coordinate in reduced)
    raise ValueError("the zero vector has no projective class")


def projective_points(prime):
    points = []
    for y in range(prime):
        for z in range(prime):
            points.append((1, y, z))
    for z in range(prime):
        points.append((0, 1, z))
    points.append((0, 0, 1))
    return tuple(points)


def add_term(row, point, coefficient, point_index, quotient, root_index,
             prime):
    item = point_index[canonical(point, prime)]
    root, sign, is_zero = quotient.normalized(item)
    if is_zero:
        return
    column = root_index[root]
    value = row.get(column, 0) + coefficient * sign
    if value:
        row[column] = value
    elif column in row:
        del row[column]


def primitive_rows(rows):
    seen = set()
    result = []
    for row in rows:
        if not row:
            continue
        divisor = 0
        for value in row.values():
            divisor = gcd(divisor, abs(value))
        normalized = {column: value // divisor for column, value in row.items()}
        first_column = min(normalized)
        if normalized[first_column] < 0:
            normalized = {column: -value for column, value in normalized.items()}
        key = tuple(sorted(normalized.items()))
        if key not in seen:
            seen.add(key)
            result.append(normalized)
    return result


def verify_full_relations(points, point_index, basis, prime):
    failures = {
        "cyclic_symmetry": 0,
        "sign_symmetry": 0,
        "swap_antisymmetry": 0,
        "three_term": 0,
        "zero_boundary": 0,
        "parabolic_sum": 0,
    }
    for basis_row in range(basis.nrows()):
        values = basis.row(basis_row)
        for point_column, (x, y, z) in enumerate(points):
            value = values[point_column]
            if value != values[point_index[canonical((z, x, y), prime)]]:
                failures["cyclic_symmetry"] += 1
            if value != values[point_index[canonical((-x, y, z), prime)]]:
                failures["sign_symmetry"] += 1
            if value != -values[point_index[canonical((y, x, z), prime)]]:
                failures["swap_antisymmetry"] += 1
            three_term = value
            three_term += values[
                point_index[canonical((-y, x - y, z), prime)]]
            three_term += values[
                point_index[canonical((y - x, -x, z), prime)]]
            if three_term:
                failures["three_term"] += 1
            if z == 0 and value:
                failures["zero_boundary"] += 1
        for x in range(prime):
            for y in range(prime):
                if x == 0 and y == 0:
                    continue
                total = sum(
                    values[point_index[canonical((x, y, z), prime)]]
                    for z in range(prime))
                if total:
                    failures["parabolic_sum"] += 1
    return {key: int(value) for key, value in failures.items()}


def compute(prime):
    points = projective_points(prime)
    point_index = {point: index for index, point in enumerate(points)}
    quotient = SignedDisjointSet(len(points))

    for index, (x, y, z) in enumerate(points):
        quotient.equate(
            index, 1, point_index[canonical((z, x, y), prime)])
        quotient.equate(
            index, 1, point_index[canonical((-x, y, z), prime)])
        quotient.equate(
            index, -1, point_index[canonical((y, x, z), prime)])
        if z == 0:
            quotient.mark_zero(index)

    roots = sorted({quotient.normalized(index)[0] for index in range(len(points))
                    if not quotient.normalized(index)[2]})
    root_index = {root: index for index, root in enumerate(roots)}

    rows = []
    # The three-term modular-symbol relation.
    for x, y, z in points:
        row = {}
        add_term(row, (x, y, z), 1, point_index, quotient, root_index, prime)
        add_term(
            row, (-y, x - y, z), 1, point_index, quotient, root_index,
            prime)
        add_term(
            row, (y - x, -x, z), 1, point_index, quotient, root_index,
            prime)
        rows.append(row)

    # The parabolic/cuspidality relation sum_z f(x,y,z)=0.
    for x in range(prime):
        for y in range(prime):
            if x == 0 and y == 0:
                continue
            row = {}
            for z in range(prime):
                add_term(
                    row, (x, y, z), 1, point_index, quotient, root_index,
                    prime)
            rows.append(row)

    rows = primitive_rows(rows)
    relation_matrix = matrix(ZZ, len(rows), len(roots), sparse=True)
    for row_index, row in enumerate(rows):
        for column, value in row.items():
            relation_matrix[row_index, column] = value

    quotient_kernel = relation_matrix.right_kernel_matrix()
    if quotient_kernel.nrows():
        quotient_kernel = matrix(ZZ, quotient_kernel, sparse=False).LLL()
    full_basis = matrix(ZZ, quotient_kernel.nrows(), len(points))
    for point_column in range(len(points)):
        root, sign, is_zero = quotient.normalized(point_column)
        if is_zero:
            continue
        quotient_column = root_index[root]
        for basis_row in range(quotient_kernel.nrows()):
            full_basis[basis_row, point_column] = (
                sign * quotient_kernel[basis_row, quotient_column])

    if relation_matrix * quotient_kernel.transpose() != 0:
        raise AssertionError("quotient kernel fails an exact relation")
    full_failures = verify_full_relations(
        points, point_index, full_basis, prime)
    if any(full_failures.values()):
        raise AssertionError("integral basis fails a full cuspidal relation")
    gram = full_basis * full_basis.transpose()
    return points, full_basis, {
        "prime": prime,
        "projective_points": len(points),
        "signed_symmetry_variables": len(roots),
        "remaining_relations": len(rows),
        "remaining_relation_rank": int(relation_matrix.rank()),
        "cuspidal_dimension": int(full_basis.nrows()),
        "basis_maximum_absolute_coefficient": (
            max(abs(int(value)) for value in full_basis.list())
            if full_basis.nrows() else int(0)),
        "basis_support_sizes": [
            int(sum(1 for value in full_basis.row(row) if value))
            for row in range(full_basis.nrows())],
        "basis_gram": [
            [int(gram[row, column]) for column in range(gram.ncols())]
            for row in range(gram.nrows())],
        "exact_relation_verification": True,
        "full_relation_nonzero_residuals": full_failures,
    }


def write_basis(path, points, basis):
    digest = hashlib.sha256()
    with open(path, "w", encoding="ascii") as stream:
        header = "x y z " + " ".join(
            f"basis_{index}" for index in range(basis.nrows())) + "\n"
        stream.write(header)
        digest.update(header.encode("ascii"))
        for column, point in enumerate(points):
            values = point + tuple(
                int(basis[row, column]) for row in range(basis.nrows()))
            raw = " ".join(map(str, values)) + "\n"
            stream.write(raw)
            digest.update(raw.encode("ascii"))
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prime", type=int, required=True)
    parser.add_argument("--basis-output", required=True)
    parser.add_argument("--metadata-output")
    args = parser.parse_args()
    if args.prime <= 2 or not is_prime(args.prime):
        parser.error("--prime must be an odd prime")

    points, basis, metadata = compute(args.prime)
    metadata["basis_sha256"] = write_basis(
        args.basis_output, points, basis)
    rendered = json.dumps(metadata, indent=2, sort_keys=True) + "\n"
    if args.metadata_output:
        with open(args.metadata_output, "w", encoding="utf-8") as stream:
            stream.write(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
