"""Put the marked natural PSL5(2) module in A=S3 isotypic coordinates.

This is a five-dimensional exact calibration.  Rows act on the right, matching
the GAP matrices exported by atlas_a4_q1920_psl5_repeated_module_seam.g.
"""

F = GF(2)


def mat(rows):
    return matrix(F, rows)


r = mat([
    [1, 0, 1, 1, 1],
    [0, 0, 1, 1, 1],
    [1, 1, 0, 1, 0],
    [1, 0, 0, 0, 1],
    [0, 0, 1, 0, 0],
])
y = mat([
    [0, 1, 1, 0, 0],
    [1, 1, 0, 1, 0],
    [1, 1, 0, 0, 1],
    [0, 0, 1, 0, 0],
    [1, 0, 1, 0, 0],
])
u = mat([
    [1, 0, 0, 0, 0],
    [0, 0, 1, 1, 1],
    [0, 1, 0, 1, 1],
    [1, 0, 0, 0, 1],
    [1, 0, 0, 1, 0],
])
b = mat([
    [1, 0, 1, 1, 0],
    [1, 1, 0, 1, 0],
    [0, 0, 0, 1, 0],
    [0, 0, 1, 0, 0],
    [1, 0, 1, 0, 1],
])
t = y.inverse()
s = b * y

V = VectorSpace(F, 5)
stable_two_spaces = []
for subspace in V.subspaces(2):
    if all(vector * generator in subspace
           for generator in (r, u) for vector in subspace.basis()):
        stable_two_spaces.append(subspace)

fixed = (r - 1).left_kernel().intersection((u - 1).left_kernel())
assert fixed.dimension() == 1

chosen = None
for left in stable_two_spaces:
    for right in stable_two_spaces:
        if left == right or left.intersection(right).dimension() != 0:
            continue
        if (left + right).intersection(fixed).dimension() != 0:
            continue
        chosen = left, right
        break
    if chosen is not None:
        break
assert chosen is not None

change = matrix(F, list(chosen[0].basis()) + list(chosen[1].basis()) +
                list(fixed.basis()))
assert change.is_invertible()


def conjugate(generator):
    return change * generator * change.inverse()


print("stable_two_space_count=", len(stable_two_spaces), sep="")
print("change_of_basis_rows=", change.rows(), sep="")
for name, generator in (("r", r), ("y", y), ("u", u), ("b", b),
                        ("t", t), ("s", s)):
    print(name, "=", conjugate(generator).rows(), sep="")

# Tangent space at the identity collision involution.  Since the scalar
# coefficient ring has characteristic two, c=1+epsilon*d is automatically an
# involution over dual numbers.  Linearize the other two collision relations.
rr, yy, uu, bb, tt, ss = map(conjugate, (r, y, u, b, t, s))
centralizer_rows = []
for i in range(5):
    for j in range(5):
        unit = matrix(F, 5, 5)
        unit[i, j] = 1
        centralizer_rows.append(
            list((unit*rr - rr*unit).list()) +
            list((unit*uu - uu*unit).list()))
centralizer_basis_coordinates = matrix(F, centralizer_rows).left_kernel().basis()
centralizer_basis = [matrix(F, 5, 5, coordinates[:25])
                     for coordinates in centralizer_basis_coordinates]
assert len(centralizer_basis) == 5


def collision_word(factors):
    result = identity_matrix(F, 5)
    for factor in factors:
        result *= factor
    return result


def linearized_word(constants, c_positions, direction):
    result = matrix(F, 5, 5)
    for position in c_positions:
        term = identity_matrix(F, 5)
        for index, constant in enumerate(constants):
            term *= direction if index == position else constant
        result += term
    return result


# (c*t)^3 has c in positions 0,2,4.
ct_constants = [identity_matrix(F, 5), tt] * 3
# t*c*s*c*t^-1*c*s*t*c has c in positions 1,3,5,8.
q_constants = [tt, identity_matrix(F, 5), ss, identity_matrix(F, 5),
               tt.inverse(), identity_matrix(F, 5), ss, tt,
               identity_matrix(F, 5)]
tangent_rows = []
for direction in centralizer_basis:
    tangent_rows.append(
        list(linearized_word(ct_constants, [0, 2, 4], direction).list()) +
        list(linearized_word(q_constants, [1, 3, 5, 8], direction).list()))
tangent_kernel = matrix(F, tangent_rows).left_kernel()
print("centralizer_basis_count=", len(centralizer_basis), sep="")
print("identity_collision_tangent_dimension=", tangent_kernel.dimension(), sep="")
print("identity_collision_tangent_coordinates=", tangent_kernel.basis(), sep="")
