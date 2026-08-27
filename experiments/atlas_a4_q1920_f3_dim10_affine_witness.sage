# Exact affine witness extracted from the marking-1, module-6 polynomial seam
# calculation in atlas_a4_q1920_f3_seam_polynomial.sage.

load("atlas_a4_q1920_f3_seam_data.py")

F3 = GF(3)
record = next(record for record in modules
              if (record["marking"], record["module_index"]) == (1, 6))
d = record["dimension"]
assert d == 10 and record["image_order"] == 1920


def linear(rows):
    return matrix(F3, rows)


def homogeneous_linear(current):
    return block_matrix(F3, [[current, zero_matrix(F3, d, 1)],
                             [zero_matrix(F3, 1, d), matrix(F3, [[1]])]])


def homogeneous_translation(vector_row):
    return block_matrix(F3, [[identity_matrix(F3, d),
                              zero_matrix(F3, d, 1)],
                             [matrix(F3, [vector_row]), matrix(F3, [[1]])]])


r0 = linear(record["r"])
u0 = linear(record["u"])
t0 = linear(record["t"])
s0 = linear(record["s"])
c0 = linear([
    [2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 2, 0, 0, 0, 0, 2, 0],
    [0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 2, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 2, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
])
z0 = vector(F3, [1, 1, 0, 2, 1, 2, 0, 2, 0, 0])

r = homogeneous_linear(r0)
u = homogeneous_linear(u0)
t = homogeneous_linear(t0)
s = homogeneous_linear(s0)
c = homogeneous_linear(c0)
z = homogeneous_translation(z0)
y = t^-1
b = s*t
one = identity_matrix(F3, d + 1)

relations = {
    "r3": r^3,
    "y3": y^3,
    "u2": u^2,
    "b2": b^2,
    "urur": u*r*u*r,
    "byby": b*y*b*y,
    "r^-1-b cube": (r^-1*b)^3,
    "u-y cube": (u*y)^3,
    "ur-y^-1 cube": ((u*r)*y^-1)^3,
    "r-b-y cube": (r*b*y)^3,
    "z3": z^3,
    "c2": c^2,
    "[r,z]": r*z*r^-1*z^-1,
    "[c,r]": c*r*c^-1*r^-1,
    "(cz)2": (c*z)^2,
    "[u,z]": u*z*u^-1*z^-1,
    "[u,c]": u*c*u^-1*c^-1,
    "(ct)3": (c*t)^3,
    "collision q": t*c*s*c*t^-1*c*s*t*c,
}
failures = [name for name, value in relations.items() if value != one]
assert not failures, failures
assert z != one and c != one

groups = {
    "Q=<r,y,u,b>": MatrixGroup([r, y, u, b]),
    "F=<r,z,c,u>": MatrixGroup([r, z, c, u]),
    "J=<t,s,c>": MatrixGroup([t, s, c]),
    "C=<r,z,b>": MatrixGroup([r, z, b]),
    "linear=<r,y,u,b,c>": MatrixGroup([r, y, u, b, c]),
    "affine=<r,y,u,b,c,z>": MatrixGroup([r, y, u, b, c, z]),
}
orders = {name: group.order() for name, group in groups.items()}

print({
    "field": 3,
    "linear_dimension": d,
    "homogeneous_dimension": d + 1,
    "module": (record["marking"], record["module_index"]),
    "all_relations": True,
    "protected_nonidentity": {"c": c != one, "z": z != one},
    "orders": orders,
})
