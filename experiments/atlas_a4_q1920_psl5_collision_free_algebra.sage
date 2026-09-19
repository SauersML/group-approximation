"""Universal collision equations on repeated natural PSL5(2) modules.

After putting W|A in U+U+1 coordinates, every A-central endomorphism on
W^m is encoded by five m by m coefficients p11,p12,p21,p22,q.  This script
forms the exact noncommutative polynomial equations for a collision
involution c.  It does not assume that the coefficient matrices commute.
"""

F = GF(2)
R = FreeAlgebra(F, 5, names=("p11", "p12", "p21", "p22", "q"))
p11, p12, p21, p22, q = R.gens()


def scalar_matrix(rows):
    return matrix(R, [[R(entry) for entry in row] for row in rows])


t = scalar_matrix([
    [1, 0, 1, 0, 1],
    [1, 0, 0, 1, 1],
    [1, 0, 0, 0, 0],
    [0, 1, 1, 1, 0],
    [0, 0, 0, 0, 1],
])
s = scalar_matrix([
    [0, 0, 1, 1, 1],
    [1, 0, 0, 1, 1],
    [1, 1, 1, 1, 1],
    [0, 1, 1, 1, 0],
    [0, 0, 0, 0, 1],
])
c = matrix(R, [
    [p11, 0, p12, 0, 0],
    [0, p11, 0, p12, 0],
    [p21, 0, p22, 0, 0],
    [0, p21, 0, p22, 0],
    [0, 0, 0, 0, q],
])
identity = identity_matrix(R, 5)

relation_matrices = {
    "c2": c*c + identity,
    "ct3": (c*t)^3 + identity,
    "collision": t*c*s*c*(t^-1)*c*s*t*c + identity,
}


def unique_nonzero_entries(current):
    result = []
    for entry in current.list():
        if entry != 0 and entry not in result:
            result.append(entry)
    return result


all_relations = []
for name, current in relation_matrices.items():
    entries = unique_nonzero_entries(current)
    print(name, "_relation_count=", len(entries), sep="")
    for index, entry in enumerate(entries):
        print(name, "_", index, "=", entry, sep="")
        if entry not in all_relations:
            all_relations.append(entry)
print("total_unique_relations=", len(all_relations), sep="")
