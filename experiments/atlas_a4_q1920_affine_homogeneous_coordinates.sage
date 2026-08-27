"""Build the faithful six-dimensional homogeneous affine Q1920 module.

The five-dimensional matrices and translation vectors are the exact GAP pcgs
data from atlas_a4_q1920_module_structure.g.  Rows act on the right.
"""

F = GF(2)

MARKINGS = [
    {
        "linear": [
            [[0,0,0,0,1],[0,0,0,1,1],[0,1,0,0,1],[0,0,1,0,1],[1,0,0,0,1]],
            [[0,1,0,1,0],[0,1,0,0,1],[1,1,0,0,0],[0,1,1,0,0],[0,1,0,0,0]],
            [[1,0,0,0,0],[1,0,0,1,0],[1,0,1,0,0],[1,1,0,0,0],[1,0,0,0,1]],
            [[0,0,0,1,0],[0,0,0,0,1],[0,0,1,0,0],[1,0,0,0,0],[0,1,0,0,0]],
        ],
        "translation": [[0,0,0,0,0],[1,0,0,1,1],[0,0,0,0,0],[0,1,1,0,1]],
    },
    {
        "linear": [
            [[0,0,0,1,0],[0,0,0,1,1],[0,1,0,1,0],[1,0,0,1,0],[0,0,1,1,0]],
            [[0,1,0,0,1],[0,1,0,1,0],[1,1,0,0,0],[0,1,0,0,0],[0,1,1,0,0]],
            [[1,0,0,0,0],[1,0,0,0,1],[1,0,1,0,0],[1,0,0,1,0],[1,1,0,0,0]],
            [[0,0,0,0,1],[0,0,0,1,0],[0,0,1,0,0],[0,1,0,0,0],[1,0,0,0,0]],
        ],
        "translation": [[0,0,0,1,0],[1,0,0,0,1],[1,1,1,1,1],[1,0,0,0,1]],
    },
]


def homogeneous(linear, translation):
    linear = matrix(F, linear)
    translation = vector(F, translation)
    result = block_matrix(F, [[linear, zero_matrix(F, 5, 1)],
                              [matrix(F, [translation * linear]), matrix(F, [[1]])]])
    return result


for marking_index, data in enumerate(MARKINGS, start=1):
    r, y, u, b = [homogeneous(linear, translation)
                  for linear, translation in zip(data["linear"],
                                                 data["translation"])]
    edge_words = [r.inverse()*b, u*y, (u*r)*y.inverse(), r*b*y]
    relators = ([r^3, y^3, u^2, b^2, u*r*u*r, b*y*b*y] +
                [word^3 for word in edge_words])
    print("marking=", marking_index,
          " relators_hold=", all(word.is_one() for word in relators),
          " generated_order=", MatrixGroup([r,y,u,b]).order(), sep="")
    for name, generator in zip(("r", "y", "u", "b"), (r, y, u, b)):
        print("marking", marking_index, "_", name, "=", generator.rows(), sep="")
