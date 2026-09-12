"""Exact multiplicity-two Boolean collision SAT system for the Omega8+ type-B module.

The eight-dimensional matrices are in A-isotypic coordinates
H|A = 1^4 + U^2.  Thus End_A(H^2) is M_8(F2) x M_4(F2), encoded below by
twenty freely chosen 2 by 2 coefficient blocks.  Sage's exact ANF-to-CNF
converter and CryptoMiniSat test all 2^80 assignments without enumerating
them.  Requesting two solutions proves uniqueness when only the known
identity solution exists.
"""

if "MARKING" not in globals():
    MARKING = 1
if "RUN_SOLVER" not in globals():
    RUN_SOLVER = True

F = GF(2)

TUPLES = [
    [
        [[1,0,0,0,0,0,0,0],[0,1,0,0,0,0,0,0],[0,0,1,0,0,0,0,0],[0,0,0,1,0,0,0,0],[0,0,0,0,1,1,0,0],[0,0,0,0,1,0,0,0],[0,0,0,0,0,0,1,1],[0,0,0,0,0,0,1,0]],
        [[1,0,0,0,0,0,0,0],[1,1,0,0,1,0,0,1],[0,0,0,1,1,1,0,0],[0,0,1,0,1,1,0,0],[0,0,1,1,0,1,1,0],[0,0,0,0,0,1,0,1],[1,0,0,0,1,0,1,1],[1,0,1,1,0,1,0,0]],
        [[1,0,0,0,0,0,0,0],[0,1,0,0,0,0,0,0],[0,0,1,0,0,0,0,0],[0,0,0,1,0,0,0,0],[0,0,0,0,1,1,0,0],[0,0,0,0,0,1,0,0],[0,0,0,0,0,0,1,1],[0,0,0,0,0,0,0,1]],
        [[1,0,0,0,0,0,0,0],[0,1,0,0,1,0,0,1],[0,0,1,0,0,1,1,1],[0,0,0,1,0,1,1,1],[0,0,1,1,0,1,1,0],[1,0,1,1,0,0,1,1],[1,0,0,0,1,0,1,1],[0,0,1,1,1,1,1,1]],
    ],
    [
        [[1,0,0,0,0,0,0,0],[0,1,0,0,0,0,0,0],[0,0,1,0,0,0,0,0],[0,0,0,1,0,0,0,0],[0,0,0,0,0,1,0,0],[0,0,0,0,1,1,0,0],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1,1]],
        [[0,1,0,1,1,1,1,1],[0,1,1,0,0,1,0,0],[0,0,1,0,0,0,0,0],[1,1,1,0,1,0,1,1],[0,0,1,0,1,1,1,0],[0,0,1,0,0,0,0,1],[1,1,1,1,1,0,0,1],[0,0,1,0,0,1,0,1]],
        [[1,0,0,0,0,0,0,0],[0,1,0,0,0,0,0,0],[0,0,1,0,0,0,0,0],[0,0,0,1,0,0,0,0],[0,0,0,0,0,1,0,0],[0,0,0,0,1,0,0,0],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1,0]],
        [[1,0,0,0,0,1,1,0],[0,1,0,0,1,1,0,1],[0,0,1,0,0,0,0,0],[0,0,0,1,1,0,1,1],[0,0,1,0,1,1,1,0],[1,1,1,1,1,1,1,1],[1,1,1,1,1,0,0,1],[1,1,0,1,1,1,0,0]],
    ],
]

if MARKING not in (1, 2):
    raise ValueError("MARKING must be 1 or 2")

r, y, u, b = [matrix(F, rows) for rows in TUPLES[MARKING - 1]]
t = y.inverse()
s = b*y
calibration = [r^3, y^3, u^2, b^2, u*r*u*r, b*y*b*y,
               (r.inverse()*b)^3, (u*y)^3,
               ((u*r)*y.inverse())^3, (r*b*y)^3]
assert all(word.is_one() for word in calibration)
assert MatrixGroup([r, y, u, b]).order() == 1920

B = BooleanPolynomialRing(80, "v", order="deglex")
variables = B.gens()
coefficient_blocks = [matrix(B, 2, 2, variables[4*i:4*i+4])
                      for i in range(20)]
zero2 = zero_matrix(B, 2)
one2 = identity_matrix(B, 2)

c_blocks = [[zero2 for _ in range(8)] for _ in range(8)]
for i in range(4):
    for j in range(4):
        c_blocks[i][j] = coefficient_blocks[4*i+j]
for i in range(2):
    for j in range(2):
        block = coefficient_blocks[16+2*i+j]
        c_blocks[4+2*i][4+2*j] = block
        c_blocks[5+2*i][5+2*j] = block
C = block_matrix(B, c_blocks)


def scalar_lift(current):
    return block_matrix(B, [[one2 if entry else zero2 for entry in row]
                            for row in current.rows()])


T = scalar_lift(t)
T_inverse = scalar_lift(y)
S = scalar_lift(s)
identity = identity_matrix(B, 16)
relation_matrices = [C*C + identity, (C*T)^3 + identity,
                     T*C*S*C*T_inverse*C*S*T*C + identity]
relations = sorted(set(entry for current in relation_matrices
                       for entry in current.list() if entry), key=str)

identity_values = []
for i in range(4):
    for j in range(4):
        identity_values.extend([1, 0, 0, 1] if i == j else [0, 0, 0, 0])
for i in range(2):
    for j in range(2):
        identity_values.extend([1, 0, 0, 1] if i == j else [0, 0, 0, 0])
if RUN_SOLVER:
    from sage.sat.boolean_polynomials import solve as solve_sat
    from sage.sat.solvers import CryptoMiniSat

    print("marking=", MARKING,
          " variable_count=", len(variables),
          " relation_count=", len(relations),
          " anf_degree_histogram=",
          {degree: sum(relation.degree() == degree for relation in relations)
           for degree in sorted(set(relation.degree() for relation in relations))},
          " sat_start=true", sep="", flush=True)
    solutions = solve_sat(relations, solver=CryptoMiniSat, n=2,
                          target_variables=list(variables),
                          c_max_vars_sparse=8, c_cutting_number=8)
    print("marking=", MARKING, " sat_finished=true", sep="", flush=True)
    assert solutions
    assert all(all(relation.subs(solution) == 0 for relation in relations)
               for solution in solutions)
    solution_vectors = [[ZZ(solution[variable]) for variable in variables]
                        for solution in solutions]
    identity_forced = (len(solution_vectors) == 1 and
                       solution_vectors[0] == identity_values)

    print("marking=", MARKING,
          " variable_count=", len(variables),
          " relation_count=", len(relations),
          " returned_solution_count=", len(solutions),
          " identity_forced=", identity_forced, sep="", flush=True)
    print("solution_vectors=", solution_vectors, sep="", flush=True)

if RUN_SOLVER and not identity_forced:
    nonidentity = next(vector for vector in solution_vectors
                       if vector != identity_values)
    concrete_blocks = [matrix(F, 2, 2, nonidentity[4*i:4*i+4])
                       for i in range(20)]
    concrete_c_blocks = [[zero_matrix(F, 2) for _ in range(8)]
                         for _ in range(8)]
    for i in range(4):
        for j in range(4):
            concrete_c_blocks[i][j] = concrete_blocks[4*i+j]
    for i in range(2):
        for j in range(2):
            block = concrete_blocks[16+2*i+j]
            concrete_c_blocks[4+2*i][4+2*j] = block
            concrete_c_blocks[5+2*i][5+2*j] = block
    concrete_c = block_matrix(F, concrete_c_blocks)
    concrete_t = matrix(F, T)
    concrete_s = matrix(F, S)
    assert concrete_c^2 == 1
    assert (concrete_c*concrete_t)^3 == 1
    assert (concrete_t*concrete_c*concrete_s*concrete_c*
            concrete_t.inverse()*concrete_c*concrete_s*concrete_t*
            concrete_c) == 1
    local_group = MatrixGroup([concrete_t, concrete_s, concrete_c])
    print("nonidentity_matrix=", concrete_c.rows(), sep="")
    print("collision_vertex_order=", local_group.order(), sep="")
