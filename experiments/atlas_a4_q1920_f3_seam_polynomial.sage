# Exact finite-field polynomial feasibility for a collision involution on the
# exported marked F3[Q1920] modules.  By default solve only dimension ten; set
# TARGET_DIMENSIONS below for further calibrated runs.

load("atlas_a4_q1920_f3_seam_data.py")

TARGET_KEYS = {(1, 6)}
F = GF(3)


def matrix_over_f3(rows):
    return matrix(F, rows)


def centralizer_basis(generators):
    d = generators[0].nrows()
    columns = []
    for i in range(d):
        for j in range(d):
            elementary = matrix(F, d, d)
            elementary[i, j] = 1
            columns.append(vector(F, sum(
                ((elementary * generator - generator * elementary).list()
                 for generator in generators), [])))
    constraint = matrix(F, columns).transpose()
    basis_vectors = constraint.right_kernel().basis()
    return [matrix(F, d, d, list(vector_)) for vector_ in basis_vectors]


def nonzero_entries(matrices):
    return [entry for current in matrices for entry in current.list()
            if entry != 0]


def triangular_point(basis, variables):
    """Extract one F3 point from a triangular Groebner basis.

    This deliberately avoids ``Ideal.variety()``, which enumerates the whole
    finite variety before returning and is needlessly expensive for these
    zero-dimensional ideals.
    """
    point = {}
    while len(point) < len(variables):
        progress = False
        for polynomial in basis:
            specialized = polynomial.subs(point)
            remaining = [variable for variable in variables
                         if variable not in point and specialized.degree(variable) > 0]
            if len(remaining) != 1:
                continue
            variable = remaining[0]
            roots = [value for value in F
                     if specialized.subs({variable: value}) == 0]
            if roots:
                point[variable] = roots[0]
                progress = True
        if not progress:
            raise RuntimeError("Groebner basis is not triangular over F3")
    assert all(polynomial.subs(point) == 0 for polynomial in basis)
    return point


def solve_module(record):
    r = matrix_over_f3(record["r"])
    u = matrix_over_f3(record["u"])
    t = matrix_over_f3(record["t"])
    s = matrix_over_f3(record["s"])
    d = record["dimension"]
    end_basis = centralizer_basis([r, u])

    # Sage-side common fixed space for row vectors.
    identityF = identity_matrix(F, d)
    fixed = block_matrix(F, 1, 2,
                         [r - identityF, u - identityF]).left_kernel().basis()
    n = len(end_basis)
    f = len(fixed)
    ring = PolynomialRing(F, n + f, names=[
        *(f"x{i}" for i in range(n)), *(f"v{i}" for i in range(f))])
    variables = ring.gens()
    xs = variables[:n]
    vs = variables[n:]
    c = sum((xs[i] * end_basis[i] for i in range(n)),
            matrix(ring, d, d))
    identity = identity_matrix(ring, d)
    tR = t.change_ring(ring)
    sR = s.change_ring(ring)

    equations = []
    equations += nonzero_entries([c*c - identity])
    equations += nonzero_entries([(c*tR)^3 - identity])
    collision = tR*c*sR*c*(tR^-1)*c*sR*tR*c
    equations += nonzero_entries([collision - identity])

    signal = sum((vs[i] * vector(ring, list(fixed[i])) for i in range(f)),
                 vector(ring, d))
    equations += [entry for entry in signal*c + signal if entry != 0]
    equations.append(prod(1 - value^2 for value in vs))
    equations += [value^3 - value for value in variables]

    ideal = ring.ideal(equations)
    basis = ideal.groebner_basis()
    unsat = len(basis) == 1 and basis[0] == ring.one()
    result = {
        "marking": record["marking"],
        "module_index": record["module_index"],
        "dimension": d,
        "image_order": record["image_order"],
        "endomorphism_dimension": n,
        "A_fixed_dimension": f,
        "equation_count": len(equations),
        "groebner_basis_length": len(basis),
        "unsat": bool(unsat),
    }
    print({**result, "groebner_basis": [str(polynomial) for polynomial in basis]})
    if not unsat:
        point = triangular_point(basis, variables)
        c_value = sum((point[xs[i]] * end_basis[i] for i in range(n)),
                      matrix(F, d, d))
        signal_value = sum(
            (point[vs[i]] * vector(F, list(fixed[i])) for i in range(f)),
            vector(F, d))
        assert c_value^2 == identity_matrix(F, d)
        assert (c_value*t)^3 == identity_matrix(F, d)
        assert t*c_value*s*c_value*(t^-1)*c_value*s*t*c_value == identity_matrix(F, d)
        assert signal_value*c_value == -signal_value
        result["witness_extraction"] = "triangular Groebner basis"
        result["c_matrix"] = [[int(value) for value in row]
                              for row in c_value.rows()]
        result["z_vector"] = [int(value) for value in signal_value]
    print(result)


for module_record in modules:
    if (module_record["marking"], module_record["module_index"]) in TARGET_KEYS:
        solve_module(module_record)
