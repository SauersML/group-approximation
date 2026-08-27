"""Audited circuit-CNF screen for the Omega8+ type-B seam at multiplicity two.

The expanded source ANF has about 1.5 million monomials, so translating that
normal form is needlessly large.  This file instead encodes the three matrix
word identities directly as a Boolean circuit.  Matrix multiplication over F2
uses only binary AND and XOR gates.  Every Tseitin gate's CNF truth table is
exhaustively audited before the solver runs.  The final CNF includes a clause
excluding the known identity matrix, so UNSAT is exactly uniqueness of that
solution at multiplicity two.
"""

if "MARKING" not in globals():
    MARKING = 1

RUN_SOLVER = False
load("atlas_a4_q1920_o8plus_typeb_m2_boolean.sage")

from hashlib import sha256
from itertools import product
from pycryptosat import Solver


original_variable_count = len(variables)
clauses = []
gate_audits = []
next_variable = original_variable_count


def new_variable():
    global next_variable
    next_variable += 1
    return next_variable


# A distinguished asserted variable lets signed literals represent constants.
true_literal = new_variable()
clauses.append((true_literal,))
false_literal = -true_literal


def add_and_gate(left, right):
    """Return a literal for left AND right, simplifying constants exactly."""
    if left == false_literal or right == false_literal or left == -right:
        return false_literal
    if left == true_literal:
        return right
    if right == true_literal or left == right:
        return left
    output = new_variable()
    local = ((left, -output), (right, -output),
             (output, -left, -right))
    clauses.extend(local)
    gate_audits.append(("and", left, right, output, local))
    return output


def add_xor_gate(left, right):
    """Return a literal for left XOR right, simplifying constants exactly."""
    if left == false_literal:
        return right
    if right == false_literal:
        return left
    if left == true_literal:
        return -right
    if right == true_literal:
        return -left
    if left == right:
        return false_literal
    if left == -right:
        return true_literal
    output = new_variable()
    local = ((left, right, -output), (left, -right, output),
             (-left, right, output), (-left, -right, -output))
    clauses.extend(local)
    gate_audits.append(("xor", left, right, output, local))
    return output


def xor_sum(entries):
    result = false_literal
    for entry in entries:
        result = add_xor_gate(result, entry)
    return result


def circuit_matrix_multiply(left, right):
    row_count = len(left)
    inner = len(right)
    column_count = len(right[0])
    assert len(left[0]) == inner
    return [[xor_sum(add_and_gate(left[i][k], right[k][j])
                     for k in range(inner))
             for j in range(column_count)]
            for i in range(row_count)]


def fixed_matrix(current):
    return [[true_literal if current[i, j] else false_literal
             for j in range(current.ncols())]
            for i in range(current.nrows())]


def circuit_identity(size):
    return [[true_literal if i == j else false_literal
             for j in range(size)] for i in range(size)]


def constrain_equal(left, right):
    for left_row, right_row in zip(left, right):
        for left_entry, right_entry in zip(left_row, right_row):
            difference = add_xor_gate(left_entry, right_entry)
            clauses.append((-difference,))


# Rebuild the A-central unknown C from its twenty 2x2 coefficient blocks.  The
# first sixteen blocks form M4(M2), while the last four form M2(M2) tensor I_U.
input_blocks = []
for block_index in range(20):
    start = 4 * block_index + 1
    input_blocks.append([[start, start + 1], [start + 2, start + 3]])

circuit_c = [[false_literal for _ in range(16)] for _ in range(16)]
for i in range(4):
    for j in range(4):
        block = input_blocks[4 * i + j]
        for ii in range(2):
            for jj in range(2):
                circuit_c[2 * i + ii][2 * j + jj] = block[ii][jj]
for i in range(2):
    for j in range(2):
        block = input_blocks[16 + 2 * i + j]
        for copy in range(2):
            for ii in range(2):
                for jj in range(2):
                    circuit_c[2 * (4 + 2 * i + copy) + ii][2 * (4 + 2 * j + copy) + jj] = block[ii][jj]

circuit_t = fixed_matrix(matrix(F, T))
circuit_t_inverse = fixed_matrix(matrix(F, T_inverse))
circuit_s = fixed_matrix(matrix(F, S))
circuit_i = circuit_identity(16)


def circuit_word(factors):
    result = factors[0]
    for factor in factors[1:]:
        result = circuit_matrix_multiply(result, factor)
    return result


constrain_equal(circuit_word([circuit_c, circuit_c]), circuit_i)
constrain_equal(circuit_word([circuit_c, circuit_t,
                              circuit_c, circuit_t,
                              circuit_c, circuit_t]), circuit_i)
constrain_equal(circuit_word([circuit_t, circuit_c, circuit_s, circuit_c,
                              circuit_t_inverse, circuit_c, circuit_s,
                              circuit_t, circuit_c]), circuit_i)

# Exclude C=I on the eighty original coefficient variables.
clauses.append(tuple(-index if value else index
                     for index, value in enumerate(identity_values, start=1)))


def literal_value(literal, assignment):
    value = assignment[abs(literal)]
    return value if literal > 0 else not value


def clause_value(clause, assignment):
    return any(literal_value(literal, assignment) for literal in clause)


def audit_gate(kind, left, right, output, local_clauses):
    variables_here = sorted(set(map(abs, (left, right, output))))
    for values in product([False, True], repeat=len(variables_here)):
        assignment = dict(zip(variables_here, values))
        cnf_value = all(clause_value(clause, assignment)
                        for clause in local_clauses)
        left_value = literal_value(left, assignment)
        right_value = literal_value(right, assignment)
        output_value = literal_value(output, assignment)
        intended = output_value == (left_value and right_value)
        if kind == "xor":
            intended = output_value == (left_value != right_value)
        assert cnf_value == intended


for gate in gate_audits:
    audit_gate(*gate)

# Independently evaluate the expanded source ANF at the known identity point.
identity_substitution = dict(zip(variables, identity_values))
assert all(relation.subs(identity_substitution) == 0
           for relation in relations)

dimacs_lines = ["p cnf %d %d" % (next_variable, len(clauses))]
dimacs_lines.extend(" ".join(str(literal) for literal in clause) + " 0"
                    for clause in clauses)
dimacs = "\n".join(dimacs_lines) + "\n"

print("marking=", MARKING,
      " original_variables=", original_variable_count,
      " auxiliary_variables=", next_variable - original_variable_count,
      " clauses=", len(clauses),
      " and_gates=", sum(gate[0] == "and" for gate in gate_audits),
      " xor_gates=", sum(gate[0] == "xor" for gate in gate_audits),
      " all_gate_truth_tables_audited=true",
      " identity_source_anf_verified=true",
      " dimacs_sha256=", sha256(dimacs.encode()).hexdigest(),
      " solver_start=true", sep="", flush=True)

solver = Solver()
for clause in clauses:
    solver.add_clause([int(literal) for literal in clause])
satisfiable, model = solver.solve()
print("marking=", MARKING, " solver_finished=true",
      " nonidentity_satisfiable=", satisfiable, sep="", flush=True)

if satisfiable:
    witness = [ZZ(model[index]) for index in range(1, original_variable_count + 1)]
    witness_substitution = dict(zip(variables, witness))
    assert witness != identity_values
    # This check uses the separately expanded source ANF rather than the circuit.
    assert all(relation.subs(witness_substitution) == 0
               for relation in relations)
    print("witness_source_anf_verified=true witness=", witness,
          sep="", flush=True)
