"""Bounded exact GL3(F2) probe for {r_star,R_v,R_0,R_sum,d^2}.

Run only on MSI after review. Filter the 512 binary 3x3 matrices, then
try every order-three C and every ordered triple from each of two fixed
V4 subgroups. At most 56*2*4^3=7168 tuples and five seconds; no random
choices, restarts, third-party packages, or larger groups are searched.

Matrix encoding is column-packed: bit (3*j+i) is entry (i,j), zero-based.
Products act on columns, so (AB)v=A(Bv). A central C2^3 factor can make the
marked b_i independent even when their GL3(F2) images include identity.
"""

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import signal
import time


IDENTITY = (1 << 0) | (1 << 4) | (1 << 8)
ROW_NAMES = ("r_star", "R_v", "R_0", "R_sum", "d_squared")
MAX_TUPLES = 7168
WALL_SECONDS = 5.0


class EnumerationBudgetExpired(Exception):
    """Keep the completed enumeration counts when the fixed budget expires."""


def expire_enumeration(_signum, _frame):
    raise EnumerationBudgetExpired


def matrix_vector(matrix, vector):
    return ((matrix & 7) if vector & 1 else 0) ^ (
        ((matrix >> 3) & 7) if vector & 2 else 0
    ) ^ (((matrix >> 6) & 7) if vector & 4 else 0)


def matrix_product(left, right):
    return (matrix_vector(left, right & 7)
            | (matrix_vector(left, (right >> 3) & 7) << 3)
            | (matrix_vector(left, (right >> 6) & 7) << 6))


def invertible(matrix):
    first, second, third = matrix & 7, (matrix >> 3) & 7, (matrix >> 6) & 7
    return (first != 0 and second not in (0, first)
            and third not in (0, first, second, first ^ second))


def matrix_rows(matrix):
    return [[(matrix >> (3 * column + row)) & 1 for column in range(3)]
            for row in range(3)]


def transvection(row, column):
    return IDENTITY ^ (1 << (3 * column + row))


def expanded_packet_words():
    """Symbolic words for independent vector-action replay and padding checks."""
    c, b1, b2, b3 = (1,), (2,), (3,), (4,)

    def inv(word):
        return tuple(-letter for letter in reversed(word))

    def bracket(left, right):
        return left + right + inv(left) + inv(right)

    def gamma(word):
        return c + word + inv(c)

    def gamma_squared(word):
        return inv(c) + word + c

    d = bracket(b2, gamma(b1))
    h = gamma_squared(d)
    a = bracket(d, h)
    e = gamma(d)
    j = a + e + inv(a)
    u = bracket(b2, gamma(b3))
    w = bracket(gamma_squared(b1), a)
    return (
        j + c + j + c,
        bracket(b3, gamma(b3)) + inv(d),
        bracket(u, w),
        bracket(bracket(b1, gamma(b2)), h)
        + bracket(bracket(b3, gamma(b1)), gamma_squared(u)) + inv(a),
        d + d,
    )


def direct_word_matrix(word, generators):
    """Replay a literal word right-to-left on the three coordinate vectors."""
    columns = []
    for column in range(3):
        value = 1 << column
        for token in reversed(word):
            value = matrix_vector(generators[token], value)
        columns.append(value)
    return columns[0] | (columns[1] << 3) | (columns[2] << 6)


def shared_packet(cycle, b, multiplication, inverses):
    """Operate on GL3(F2) table indices using the exact shared expressions."""
    mul = lambda left, right: multiplication[left][right]

    def bracket(left, right):
        return mul(mul(mul(left, right), inverses[left]), inverses[right])

    def gamma(word):
        return mul(mul(cycle, word), inverses[cycle])

    def gamma_squared(word):
        return mul(mul(inverses[cycle], word), cycle)

    b1, b2, b3 = b
    d = bracket(b2, gamma(b1))
    h = gamma_squared(d)
    a = bracket(d, h)
    e = gamma(d)
    j = mul(mul(a, e), inverses[a])
    u = bracket(b2, gamma(b3))
    w = bracket(gamma_squared(b1), a)
    return (
        mul(mul(mul(j, cycle), j), cycle),
        mul(bracket(b3, gamma(b3)), inverses[d]),
        bracket(u, w),
        mul(mul(bracket(bracket(b1, gamma(b2)), h),
                bracket(bracket(b3, gamma(b1)), gamma_squared(u))), inverses[a]),
        mul(d, d),
    )


def enumerate_packet(stats):
    matrices = tuple(value for value in range(512) if invertible(value))
    stats["invertible_matrix_count"] = len(matrices)
    if len(matrices) != 168:
        raise ArithmeticError("The binary matrix filter did not produce 168 elements")
    index = {value: position for position, value in enumerate(matrices)}
    identity = index[IDENTITY]
    multiplication = [[index[matrix_product(left, right)] for right in matrices]
                      for left in matrices]
    inverses = tuple(row.index(identity) for row in multiplication)
    if not all(multiplication[inverses[i]][i] == identity for i in range(168)):
        raise ArithmeticError("Left and right inverse table mismatch")
    cycles = tuple(i for i in range(168)
                   if i != identity and multiplication[multiplication[i][i]][i] == identity)
    stats["order_three_matrix_count"] = len(cycles)
    if len(cycles) != 56:
        raise ArithmeticError("Expected 56 nonidentity order-three elements")

    row_generators = transvection(0, 1), transvection(0, 2)
    column_generators = transvection(1, 0), transvection(2, 0)
    families = {
        "row_V4": (IDENTITY, *row_generators, matrix_product(*row_generators)),
        "column_V4": (IDENTITY, *column_generators, matrix_product(*column_generators)),
    }
    for name, family in families.items():
        if len(set(family)) != 4:
            raise ArithmeticError(f"{name} does not have four elements")
        if not all(matrix_product(value, value) == IDENTITY for value in family):
            raise ArithmeticError(f"{name} has a noninvolution")
        if not all(matrix_product(left, right) == matrix_product(right, left)
                   for left in family for right in family):
            raise ArithmeticError(f"{name} is not abelian")
    stats["families_matrix_integers"] = families
    stats["setup_checks_passed"] = True

    for cycle in cycles:
        for family_name, family_matrices in families.items():
            family = tuple(index[value] for value in family_matrices)
            for triple in itertools.product(family, repeat=3):
                rows = shared_packet(cycle, triple, multiplication, inverses)
                matches = tuple(value == identity for value in rows)
                stats["tuples_evaluated"] += 1
                stats["tuples_by_family"][family_name] += 1
                for row_name, match in zip(ROW_NAMES, matches):
                    stats["individual_relation_pass_counts"][row_name] += int(match)
                for count in range(1, len(ROW_NAMES) + 1):
                    stats["prefix_relation_pass_counts"][count - 1] += int(all(matches[:count]))
                if stats["tuples_evaluated"] > MAX_TUPLES:
                    raise ArithmeticError("Enumeration exceeded its fixed tuple bound")
                if all(matches):
                    generators = {1: matrices[cycle],
                                  **{i + 2: matrices[value] for i, value in enumerate(triple)}}
                    generators.update({-key: matrices[inverses[index[value]]]
                                       for key, value in tuple(generators.items())})
                    return {
                        "family": family_name,
                        "tuple_number": stats["tuples_evaluated"],
                        "generator_matrix_integers": {
                            "C": matrices[cycle],
                            **{f"B{i + 1}": matrices[value] for i, value in enumerate(triple)},
                        },
                        "shared_relation_matrix_integers": dict(zip(
                            ROW_NAMES, (matrices[value] for value in rows)
                        )),
                        "signed_generators_for_replay": generators,
                    }
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="New JSON output; an existing file is rejected")
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        parser.error("output must be new; there are no overwrites or restarts")

    started = time.monotonic()
    stats = {
        "invertible_matrix_count": None,
        "order_three_matrix_count": None,
        "setup_checks_passed": False,
        "tuples_evaluated": 0,
        "tuples_by_family": {"row_V4": 0, "column_V4": 0},
        "individual_relation_pass_counts": dict.fromkeys(ROW_NAMES, 0),
        "prefix_relation_pass_counts": [0] * len(ROW_NAMES),
    }
    witness = None
    stop_reason = "exhausted_requested_class"
    old_handler = signal.signal(signal.SIGALRM, expire_enumeration)
    try:
        signal.setitimer(signal.ITIMER_REAL, WALL_SECONDS)
        witness = enumerate_packet(stats)
        if witness is not None:
            stop_reason = "exact_model_found"
    except EnumerationBudgetExpired:
        stop_reason = "wall_budget"
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old_handler)
    enumeration_seconds = time.monotonic() - started

    words = expanded_packet_words()
    central_labels = []
    for word in words:
        label = 0
        for token in word:
            if abs(token) >= 2:
                label ^= 1 << (abs(token) - 2)
        central_labels.append(label)
    padding_checked = all(label == 0 for label in central_labels)
    replay_passed = None
    if witness is not None:
        generators = witness.pop("signed_generators_for_replay")
        replay = dict(zip(ROW_NAMES, (direct_word_matrix(word, generators) for word in words)))
        replay_passed = (replay == witness["shared_relation_matrix_integers"]
                         and all(value == IDENTITY for value in replay.values())
                         and generators[1] != IDENTITY
                         and matrix_product(matrix_product(generators[1], generators[1]),
                                            generators[1]) == IDENTITY)
        witness["direct_replay_relation_matrix_integers"] = replay
        witness["generator_rows"] = {
            name: matrix_rows(value) for name, value in witness["generator_matrix_integers"].items()
        }
        witness["relation_rows"] = {name: matrix_rows(value) for name, value in replay.items()}
    checks_passed = stats["setup_checks_passed"] and padding_checked and replay_passed is not False
    exact = witness is not None and checks_passed
    exhausted = stop_reason == "exhausted_requested_class" and stats["tuples_evaluated"] == MAX_TUPLES
    report = {
        "schema": "leavitt-packet-gl3f2-probe-v1",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "matrix_encoding": "bit(3*j+i)=entry(i,j), indices zero-based; products act on columns",
        "identity_matrix_integer": IDENTITY,
        "packet_order": ROW_NAMES,
        "word_lengths": dict(zip(ROW_NAMES, map(len, words))),
        "tuple_cap": MAX_TUPLES,
        "wall_budget_seconds": WALL_SECONDS,
        "stop_reason": stop_reason,
        "exhausted_requested_class": exhausted,
        "exact_model_found": exact,
        "stats": stats,
        "central_C2_cubed_padding": {
            "generator_rule": "c -> (C,0), b_i -> (B_i,e_i) in GL3(F2) x C2^3",
            "relation_labels": dict(zip(ROW_NAMES, central_labels)),
            "all_relation_labels_zero": padding_checked,
            "regular_representation_dimension": 1344,
            "regular_representation_k": 56,
            "justification": "C has order three; the independent central labels embed C2^3 "
                             "even when some B_i=I. Left regular restrictions have the required "
                             "regular multiplicities. Every tested word has zero central label.",
        },
        "witness": witness,
        "direct_replay_passed": replay_passed,
        "checks_passed": checks_passed,
        "scope": (
            "Exact augmented-packet model; central padding gives a frozen-factor model at "
            "k=56, so these five relations cannot give a uniform 24k gap. This does not "
            "model the full Leavitt group."
            if exact else
            "No verified exact model found in the tested GL3(F2), row/column V4 tuples. "
            "This conclusion is limited to the completed tuples, and gives no general "
            "finite-model exclusion or normalized-HS gap evidence."
        ),
        "timing": {
            "enumeration_seconds_including_tables": enumeration_seconds,
            "timer_delivery_overrun_seconds": max(0.0, enumeration_seconds - WALL_SECONDS),
            "total_seconds_through_replay": time.monotonic() - started,
            "timer_scope": "Matrix filtering, tables, and tuple enumeration; final bounded "
                           "literal replay and JSON serialization are excluded.",
        },
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x") as handle:
        json.dump(report, handle, indent=2, allow_nan=False)
        handle.write("\n")
    print(json.dumps({"output": str(output), "stop_reason": stop_reason,
                      "tuples_evaluated": stats["tuples_evaluated"],
                      "exact_model_found": exact, "checks_passed": checks_passed,
                      "enumeration_seconds": enumeration_seconds}, allow_nan=False))
    return 0 if checks_passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
