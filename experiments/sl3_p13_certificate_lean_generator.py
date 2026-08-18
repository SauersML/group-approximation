"""Generate the kernel-checked P13 residual proof family.

The generated numerals are only expected results.  Every eight-class chunk is
recomputed by Lean from the public exact definitions of ``D``, ``B``, and
``q`` with ordinary kernel reduction.  No residual coefficient table is
emitted, and no generated equality is trusted.

Run this generator on MSI.  It verifies the pinned discovery artifacts before
writing the canonical Lean modules.
"""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

import numpy as np


EXPECTED_CERTIFICATE_SHA256 = (
    "5b83dc59e55b89a8f48e115e06ce72deaac2bccd5c3f1ded1ead3837c26b021b"
)
EXPECTED_REPLAY_SHA256 = (
    "66255b59016bdeefd1fddd5de5069e5c32810543039f31da3930f43ce7cb5916"
)
COMMON_DENOMINATOR = 10**16
GAP_SCALED = 4 * 10**13
IDENTITY_CLASS = 201
ROOTS = 6
RELATORS = 13
ROWS = 102
SUPPORT = 22
CLASSES = 293


def checked_bytes(path, expected):
    payload = path.read_bytes()
    digest = hashlib.sha256(payload).hexdigest()
    if digest != expected:
        raise ValueError("SHA-256 mismatch for %s: %s" % (path, digest))
    return payload


def load_helper(path):
    specification = importlib.util.spec_from_file_location(
        "sl3_p13_relator_replay", path)
    helper = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(helper)
    return helper


def exact_residual(certificate_path, replay_path, helper_path):
    checked_bytes(certificate_path, EXPECTED_CERTIFICATE_SHA256)
    replay = json.loads(
        checked_bytes(replay_path, EXPECTED_REPLAY_SHA256).decode("utf-8"))
    table = replay["product_class_table"]
    if len(table) != SUPPORT or any(len(row) != SUPPORT for row in table):
        raise ValueError("product-class table is not 22 x 22")
    if len(replay["product_class_words"]) != CLASSES:
        raise ValueError("expected exactly 293 product classes")
    if replay["product_class_words"][IDENTITY_CLASS] != []:
        raise ValueError("product class 201 is not the identity word")

    helper = load_helper(helper_path)
    support_words, class_words, helper_table, _targets = \
        helper.support_and_targets(certificate_path)
    if [list(word) for word in support_words] != replay["support_words"]:
        raise ValueError("NPZ support order disagrees with the replay artifact")
    if [list(word) for word in class_words] != replay["product_class_words"]:
        raise ValueError("NPZ product classes disagree with the replay artifact")
    if helper_table != table:
        raise ValueError("NPZ product table disagrees with the replay artifact")
    boundary = helper.canonical_boundary(certificate_path)
    if (len(boundary) != RELATORS or
            any(len(row) != ROOTS for row in boundary) or
            any(len(entry) != SUPPORT for row in boundary for entry in row)):
        raise ValueError("canonical Fox tensor has the wrong shape")

    archive = np.load(certificate_path)
    factor = archive["factor_numerators"]
    if factor.shape != (ROWS, ROOTS * SUPPORT):
        raise ValueError("Gram factor has the wrong shape")
    if int(archive["factor_denominator"][0]) != 10**8:
        raise ValueError("Gram denominator is not 10^8")
    q = factor.astype(object).reshape(ROWS, ROOTS, SUPPORT)

    fibers = [[] for _ in range(CLASSES)]
    for left in range(SUPPORT):
        for right in range(SUPPORT):
            fibers[int(table[left][right])].append((left, right))
    if sum(map(len, fibers)) != SUPPORT * SUPPORT or any(not x for x in fibers):
        raise ValueError("product fibers do not partition the 484 pairs")

    adjoint_d = [[0] * SUPPORT for _ in range(ROOTS)]
    for root in range(ROOTS):
        adjoint_d[root][6 + root] = 1
        adjoint_d[root][12] = -1

    residual = [[[0] * CLASSES for _ in range(ROOTS)]
                for _ in range(ROOTS)]
    for i in range(ROOTS):
        for k in range(ROOTS):
            for coefficient_class, pairs in enumerate(fibers):
                hodge = 0
                gram = 0
                for left, right in pairs:
                    hodge += sum(
                        int(boundary[relator][i][left]) *
                        int(boundary[relator][k][right])
                        for relator in range(RELATORS))
                    hodge += adjoint_d[i][left] * adjoint_d[k][right]
                    gram += sum(
                        int(q[row, i, left]) * int(q[row, k, right])
                        for row in range(ROWS))
                scalar = (GAP_SCALED if
                          i == k and coefficient_class == IDENTITY_CLASS else 0)
                residual[i][k][coefficient_class] = (
                    hodge * COMMON_DENOMINATOR - scalar - gram)
    return residual


def chunks(values):
    initial = [sum(abs(value) for value in values[8 * j:8 * j + 8])
               for j in range(36)]
    final = sum(abs(value) for value in values[288:293])
    return initial, final


def vector(values):
    return "![%s]" % ", ".join(str(value) for value in values)


def module_header(core_module, i, k, first, last):
    return (
        "import GroupApproximation.Sofic.%s\n" % core_module +
        "import GroupApproximation.Meta.BatchedKernelChecks\n\n" +
        "namespace GroupApproximation\n" +
        "namespace LiteralP13HodgeCertificate\n\n" +
        "/-! Batched kernel checks %d--%d for residual block (%d, %d). -/\n\n"
        % (first, last, i, k))


MODULE_END = "\nend LiteralP13HodgeCertificate\nend GroupApproximation\n"


def emit_part(output, core_module, residual, i, k, part):
    initial, final = chunks(residual[i][k])
    first = 9 * part
    namespace = "Residual%d%dPart%d" % (i, k, part)
    expected = initial[first:first + 9]
    out = [module_header(core_module, i, k, first, first + 8)]
    out.extend([
        "namespace %s\n\n" % namespace,
        "/-- Expected chunk totals; these numerals are data, not trusted equalities. -/\n",
        "def expected : Fin 9 → Nat := %s\n\n" % vector(expected),
        "/-- One independently kernel-checked chunk equality. -/\n",
        "def check (u : Fin 9) : Prop :=\n",
        "  initialChunk %d %d (finProdFinEquiv ((%d : Fin 4), u)) = expected u\n\n"
        % (i, k, part),
    ])

    if part == 2:
        coefficient_values = [
            abs(residual[i][k][coefficient_class])
            for coefficient_class in range(200, 208)
        ]
        out.extend([
            "/-- The identity-containing chunk is split into eight coefficient checks. -/\n",
            "def chunk25Expected : Fin 8 → Nat := %s\n\n" % vector(coefficient_values),
            "def chunk25Check (u : Fin 8) : Prop :=\n",
            "  (residualNumerator %d %d\n" % (i, k),
            "    (Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), u)))).natAbs =\n",
            "      chunk25Expected u\n\n",
            "mk_kernel_batched_theorem 8 chunk25Check\n\n",
            "theorem chunk25All : ∀ u : Fin 8, chunk25Check u :=\n",
            "  combine_kernel_batched_theorems% chunk25Check 8\n\n",
            "theorem chunk25 : initialChunk %d %d 25 = %d := by\n" %
            (i, k, initial[25]),
            "  unfold initialChunk\n",
            "  calc\n",
            "    ∑ u : Fin 8,\n",
            "        (residualNumerator %d %d\n" % (i, k),
            "          (Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), u)))).natAbs =\n",
            "        ∑ u : Fin 8, chunk25Expected u := by\n",
            "      apply Finset.sum_congr rfl\n",
            "      intro u _\n",
            "      exact chunk25All u\n",
            "    _ = %d := by decide +kernel\n\n" % initial[25],
            "mk_kernel_batched_theorem_except 9 7 check\n\n",
            "theorem check.case_7 : check 7 := by\n",
            "  simpa [check, expected] using chunk25\n\n",
        ])
    else:
        out.append("mk_kernel_batched_theorem 9 check\n\n")

    out.extend([
        "theorem all : ∀ u : Fin 9, check u :=\n",
        "  combine_kernel_batched_theorems% check 9\n\n",
    ])
    if part == 3:
        out.extend([
            "theorem final : finalChunk %d %d = %d := by\n" % (i, k, final),
            "  decide +kernel\n\n",
        ])
    out.append("end %s\n\n" % namespace)

    subtotal = sum(expected) + (final if part == 3 else 0)
    lhs = "initialPart %d %d %d" % (i, k, part)
    if part == 3:
        lhs += " + finalChunk %d %d" % (i, k)
    out.extend([
        "/-- Exact subtotal for this independently checked residual part. -/\n",
        "theorem residual_part_sum_%d_%d_%d : %s = %d := by\n" %
        (i, k, part, lhs, subtotal),
        "  have hpart : initialPart %d %d %d =\n" % (i, k, part),
        "      ∑ u : Fin 9, %s.expected u := by\n" % namespace,
        "    unfold initialPart\n",
        "    apply Finset.sum_congr rfl\n",
        "    intro u _\n",
        "    exact %s.all u\n" % namespace,
    ])
    if part == 3:
        out.extend([
            "  rw [hpart, %s.final]\n" % namespace,
            "  decide +kernel\n",
        ])
    else:
        out.extend([
            "  rw [hpart]\n",
            "  decide +kernel\n",
        ])
    out.append(MODULE_END)
    output.write_text("".join(out))

def emit_block(output, module_prefix, residual, i, k):
    total = sum(abs(value) for value in residual[i][k])
    imports = "".join(
        "import GroupApproximation.Sofic.%s%d%dPart%d\n" %
        (module_prefix, i, k, part) for part in range(4))
    names = [
        "residual_part_sum_%d_%d_%d" % (i, k, part)
        for part in range(4)]
    output.write_text(
        imports +
        "import GroupApproximation.Sofic.LiteralP13HodgeResidualComposition\n" +
        "\nnamespace GroupApproximation\n" +
        "namespace LiteralP13HodgeCertificate\n\n" +
        "theorem residual_block_natAbs_%d_%d :\n" % (i, k) +
        "    ∑ c : Fin 293, (residualNumerator %d %d c).natAbs = %d := by\n"
        % (i, k, total) +
        "  refine (sum_natAbs_eq_of_part_sums %d %d\n" % (i, k) +
        "    %s %s\n" % (names[0], names[1]) +
        "    %s %s).trans ?_\n" % (names[2], names[3]) +
        "  norm_num\n" + MODULE_END)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--replay", type=Path, required=True)
    parser.add_argument("--helper", type=Path, required=True)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--core-module", default="LiteralP13HodgeCertificateCore")
    parser.add_argument("--residual-prefix", default="LiteralP13HodgeResidual")
    args = parser.parse_args()
    residual = exact_residual(args.certificate, args.replay, args.helper)
    args.output_directory.mkdir(parents=True, exist_ok=True)

    for i in range(ROOTS):
        for k in range(ROOTS):
            for part in range(4):
                emit_part(
                    args.output_directory /
                    ("%s%d%dPart%d.lean" %
                     (args.residual_prefix, i, k, part)),
                    args.core_module, residual, i, k, part)
            emit_block(
                args.output_directory /
                ("%s%d%d.lean" % (args.residual_prefix, i, k)),
                args.residual_prefix, residual, i, k)

    imports = "".join(
        "import GroupApproximation.Sofic.%s%d%d\n" %
        (args.residual_prefix, i, k)
        for i in range(ROOTS) for k in range(ROOTS))
    (args.output_directory / (args.residual_prefix + ".lean")).write_text(
        imports +
        "\n/-! Aggregator for the 36 independently checked exact residual blocks. -/\n")

    row_sums = [sum(abs(value) for block in residual[i] for value in block)
                for i in range(ROOTS)]
    column_sums = [sum(abs(residual[i][k][c])
                       for i in range(ROOTS) for c in range(CLASSES))
                   for k in range(ROOTS)]
    if row_sums != column_sums or max(row_sums) != 11670886519714:
        raise ValueError("unexpected residual row/column bounds")
    print("wrote 144 direct parts, 36 blocks, and one aggregator")


if __name__ == "__main__":
    main()
