"""Emit literal Lean tables for the exact P13 Hodge certificate.

This generator is deliberately not a verifier.  It checks the immutable NPZ
hash and dimensions, then prints every stored integer as source text.  The
resulting Lean certificate must independently prove all group-ring identities
using abstract P13 relator replay; neither the NPZ's metadata nor the matrix
model is a trusted premise.

Run this only on MSI.  The dense factor has no useful exact orbit or block
symmetry, so the honest representation is a finite three-index integer table
`row x root x support = 102 x 6 x 22`.
"""

import argparse
import hashlib
from pathlib import Path

import numpy as np


EXPECTED_SHA256 = (
    "5b83dc59e55b89a8f48e115e06ce72deaac2bccd5c3f1ded1ead3837c26b021b"
)
EXPECTED_FACTOR_SHAPE = (102, 132)
ROOTS = 6
SUPPORT = 22


def load_factor(path):
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != EXPECTED_SHA256:
        raise ValueError("certificate SHA-256 mismatch: %s" % digest)
    archive = np.load(path)
    factor = archive["factor_numerators"]
    if factor.shape != EXPECTED_FACTOR_SHAPE:
        raise ValueError("unexpected factor shape: %r" % (factor.shape,))
    if factor.dtype != np.dtype("int64"):
        raise ValueError("unexpected factor dtype: %s" % factor.dtype)
    if factor.shape[1] != ROOTS * SUPPORT:
        raise AssertionError("root/support factorization is inconsistent")
    return factor


def lean_integer(value):
    value = int(value)
    return str(value) if value >= 0 else "(%d)" % value


def emit_factor(factor, output):
    for row in range(factor.shape[0]):
        output.write(
            "/-- Numerator row %d of the exact Gram factor. -/\n" % row
        )
        output.write(
            "def qNumeratorRow%d : Fin 6 → Fin 22 → ℤ\n" % row
        )
        for root in range(ROOTS):
            entries = factor[row, root * SUPPORT:(root + 1) * SUPPORT]
            literal = ", ".join(lean_integer(value) for value in entries)
            output.write(
                "  | %d => integerBlock [%s] (by decide)\n"
                % (root, literal)
            )
        output.write("\n")
    output.write(
        "/-- Bounded exact tables for the first 96 Gram-factor rows. -/\n"
    )
    for chunk in range(12):
        first = 8 * chunk
        rows = ", ".join(
            "qNumeratorRow%d" % row for row in range(first, first + 8))
        output.write(
            "private def qNumeratorChunk%d : Fin 8 → Fin 6 → Fin 22 → ℤ :=\n"
            "  finiteTable [%s] (by decide)\n" % (chunk, rows)
        )
    output.write(
        "private def qNumeratorFinal : Fin 6 → Fin 6 → Fin 22 → ℤ :=\n"
        "  finiteTable [%s] (by decide)\n\n" % ", ".join(
            "qNumeratorRow%d" % row for row in range(96, 102))
    )
    output.write(
        "/-- Bounded-depth access to every exact Gram-factor row. -/\n"
        "def qNumerator (row : Fin 102) : Fin 6 → Fin 22 → ℤ :=\n"
    )
    for chunk in range(12):
        upper = 8 * (chunk + 1)
        lower = 8 * chunk
        index = "row.1" if chunk == 0 else "row.1 - %d" % lower
        output.write(
            "  if h%d : row.1 < %d then qNumeratorChunk%d "
            "⟨%s, by lia⟩ else\n" % (chunk, upper, chunk, index)
        )
    output.write("  qNumeratorFinal ⟨row.1 - 96, by lia⟩\n")
    output.write("\n")
    output.write("/-- The exact rational Gram factor `Q_Z / 10^8`. -/\n")
    output.write(
        "def q : Fin 102 → Fin 6 → RatGroupRing P13 :=\n"
    )
    output.write("  fun row root ↦ ∑ supportIndex : Fin 22,\n")
    output.write("    monomial (support supportIndex)\n")
    output.write(
        "      ((qNumerator row root supportIndex : ℚ) / qDenominator)\n"
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    factor = load_factor(args.certificate)
    with args.output.open("w") as output:
        emit_factor(factor, output)
    print("wrote %s bytes to %s" % (args.output.stat().st_size, args.output))


if __name__ == "__main__":
    main()
