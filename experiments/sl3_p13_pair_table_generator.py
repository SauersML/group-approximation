"""Emit a sparse, exhaustively checked P13 support-pair partition.

The explicit fibers are a performance representation of the existing replay
table, not new certificate data.  The generated Lean module checks soundness
on each short fiber and completeness on each of the 484 input pairs with
ordinary kernel reduction.  The generic fiber identity is then proved from
those two facts, without reducing a 484-element filter in one proof.

Run this generator on MSI, not on a local workstation.
"""

import argparse
import hashlib
import json
from pathlib import Path


EXPECTED_REPLAY_SHA256 = (
    "66255b59016bdeefd1fddd5de5069e5c32810543039f31da3930f43ce7cb5916"
)


def emit_pair(pair):
    return "(%d, %d)" % pair


def emit_fiber_table(fibers, out, chunk_size=8):
    """Emit bounded exact tables with a single proved final-chunk split."""
    full_size = (len(fibers) // chunk_size) * chunk_size
    full_chunks = [fibers[offset:offset + chunk_size]
                   for offset in range(0, full_size, chunk_size)]
    final_chunk = fibers[full_size:]
    out.extend([
        "/-- Read an exact finite table; the length proof rules out defaults. -/\n",
        "private def exactTable {A : Type*} {n : ℕ} (entries : List A)\n",
        "    (h : entries.length = n) : Fin n → A :=\n",
        "  fun i ↦ entries.get (h ▸ i)\n\n",
    ])
    for chunk_index, chunk in enumerate(full_chunks):
        out.append("private def classPairListChunk%d : Fin %d → " %
                   (chunk_index, chunk_size))
        out.append("List (Fin 22 × Fin 22) := exactTable [\n")
        for fiber in chunk:
            out.append("  [%s],\n" % ", ".join(map(emit_pair, fiber)))
        out.append("] (by decide)\n\n")
    out.append("private def classPairListChunks : Fin %d → Fin %d → " %
               (len(full_chunks), chunk_size))
    out.append("List (Fin 22 × Fin 22) := exactTable [\n")
    for chunk_index in range(len(full_chunks)):
        out.append("  classPairListChunk%d,\n" % chunk_index)
    out.append("] (by decide)\n\n")
    out.append("private def classPairListFinal : Fin %d → " % len(final_chunk))
    out.append("List (Fin 22 × Fin 22) := exactTable [\n")
    for fiber in final_chunk:
        out.append("  [%s],\n" % ", ".join(map(emit_pair, fiber)))
    out.append("] (by decide)\n\n")
    out.extend([
        "/-- Sparse support-pair list for one coefficient class. -/\n",
        "def classPairList (c : Fin 293) : List (Fin 22 × Fin 22) :=\n",
        "  if h : c.1 < %d then\n" % full_size,
        "    classPairListChunks ⟨c.1 / %d, by lia⟩ " % chunk_size,
        "⟨c.1 %% %d, Nat.mod_lt _ (by lia)⟩\n" % chunk_size,
        "  else\n",
        "    classPairListFinal ⟨c.1 - %d, by lia⟩\n\n" % full_size,
    ])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    digest = hashlib.sha256(args.replay.read_bytes()).hexdigest()
    if digest != EXPECTED_REPLAY_SHA256:
        raise ValueError("replay SHA-256 mismatch: %s" % digest)
    data = json.loads(args.replay.read_text())
    table = data["product_class_table"]
    if len(table) != 22 or any(len(row) != 22 for row in table):
        raise ValueError("product table must be exactly 22 x 22")
    fibers = [[] for _ in range(293)]
    for left, row in enumerate(table):
        for right, coefficient_class in enumerate(row):
            fibers[coefficient_class].append((left, right))
    if sum(map(len, fibers)) != 484 or any(not fiber for fiber in fibers):
        raise ValueError("the 293 fibers must partition all 484 pairs")

    out = [
        "import GroupApproximation.Sofic.LiteralP13HodgeReplay\n\n",
        "/-!\n# Sparse support-pair fibers for the exact P13 certificate\n\n",
        "The explicit list is only a fast representation of the replayed\n",
        "product-class table.  Each fiber is proved equal to the definitional\n",
        "filter below, so no generated equality is trusted.\n-/\n\n",
        "namespace GroupApproximation\n",
        "namespace LiteralP13HodgePairTable\n\n",
        "open LiteralP13HodgeReplay\n",
        "open scoped BigOperators\n\n",
    ]
    emit_fiber_table(fibers, out)
    out.extend([
        "/-- Finset form of the sparse fiber. -/\n",
        "def classPairs (c : Fin 293) : Finset (Fin 22 × Fin 22) :=\n",
        "  (classPairList c).toFinset\n\n",
    ])
    # One short soundness check per fiber.  `List.Forall` unfolds over only the
    # one-to-eight stored pairs; a decidable `∀ pair : Fin 22 × Fin 22` would
    # instead enumerate all 484 pairs even under an implication.
    for index in range(293):
        out.extend([
            "/-- Every pair stored in sparse fiber %d has class %d. -/\n" %
            (index, index),
            "private theorem classPairList_sound_%d :\n" % index,
            "    (classPairList %d).Forall\n" % index,
            "      (fun pair ↦ productClassIndex pair.1 pair.2 = %d) := by\n" % index,
            "  decide\n\n",
        ])
    # Dispatch in bounded blocks so the proof term never contains a 293-deep
    # case split.  The interval hypotheses make every block exhaustive.
    dispatch_size = 32
    for lower in range(0, 293, dispatch_size):
        upper = min(lower + dispatch_size, 293)
        out.extend([
            "private theorem classPairList_sound_%d_%d (c : Fin 293)\n" %
            (lower, upper),
            "    (hlo : %d ≤ c.1) (hhi : c.1 < %d) :\n" % (lower, upper),
            "    (classPairList c).Forall\n",
            "      (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by\n",
        ])
        for index in range(lower, upper - 1):
            out.extend([
                "  by_cases h%d : c.1 = %d\n" % (index, index),
                "  · have hc : c = (%d : Fin 293) := Fin.ext h%d\n" %
                (index, index),
                "    subst c\n",
                "    exact classPairList_sound_%d\n" % index,
            ])
        last = upper - 1
        out.extend([
            "  have hc : c = (%d : Fin 293) := Fin.ext (by lia)\n" % last,
            "  subst c\n",
            "  exact classPairList_sound_%d\n" % last,
        ])
        out.append("\n")
    out.extend([
        "private theorem classPairList_sound (c : Fin 293) :\n",
        "    (classPairList c).Forall\n",
        "      (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by\n",
    ])
    for lower in range(0, 288, dispatch_size):
        upper = lower + dispatch_size
        out.extend([
            "  by_cases h%d : c.1 < %d\n" % (lower, upper),
            "  · exact classPairList_sound_%d_%d c (by lia) h%d\n" %
            (lower, upper, lower),
        ])
    out.extend([
        "  exact classPairList_sound_288_293 c (by lia) (by lia)\n\n",
        "/-- Every pair stored in a sparse fiber has that fiber's class. -/\n",
        "theorem classPairs_sound (c : Fin 293) (pair : Fin 22 × Fin 22)\n",
        "    (hpair : pair ∈ classPairs c) :\n",
        "    productClassIndex pair.1 pair.2 = c := by\n",
        "  have hlist : pair ∈ classPairList c := by\n",
        "    simpa [classPairs] using hpair\n",
        "  exact (List.forall_iff_forall_mem.mp (classPairList_sound c)) pair hlist\n\n",
    ])

    # Completeness is split by the left support coordinate.  Each theorem has
    # only 22 small branches, which remains below Lean's default recursion and
    # heartbeat budgets.
    for left in range(22):
        out.extend([
            "/-- Every pair with left coordinate %d occurs in its class fiber. -/\n" % left,
            "private theorem classPairs_complete_left_%d (right : Fin 22) :\n" % left,
            "    (%d, right) ∈ classPairs (productClassIndex %d right) := by\n" %
            (left, left),
            "  fin_cases right <;> decide\n\n",
        ])
    out.extend([
        "/-- Every support pair occurs in the sparse fiber selected by the replay table. -/\n",
        "theorem classPairs_complete (left right : Fin 22) :\n",
        "    (left, right) ∈ classPairs (productClassIndex left right) := by\n",
        "  fin_cases left\n",
    ])
    for left in range(22):
        out.append("  · exact classPairs_complete_left_%d right\n" % left)
    out.extend([
        "\n/-- Every sparse fiber is exactly the corresponding replay-table fiber. -/\n",
        "theorem classPairs_eq_filter (c : Fin 293) :\n",
        "    classPairs c =\n",
        "      (Finset.univ : Finset (Fin 22 × Fin 22)).filter\n",
        "        (fun pair ↦ productClassIndex pair.1 pair.2 = c) := by\n",
        "  ext pair\n",
        "  constructor\n",
        "  · intro hpair\n",
        "    simpa using classPairs_sound c pair hpair\n",
        "  · intro hpair\n",
        "    have hclass : productClassIndex pair.1 pair.2 = c := by\n",
        "      simpa using hpair\n",
        "    simpa [hclass] using classPairs_complete pair.1 pair.2\n",
    ])
    out.extend([
        "\n/-- Reindex a collected convolution by its sparse fiber. -/\n",
        "theorem convolution_eq_classPairs\n",
        "    {R : Type*} [CommRing R]\n",
        "    (left right : Fin 22 → R) (c : Fin 293) :\n",
        "    (∑ a, ∑ b, if productClassIndex a b = c then\n",
        "        left a * right b else 0) =\n",
        "      ∑ pair ∈ classPairs c, left pair.1 * right pair.2 := by\n",
        "  classical\n",
        "  calc\n",
        "    (∑ a, ∑ b, if productClassIndex a b = c then\n",
        "        left a * right b else 0) =\n",
        "        ∑ pair : Fin 22 × Fin 22,\n",
        "          if productClassIndex pair.1 pair.2 = c then\n",
        "            left pair.1 * right pair.2 else 0 := by\n",
        "      rw [Fintype.sum_prod_type]\n",
        "    _ = ∑ pair ∈ classPairs c, left pair.1 * right pair.2 := by\n",
        "      rw [classPairs_eq_filter, Finset.sum_filter]\n\n",
        "/-- Integer specialization used by exact numerator computations. -/\n",
        "theorem integerConvolution_eq_classPairs\n",
        "    (left right : Fin 22 → ℤ) (c : Fin 293) :\n",
        "    (∑ a, ∑ b, if productClassIndex a b = c then\n",
        "        left a * right b else 0) =\n",
        "      ∑ pair ∈ classPairs c, left pair.1 * right pair.2 :=\n",
        "  convolution_eq_classPairs left right c\n\n",
        "end LiteralP13HodgePairTable\n",
        "end GroupApproximation\n",
    ])
    args.output.write_text("".join(out))
    print("wrote 484 pairs in 293 exact fibers to", args.output)


if __name__ == "__main__":
    main()
