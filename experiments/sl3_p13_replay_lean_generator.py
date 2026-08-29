"""Emit kernel-checkable Lean replay data for the exact P13 certificate.

The input JSON is not trusted: before emitting anything, this generator
reconstructs the thirteen literal relators and independently free-reduces the
product of every conjugated signed-relator proof.  The generated Lean module
then repeats precisely that check with `by decide` in Mathlib's free group.

Run this generator on MSI, not on a local workstation.
"""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path


EXPECTED_REPLAY_SHA256 = (
    "66255b59016bdeefd1fddd5de5069e5c32810543039f31da3930f43ce7cb5916"
)

UNUSED_REDUCTIONS = frozenset({54, 56, 60, 63, 64, 65, 70, 71, 72, 80, 83, 84})
UNUSED_PREFIX_REPLAYS = frozenset({
    26, 28, 30, 33, 34, 35, 38, 39, 40, 54, 55, 56, 60, 61,
    63, 64, 65, 69, 70, 71, 72, 74, 76, 80, 82, 83, 84, 139,
})


def load_replay_helpers(path):
    specification = importlib.util.spec_from_file_location(
        "sl3_p13_relator_replay", path)
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


def lean_letter(letter):
    return "(%d, %s)" % (
        abs(int(letter)) - 1, "true" if int(letter) > 0 else "false")


def lean_word(word):
    return "[" + ", ".join(lean_letter(letter) for letter in word) + "]"


def lean_group_value(word):
    """Render the right-associated group product computed by `wordValue`."""
    if not word:
        return "1"

    def generator_value(letter):
        generator = "p13Generator %d" % (abs(int(letter)) - 1)
        if int(letter) < 0:
            generator = "(%s)⁻¹" % generator
        return generator

    value = generator_value(word[-1])
    for letter in reversed(word[:-1]):
        value = "%s * (%s)" % (generator_value(letter), value)
    return value


def lean_atom(atom):
    return ("{ conjugator := %s, relatorIndex := %d, inverted := %s }" %
            (lean_word(atom["conjugator"]), int(atom["relator_index"]),
             "true" if atom["inverted"] else "false"))


def exact_table(name, values, value_type, emit_value, output,
                chunk_size=8):
    """Emit bounded exact list tables, with no default value or deep list."""
    if not values:
        raise ValueError("exact tables must be nonempty")
    full_size = ((len(values) - 1) // chunk_size) * chunk_size
    chunks = [values[offset:offset + chunk_size]
              for offset in range(0, full_size, chunk_size)]
    final_chunk = values[full_size:]
    for chunk_index, chunk in enumerate(chunks):
        output.write("private def %sChunk%d : Fin %d → %s :=\n" %
                     (name, chunk_index, chunk_size, value_type))
        output.write("  fun i ↦ ([%s] : List (%s)).get i\n\n" %
                     (", ".join(emit_value(value) for value in chunk),
                      value_type))
    output.write("private def %sFinal : Fin %d → %s :=\n" %
                 (name, len(final_chunk), value_type))
    output.write("  fun i ↦ ([%s] : List (%s)).get i\n\n" %
                 (", ".join(emit_value(value) for value in final_chunk),
                  value_type))
    output.write("def %s (i : Fin %d) : %s :=\n" %
                 (name, len(values), value_type))
    for chunk_index in range(len(chunks)):
        lower = chunk_index * chunk_size
        upper = lower + chunk_size
        output.write("  if h%d : i.1 < %d then %sChunk%d " %
                     (chunk_index, upper, name, chunk_index))
        index = "i.1" if lower == 0 else "i.1 - %d" % lower
        output.write("⟨%s, by omega⟩ else\n" % index)
    output.write("  %sFinal ⟨i.1 - %d, by omega⟩\n" %
                 (name, full_size))


def emit_product_class_table(table, output):
    for row, values in enumerate(table):
        exact_table("productClassIndexRow%d" % row, values, "Fin 293",
                    str, output)
        output.write("\n")
    exact_table("productClassIndex",
                ["productClassIndexRow%d" % row for row in range(len(table))],
                "Fin 22 → Fin 293", str, output)
    output.write("\n")


def emit_prod_is_one(names, output):
    """Close a mapped finite product using already proved factor theorems."""
    theorem_names = ", ".join(name + "_eq_one" for name in names)
    if len(names) == 1:
        output.write(
            "  simpa only [List.prod_cons, List.prod_nil, mul_one] using %s\n\n"
            % theorem_names)
    else:
        output.write(
            "  simp only [List.prod_cons, List.prod_nil, mul_one, map_mul, "
            "%s]\n\n" % theorem_names)


def validate(data, helper):
    if data.get("format") != "P13 conjugated-relator replay v1":
        raise ValueError("unrecognized replay format")
    if len(data["reductions"]) != 144:
        raise ValueError("expected all 144 replay reductions")
    if [item["target_index"] for item in data["reductions"]] != list(
            range(144)):
        raise ValueError("replay targets are missing or out of order")
    relators = helper.presentation_relators()
    total_atoms = 0
    maximum_atoms = 0
    for reduction in data["reductions"]:
        atoms = tuple((tuple(atom["conjugator"]),
                       int(atom["relator_index"]), bool(atom["inverted"]))
                      for atom in reduction["atoms"])
        left = tuple(reduction["left"])
        right = tuple(reduction["right"])
        if helper.atoms_word(atoms, relators) != helper.multiply(
                left, helper.inverse_word(right)):
            raise ValueError("free replay failed at target %d" %
                             reduction["target_index"])
        total_atoms += len(atoms)
        maximum_atoms = max(maximum_atoms, len(atoms))
    if total_atoms != data["proof_atoms"] or \
            maximum_atoms != data["maximum_atoms_per_reduction"]:
        raise ValueError("replay atom metadata mismatch")


def emit(data, helper, certificate, output):
    output.write(
        "import GroupApproximation.Kazhdan.FoxBoundary\n"
        "import GroupApproximation.Sofic.LiteralP13Presentation\n\n"
        "/-!\n"
        "# Exact relator replays for the P13 Hodge certificate\n\n"
        "Every theorem below is checked solely in the free group as a finite\n"
        "product of conjugates of the thirteen abstract P13 relators.  The\n"
        "discovery matrix model and the replay-search program are not trusted\n"
        "inputs.  The source JSON has SHA-256\n"
        "`%s`; Lean independently checks every emitted proof with `decide`.\n"
        "-/\n\n" % EXPECTED_REPLAY_SHA256)
    output.write(
        "namespace GroupApproximation\n"
        "namespace LiteralP13HodgeReplay\n\n"
        "open LiteralP13Presentation PresentedGroupRelatorReplay\n"
        "open FoxBoundary\n\n"
        "noncomputable section\n\n"
        "/-- Evaluation of a literal free word agrees with signed-word "
        "evaluation. -/\n"
        "@[simp] theorem p13Word_word_eq_wordValue "
        "(letters : SignedWord P13Generator) :\n"
        "    p13Word (word letters) = wordValue p13Generator letters := by\n"
        "  change p13Word (word letters) =\n"
        "    wordValue (fun i ↦ p13Word (FreeGroup.of i)) letters\n"
        "  exact (wordValue_freeGroup_map p13Word letters).symm\n\n")
    exact_table("supportFreeWord", data["support_words"],
                "FreeGroup P13Generator",
                lambda value: "word " + lean_word(value), output)
    output.write("\n")
    for index, value in enumerate(data["support_words"]):
        output.write(
            "@[simp] theorem supportFreeWord_eq_%d :\n"
            "    supportFreeWord (%d : Fin 22) = word %s := by decide\n\n" %
            (index, index, lean_word(value)))
    exact_table("productClassFreeWord", data["product_class_words"],
                "FreeGroup P13Generator",
                lambda value: "word " + lean_word(value), output)
    output.write("\n")
    emit_product_class_table(data["product_class_table"], output)
    relators = helper.presentation_relators()
    chunk_size = 12
    for reduction in data["reductions"]:
        index = reduction["target_index"]
        if index in UNUSED_REDUCTIONS:
            continue
        output.write(
            "/-- Checked P13 coefficient merge %d (`%s`). -/\n" %
            (index, reduction["kind"]))
        chunk_names = []
        chunk_words = []
        atoms = reduction["atoms"]
        for chunk_index, offset in enumerate(range(0, len(atoms), chunk_size)):
            chunk = atoms[offset:offset + chunk_size]
            chunk_atoms = tuple(
                (tuple(atom["conjugator"]), int(atom["relator_index"]),
                 bool(atom["inverted"])) for atom in chunk)
            chunk_word = helper.atoms_word(chunk_atoms, relators)
            chunk_name = "reduction%dChunk%d" % (index, chunk_index)
            chunk_names.append(chunk_name)
            chunk_words.append(chunk_word)
            output.write(
                "def %sAtoms : List (Atom P13Generator (Fin 13)) :=\n"
                "  [%s]\n\n" %
                (chunk_name, ",\n    ".join(lean_atom(atom)
                                               for atom in chunk)))
            output.write(
                "def %sWord : FreeGroup P13Generator :=\n"
                "  word %s\n\n" % (chunk_name, lean_word(chunk_word)))
            output.write(
                "theorem %s_eq_one : p13Word %sWord = 1 := by\n"
                "  apply mk_eq_one_of_replay p13Relator\n"
                "    (fun i ↦ Finset.mem_coe.mpr (p13Relator_mem i))\n"
                "    %sWord %sAtoms\n"
                "  decide\n\n" %
                (chunk_name, chunk_name, chunk_name, chunk_name))

        # A few replay proofs have more than twenty chunks.  Aggregate chunks
        # through bounded eight-factor blocks so neither free reduction nor
        # elaboration needs an artificial recursion-depth budget increase.
        block_names = []
        for block_index, offset in enumerate(range(0, len(chunk_names), 8)):
            names = chunk_names[offset:offset + 8]
            words = chunk_words[offset:offset + 8]
            block_word = ()
            for value in words:
                block_word = helper.multiply(block_word, value)
            block_name = "reduction%dBlock%d" % (index, block_index)
            block_names.append(block_name)
            chunk_product = "([%s] : List (FreeGroup P13Generator)).prod" % \
                ", ".join(name + "Word" for name in names)
            output.write(
                "def %sWord : FreeGroup P13Generator :=\n"
                "  word %s\n\n" % (block_name, lean_word(block_word)))
            output.write(
                "theorem %s_eq_one : p13Word %sWord = 1 := by\n"
                "  have hfree : %sWord = %s := by decide\n"
                "  rw [hfree]\n" %
                (block_name, block_name, block_name, chunk_product))
            emit_prod_is_one(names, output)

        block_product = "([%s] : List (FreeGroup P13Generator)).prod" % \
            ", ".join(name + "Word" for name in block_names)
        output.write(
            "theorem reduction%d :\n"
            "    p13Word (word %s) = p13Word (word %s) := by\n"
            "  have hfree : %s =\n"
            "      word %s * (word %s)⁻¹ := by decide\n"
            "  apply eq_of_mul_inv_eq_one\n"
            "  rw [← map_inv, ← map_mul, ← hfree]\n" %
            (index, lean_word(reduction["left"]),
             lean_word(reduction["right"]),
             block_product, lean_word(reduction["left"]),
             lean_word(reduction["right"])))
        emit_prod_is_one(block_names, output)

    product_reductions = {
        (tuple(reduction["left"]), tuple(reduction["right"])):
            reduction["target_index"]
        for reduction in data["reductions"]
        if reduction["kind"] == "product"
    }
    support = [tuple(word) for word in data["support_words"]]
    classes = [tuple(word) for word in data["product_class_words"]]
    support_index = {value: index for index, value in enumerate(support)}
    for reduction in data["reductions"]:
        if reduction["kind"] != "prefix":
            continue
        index = reduction["target_index"]
        target = support_index[tuple(reduction["right"])]
        if index not in UNUSED_PREFIX_REPLAYS:
            output.write(
                "/-- Checked canonicalization of a Fox prefix. -/\n"
                "@[simp] theorem prefixReplay%d :\n"
                "    p13Word (word %s) = p13Word (supportFreeWord (%d : Fin 22)) := by\n"
                "  rw [show supportFreeWord (%d : Fin 22) = word %s by decide]\n"
                "  exact reduction%d\n\n" %
                (index, lean_word(reduction["left"]), target,
                 target, lean_word(reduction["right"]), index))
        if index in UNUSED_REDUCTIONS:
            continue
        output.write(
            "/-- Group evaluation of the same checked Fox-prefix replay. -/\n"
            "@[simp] theorem prefixValue%d :\n"
            "    %s = %s := by\n"
            "  have h : wordValue p13Generator %s = "
            "wordValue p13Generator %s := by\n"
            "    rw [← p13Word_word_eq_wordValue, "
            "← p13Word_word_eq_wordValue]\n"
            "    exact reduction%d\n"
            "  simpa [wordValue, letterValue] using h\n\n" %
            (index, lean_group_value(reduction["left"]),
             lean_group_value(reduction["right"]),
             lean_word(reduction["left"]),
             lean_word(reduction["right"]), index))
    boundary = helper.canonical_boundary(certificate)
    output.write(
        "/-- Canonical integer Fox coefficients after the checked prefix\n"
        "replays above. -/\n"
        "def boundaryNumerator : Fin 13 → Fin 6 → Fin 22 → ℤ\n")
    for relator_index, relator_rows in enumerate(boundary):
        for generator_index, values in enumerate(relator_rows):
            rendered = ", ".join(str(value) if value >= 0 else
                                 "(%d)" % value for value in values)
            output.write(
                "  | %d, %d => fun i ↦ [%s].get i\n" %
                (relator_index, generator_index, rendered))
    output.write("\n")
    for left in range(22):
        for right in range(22):
            product = helper.multiply(helper.inverse_word(support[left]),
                                      support[right])
            class_index = data["product_class_table"][left][right]
            representative = classes[class_index]
            output.write(
                "theorem supportProduct%d_%d :\n"
                "    p13Word ((supportFreeWord (%d : Fin 22))⁻¹ * "
                "supportFreeWord (%d : Fin 22)) =\n"
                "      p13Word (productClassFreeWord "
                "(productClassIndex (%d : Fin 22) (%d : Fin 22))) := by\n"
                "  rw [show (supportFreeWord (%d : Fin 22))⁻¹ * "
                "supportFreeWord (%d : Fin 22) = word %s by decide]\n"
                "  change p13Word (word %s) = p13Word (word %s)\n" %
                (left, right, left, right, left, right, left, right,
                 lean_word(product), lean_word(product),
                 lean_word(representative)))
            if product == representative:
                output.write("  rfl\n\n")
            else:
                reduction_index = product_reductions.get(
                    (product, representative))
                if reduction_index is None:
                    raise ValueError("missing product replay for (%d,%d)" %
                                     (left, right))
                output.write("  exact reduction%d\n\n" % reduction_index)
    for left in range(22):
        output.write(
            "theorem supportProduct_replayed_row%d (right : Fin 22) :\n"
            "    p13Word ((supportFreeWord (%d : Fin 22))⁻¹ * "
            "supportFreeWord right) =\n"
            "      p13Word (productClassFreeWord "
            "(productClassIndex (%d : Fin 22) right)) := by\n"
            "  fin_cases right\n" % (left, left, left))
        for right in range(22):
            output.write("  · simpa using supportProduct%d_%d\n" %
                         (left, right))
        output.write("\n")
    output.write(
        "/-- Every one of the 484 support products is collected into its\n"
        "exact abstract P13 coefficient class. -/\n"
        "theorem supportProduct_replayed (left right : Fin 22) :\n"
        "    p13Word ((supportFreeWord left)⁻¹ * supportFreeWord right) =\n"
        "      p13Word (productClassFreeWord (productClassIndex left right)) := by\n"
        "  fin_cases left\n")
    for left in range(22):
        output.write("  · simpa using supportProduct_replayed_row%d right\n" % left)
    output.write("\n")
    output.write(
        "end\n\n"
        "end LiteralP13HodgeReplay\n"
        "end GroupApproximation\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--replay", type=Path, required=True)
    parser.add_argument("--replay-script", type=Path, required=True)
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    digest = hashlib.sha256(args.replay.read_bytes()).hexdigest()
    if digest != EXPECTED_REPLAY_SHA256:
        raise ValueError("replay SHA-256 mismatch: %s" % digest)
    data = json.loads(args.replay.read_text())
    helper = load_replay_helpers(args.replay_script)
    validate(data, helper)
    with args.output.open("w") as output:
        emit(data, helper, args.certificate, output)
    print("wrote %d bytes to %s" %
          (args.output.stat().st_size, args.output))


if __name__ == "__main__":
    main()
