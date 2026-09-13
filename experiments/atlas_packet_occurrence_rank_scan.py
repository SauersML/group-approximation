"""Root-level occurrence census and nuisance-quotient rank scan of the Atlas packet.

Run on MSI, not locally:

    python3 experiments/atlas_packet_occurrence_rank_scan.py --out scan.json

The scan reconstructs the complete 4,648-entry rank-five packet through
``atlas_relator_rank5_complete_packet.assemble`` (checking the recorded ordered
word-list SHA-256), recovers the root-level factor data of every entry from the
three source generators, and linearizes every entry in the free rectangular
language used by the Atlas nuisance-quotient nodes:

* a rank-five root ``x_kl(w)`` is the block transvection ``1 + N`` with
  ``N = iota_k w p_l`` and ``w`` an arbitrary rectangular coefficient map;
* ``(1+N)^(-1) = 1 - N`` and ``N_t N_u != 0`` only when the target index of
  ``t`` equals the source index of ``u``;
* commutators follow the packet convention ``[x,y] = x y x^-1 y^-1``;
* a reverse-dictionary entry ``g w_g^-1`` identifies the atlas generator ``g``
  blockwise with the product of its root factors.

Expanding a relator ``= 1`` gives, per matrix block, one exact integer linear
equation among path monomials (ordered root letters along composable index
paths) and generator blocks.  The script then:

1. verifies the entry census (root/orth/st3/inv/reverse counts);
2. histograms every projected equation by term count and coefficient sum;
3. for every right-hand-side occurrence of a two-letter nonconstant
   coefficient word computes its complete star (every packet row meeting it),
   the exact rank increment ``rank[C D] - rank D`` with the star's path
   monomials desired and every other column nuisance, and whether the common
   mode (all star columns equal) survives every meeting row;
4. repeats (3) for all one-letter right-hand-side stars;
5. checks globally whether the all-ones vector on every connected component
   satisfies every projected equation, i.e. whether any literal entry can pin
   a common mode;
6. validates against the hand-checked families: packet entries 3261,3262
   (increment zero) and the common-RHS star 3261,3336,3409 (increment two).
"""

import argparse
import hashlib
import json
import os
import re
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import atlas_relator_rank5_complete_packet as packet  # noqa: E402
import atlas_relator_rank5_reverse as reverse_dictionary  # noqa: E402

EXPECTED_SHA = "9e751115287b18fbe847309379d2710ffa0b1466c836d32ff4ec24446e6c2b99"
ROOT = re.compile(r"root_(\d)(\d)_([1efEF])([1efEF])$")
ORTH = re.compile(r"orth_(\d)(\d)_(\d)(\d)_([1efEF])([1efEF])$")
ST3 = re.compile(r"st3_(\d)(\d)(\d)_([1efEF])([1efEF])$")
INV = re.compile(r"inv_(\d)(\d)_([1efEF])$")


def coeff(*letters):
    out = tuple(a for a in letters if a != "1")
    return out if out else ("1",)


def comm(a, b):
    return [(1, a), (1, b), (-1, a), (-1, b)]


def expand(word):
    """Exact expansion of prod (1 + eps N_t), constant term omitted."""
    states = {}
    for eps, letter in word:
        k, l, _w = letter
        new = dict(states)
        key = (k, l, (letter,))
        new[key] = new.get(key, 0) + eps
        for (a, end, mono), c in states.items():
            if end == k:
                key2 = (a, l, mono + (letter,))
                new[key2] = new.get(key2, 0) + c * eps
        states = new
    blocks = {}
    for (a, end, mono), c in states.items():
        if c:
            blocks.setdefault((a, end), {})
            blocks[(a, end)][mono] = blocks[(a, end)].get(mono, 0) + c
    return {b: {m: c for m, c in terms.items() if c}
            for b, terms in blocks.items()
            if any(terms.values())}


def root_word(name, reverse_factors):
    m = ROOT.fullmatch(name)
    if m:
        i, j, r, s = int(m.group(1)), int(m.group(2)), m.group(3), m.group(4)
        return "root", comm((i, j, coeff(r)), (i, j, coeff(s)))
    m = ORTH.fullmatch(name)
    if m:
        i, j, k, l = map(int, m.group(1, 2, 3, 4))
        r, s = m.group(5, 6)
        return "orth", comm((i, j, coeff(r)), (k, l, coeff(s)))
    m = ST3.fullmatch(name)
    if m:
        i, j, k = map(int, m.group(1, 2, 3))
        r, s = m.group(4, 5)
        return "st3", comm((i, j, coeff(r)), (j, k, coeff(s))) + [
            (-1, (i, k, coeff(r, s)))]
    m = INV.fullmatch(name)
    if m:
        i, j, a = int(m.group(1)), int(m.group(2)), m.group(3)
        return "inv", [(1, (i, j, coeff(a))), (1, (i, j, coeff(a)))]
    if name.startswith("reverse_"):
        return "reverse", reverse_factors[name]
    raise AssertionError("unparsed packet entry name: %s" % name)


def column_label(col):
    if col[0] == "gen":
        return "gen:%s:%d%d" % (col[1], col[2], col[3])
    return "mono:" + "|".join("%d%d(%s)" % (k, l, "".join(w))
                              for k, l, w in col[1])


def rank_exact(rows, cols):
    matrix = [[Fraction(row.get(c, 0)) for c in cols] for row in rows]
    rank, m = 0, len(matrix)
    for col in range(len(cols)):
        pivot = next((i for i in range(rank, m) if matrix[i][col] != 0), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        pv = matrix[rank][col]
        for i in range(m):
            if i != rank and matrix[i][col] != 0:
                factor = matrix[i][col] / pv
                matrix[i] = [a - factor * b
                             for a, b in zip(matrix[i], matrix[rank])]
        rank += 1
    return rank


def rank_gf2(rows, cols):
    index = {c: i for i, c in enumerate(cols)}
    basis = {}
    rank = 0
    for row in rows:
        bits = 0
        for c, v in row.items():
            if c in index and v % 2:
                bits ^= 1 << index[c]
        while bits:
            top = bits.bit_length() - 1
            if top in basis:
                bits ^= basis[top]
            else:
                basis[top] = bits
                rank += 1
                break
    return rank


CHARACTERISTIC = [2]


def star_report(rows, desired, nuisance):
    cols_all = sorted(desired | nuisance, key=column_label)
    cols_nui = sorted(nuisance, key=column_label)
    if CHARACTERISTIC[0] == 2:
        total = rank_gf2(rows, cols_all)
        nui = rank_gf2(rows, cols_nui)
        common_mode = all(sum(row.values()) % 2 == 0 for row in rows)
    else:
        total = rank_exact(rows, cols_all)
        nui = rank_exact(rows, cols_nui)
        common_mode = all(sum(row.values()) == 0 for row in rows)
    return total, nui, total - nui, common_mode


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default="atlas_packet_occurrence_rank_scan.json")
    parser.add_argument("--characteristic", type=int, choices=(0, 2), default=2,
                        help="2: coefficient maps over F_2 (the packet field); "
                             "0: integer coefficients, for comparison")
    args = parser.parse_args()
    CHARACTERISTIC[0] = args.characteristic

    metadata, entries = packet.assemble(False)
    sha = metadata["word_list_sha256"]
    assert sha == EXPECTED_SHA, sha
    assert len(entries) == 4648

    rev_rows, _lengths = reverse_dictionary.generate_relators(verify=False)
    reverse_factors = {}
    for name, _chart, _u, _v, factors, _word, _relator, _ok in rev_rows:
        reverse_factors["reverse_%s" % name] = [
            (1, (k, l, coeff(b))) for k, l, b in factors]

    census, equations = {}, []
    for index, entry in enumerate(entries):
        kind, word = root_word(entry["name"], reverse_factors)
        census[kind] = census.get(kind, 0) + 1
        blocks = expand(word)
        if kind == "reverse":
            # g = prod factors  =>  G_ab - [prod - 1]_ab = 0 on every block.
            gen = entry["name"][len("reverse_"):]
            for block, terms in blocks.items():
                row = {("gen", gen, block[0], block[1]): 1}
                for mono, c in terms.items():
                    row[("mono", mono)] = row.get(("mono", mono), 0) - c
                equations.append((index, entry["name"], kind, block, row))
        else:
            for block, terms in blocks.items():
                row = {("mono", mono): c for mono, c in terms.items()}
                equations.append((index, entry["name"], kind, block, row))
    assert census == {"root": 200, "orth": 2980, "st3": 1432,
                      "inv": 24, "reverse": 12}, census
    vanished_in_characteristic = 0
    if args.characteristic == 2:
        reduced = []
        for index, name, kind, block, row in equations:
            row2 = {c: v % 2 for c, v in row.items() if v % 2}
            if row2:
                reduced.append((index, name, kind, block, row2))
            else:
                vanished_in_characteristic += 1
        equations = reduced

    histogram = {}
    nonzero_sum_rows = []
    modulus = args.characteristic if args.characteristic else None
    for index, name, kind, block, row in equations:
        total = sum(row.values())
        if modulus:
            total %= modulus
        key = "%s:terms=%d:sum=%d" % (kind, len(row), total)
        histogram[key] = histogram.get(key, 0) + 1
        if total != 0:
            nonzero_sum_rows.append((index + 1, name, list(block),
                                     {column_label(c): v for c, v in row.items()}))

    by_column = {}
    for eq in equations:
        for col in eq[4]:
            by_column.setdefault(col, []).append(eq)

    def stars(two_letter):
        out = []
        for col, meeting in sorted(by_column.items(), key=lambda kv: column_label(kv[0])):
            if col[0] != "mono" or len(col[1]) != 1:
                continue
            _k, _l, w = col[1][0]
            nonconstant = all(a != "1" for a in w)
            if two_letter != (len(w) == 2 and nonconstant):
                continue
            if not two_letter and len(w) != 1:
                continue
            rows = [eq[4] for eq in meeting]
            desired = {c for row in rows for c in row
                       if c[0] == "mono" and len(c[1]) >= 2}
            nuisance = {c for row in rows for c in row} - desired
            total, nui, inc, cm = star_report(rows, desired, nuisance)
            out.append({
                "rhs": column_label(col),
                "star_entries": sorted({eq[0] + 1 for eq in meeting}),
                "star_kinds": sorted({eq[2] for eq in meeting}),
                "desired_columns": len(desired),
                "rank_total": total, "rank_nuisance": nui,
                "quotient_increment": inc, "common_mode_survives": cm,
            })
        return out

    two = stars(True)
    one = stars(False)
    big_one = [s for s in one if s["quotient_increment"] > 2]
    first_big_one = min(big_one, key=lambda s: s["star_entries"][0]) if big_one else None

    def family_increment(entry_numbers):
        rows = [eq[4] for eq in equations if eq[0] + 1 in entry_numbers]
        desired = {c for row in rows for c in row
                   if c[0] == "mono" and len(c[1]) >= 2}
        nuisance = {c for row in rows for c in row} - desired
        return star_report(rows, desired, nuisance)

    validation = {
        "entries_3261_3262": family_increment({3261, 3262}),
        "star_3261_3336_3409": family_increment({3261, 3336, 3409}),
    }
    assert validation["entries_3261_3262"][2] == 0, validation
    assert validation["star_3261_3336_3409"][2] == 2, validation

    canonical = json.dumps(
        [[eq[0], eq[1], list(eq[3]),
          sorted((column_label(c), v) for c, v in eq[4].items())]
         for eq in equations], separators=(",", ":")).encode("ascii")
    summary = {
        "characteristic": args.characteristic,
        "rows_vanishing_in_characteristic": vanished_in_characteristic,
        "two_letter_star_kinds": sorted({k for s in two for k in s["star_kinds"]}),
        "one_letter_star_kinds": sorted({k for s in one for k in s["star_kinds"]}),
        "one_letter_increment_histogram": {
            str(v): sum(1 for s in one if s["quotient_increment"] == v)
            for v in sorted({s["quotient_increment"] for s in one})},
        "first_one_letter_star_above_two": first_big_one,
        "packet_word_list_sha256": sha,
        "entry_census": census,
        "projected_equations": len(equations),
        "equation_list_sha256": hashlib.sha256(canonical).hexdigest(),
        "equation_histogram": histogram,
        "rows_with_nonzero_coefficient_sum": nonzero_sum_rows,
        "two_letter_star_count": len(two),
        "two_letter_max_increment": max(s["quotient_increment"] for s in two),
        "two_letter_star_sizes": sorted({len(s["star_entries"]) for s in two}),
        "two_letter_common_mode_all_survive": all(s["common_mode_survives"] for s in two),
        "one_letter_star_count": len(one),
        "one_letter_max_increment": max(s["quotient_increment"] for s in one),
        "one_letter_common_mode_all_survive": all(s["common_mode_survives"] for s in one),
        "validation": validation,
        "two_letter_stars": two,
        "one_letter_stars": one,
    }
    with open(args.out, "w") as handle:
        json.dump(summary, handle, sort_keys=True, indent=1)
    for key in ("characteristic", "rows_vanishing_in_characteristic",
                "two_letter_star_kinds", "one_letter_star_kinds",
                "one_letter_increment_histogram", "first_one_letter_star_above_two",
                "packet_word_list_sha256", "entry_census", "projected_equations",
                "equation_list_sha256", "equation_histogram",
                "two_letter_star_count", "two_letter_max_increment",
                "two_letter_star_sizes", "two_letter_common_mode_all_survive",
                "one_letter_star_count", "one_letter_max_increment",
                "one_letter_common_mode_all_survive", "validation"):
        print(key, json.dumps(summary[key], sort_keys=True))
    print("rows_with_nonzero_coefficient_sum", len(nonzero_sum_rows))
    print("DONE")
    return 0


if __name__ == "__main__":
    sys.exit(main())
