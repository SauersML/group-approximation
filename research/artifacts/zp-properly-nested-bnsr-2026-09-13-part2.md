# Zaremsky Problem 1.18: properly nested BNSR invariants — part 2

Lane z1-18-nested-bnsr, 2026-09-13. Continues part 1. Status: literature table verified from
the arXiv sources listed; mechanism analysis unreviewed; no answer.

## 1. Verified literature table (what every computed example does)

| group | type | cd | levels realized | source |
|---|---|---|---|---|
| Thompson's `F` | F_∞ | ∞ | 1, 2 | Witzel–Zaremsky arXiv:1501.06682, Thm A: `Σ^2(F) = Σ^∞(F)` |
| `F_{n,∞}`, `n ≥ 2` | F_∞ | ∞ | ≤ 2 | Zaremsky arXiv:1502.02620, Thm A: `Σ^m = Σ^2` for `m ≥ 2` |
| Stein group `F_{2,3}` | F_∞ | ∞ | 1, 2 | Spahn–Zaremsky arXiv:2012.05000, Thm 3.9 |
| Lodha–Moore groups | F_∞ | ∞ | ≤ 2 | Lodha–Zaremsky arXiv:2007.12518: higher invariants equal `Σ^2` |
| Houghton `H_n` | F_{n−1} not F_n | — | 1, …, n−1 | Zaremsky arXiv:1808.00634, Thms 2.2, 2.3; Bieri Σ-property, Cor 2.7 |
| `PΣAut_n` | F | finite | includes `n−1` | Zaremsky arXiv:1607.03043 |
| McCool groups `PSA_n`, `PSO_n` | F | finite | `Σ^{n−2}` dense, `Σ^{n−1} = ∅` (for `PSA_n`) | Ershov–Zaremsky arXiv:2505.18826, Thm 1.1 |

Notes.
- Spahn–Zaremsky §4.1 conjecture the three-level shape
  `Σ^1 = S \ {[λ],[ρ]}`, `Σ^2 = S \ {[aλ+bρ] : a,b ≥ 0}`, `Σ^∞ = Σ^2` for all Stein groups
  `F_S^r`. They remark "it is notable how often Σ²=Σ^∞ holds for globally defined
  Thompson-like groups".
- In `F_{2,3}` every discrete character lies in `Σ^∞`, but some non-discrete ones are not in
  `Σ^1` (abstract of arXiv:2012.05000). Complements can be irrational, so Proposition 2 of
  part 1 (coabelian subgroups) is only sufficient.

## 2. Established so far in Cairn (this lane)

- `type-f-bnsr-invariants-stabilize-at-dimension`: a finite classifying space of dimension `n`
  gives `Σ^n = Σ^∞`. Citation: arXiv:2505.18826 §2.1.
- `bieri-sigma-property-forces-bnsr-constant-from-rank`: the Bieri Σ-property (Definition 1.4
  of arXiv:1808.00634) makes the chain constant from `min(rank, |Σ^1(G)^c|)`, by conic
  Carathéodory.
- Route `every-f-infinity-group-non-proper-bnsr-by-type-f-dichotomy` reduces the negative
  answer to `non-type-f-f-infinity-groups-have-a-non-proper-bnsr-inclusion`.

So an affirmative answer is an `F_∞` group with no finite classifying space that fails the
Bieri Σ-property. All four computed infinite-dimensional examples have the Σ-property shape
(two points in `S \ Σ^1`) or stop at level 2.

## 3. The size-bounded obstruction principle (heuristic, not a theorem)

In every Morse-theoretic computation above, `G` acts on a contractible complex `X`
(Stein–Farley cube complexes, cluster complexes, cube complexes for `H_n`). Vertices carry a
size `s(v)`, the number of feet or leaves. A character height `h_χ` plus `s` is the Morse
function.
- Ascending or descending links of large vertices are joins of matching-type complexes whose
  connectivity grows linearly in `s(v)`.
- So the failure of essential `(m−1)`-connectivity is detected at vertices of size at most
  `C·m`, and which failures occur depends only on sign patterns of `χ` on finitely many
  local moves.
- For a fixed finite set of move types the sign patterns are finite, which caps the number of
  distinct levels.

A group answering Problem 1.18 affirmatively must defeat this principle in one of three ways:
- (i) infinitely many move types, but only finitely many character coordinates;
- (ii) links of large vertices whose connectivity does not grow, for characters in a small
  set that varies with the size scale;
- (iii) a non-Morse mechanism.

## 4. Where "size selected by the character" appears naturally, and why it has not helped yet

**Periodic germs.** Let `g` be a PL homeomorphism with `g(x) = 2^n x` near `0`. A map
commuting with `g` near `0` is determined by its restriction to a fundamental domain
`[ε, 2^n ε)` and is periodic. The orbit space `R_{>0}/⟨2^n⟩` is a circle made of `n`
fundamental domains of `x ↦ 2x`, and `x ↦ 2x` acts on it as a rotation of order `n`.
- This is the calibration block `(copies)^n ⋊ C_n` of part 1 §4, with the size `n` selected
  by the germ class of `g`.
- **In `F` itself none of this survives.** Elements of `F` have finitely many breakpoints, so
  a map in `F` commuting with `g` near `0` is linear there, and the germ group of `F` at `0`
  is just `⟨x ↦ 2x⟩ ≅ Z`.
- The periodic structure survives in groups whose elements may have breakpoints accumulating
  periodically at the endpoints, as in Brin's description of `Aut(F)` (to verify). There the
  germ group at an end becomes a circle-type group, and the germ characters of `F` are
  expected not to extend (to verify).
- To make a size-`n` block activate at level `n`, the copies must carry free-group-like data
  with `Σ^1 = ∅`, e.g. lamps valued in `F_2` on the `n` fundamental domains.
- **Open sub-question:** is there a finitely generated `F_∞` group whose germ group at an end
  is `Z`-by-(periodic `F_2`-lamps), with the `Z`-coordinate surviving as a character? That
  would be the natural host for the architecture of part 1 §6: the killer direction is the
  germ class, and the lamp period is selected by the character.

**Permutational wreath products.** `A ≀_X F` with `X` the dyadic rationals is `F_∞` when `A`
is (Bartholdi–Cornulier–Kochloukova; to verify).
- The lamp-sum kernel is finitely generated through pair lamps `p_x p_y^{-1}`, since `F` is
  transitive on increasing pairs.
- Cancellation through many points suggests high finiteness for lamp characters.
- Lamp counts are invariant under the dynamics, so no character selects a period.

**Measure-weighted lamps.** A lamp character weighted by interval length would be invariant
under duplication, which is the right shape for size selection. But no Thompson-like acting
group with characters preserves a measure other than endpoint masses, and dyadic
interval-exchange groups are locally finite.

## 5. Next targets (for this lane or a successor)

1. Verify from the sources the Meier–Meinert–VanWyk criterion and the finite-index transfer.
   Then land the calibration (chain length `2^k − 1` at rank `3k`, type F) as an established
   claim refuting the rank-bound heuristic.
2. Construct or rule out the host in §4 (periodic lamp germs with a surviving germ character).
   Compute `Σ^m` for its blocks with the Morse criteria of arXiv:1501.06682 (Lemma 1.7 for
   membership, Observation 1.8 for non-membership).
3. Test the size-bounded obstruction principle as a theorem for groups with a Stein–Farley-type
   Morse structure and finitely many move types. That would settle the negative answer for that
   class, an established obstruction toward
   `non-type-f-f-infinity-groups-have-a-non-proper-bnsr-inclusion`.
