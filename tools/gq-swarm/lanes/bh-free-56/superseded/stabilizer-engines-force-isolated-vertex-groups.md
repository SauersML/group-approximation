---
rg: 2
id: stabilizer-engines-force-isolated-vertex-groups
kind: claim
title: If the stabilizer engine F_B (or its derived group D(F_B)) is finitely presented, then the vertex group B is isolated in the space of marked groups (finitely presented and finitely discriminable); so F_B is not finitely presented for B = Z (Reid's group) or for any infinite residually finite B
requires:
  - free-product-boundary-groupoids-carry-the-vertex-group-homology
  - fp-stabilizer-engines-need-fp-vertex-groups
  - stabilizer-engines-of-non-fp-simple-groups-are-not-fp
invalidates:
  - fp-decidable-vertex-groups-have-fp-stabilizer-engines
distinct_from:
  fp-stabilizer-engines-need-fp-vertex-groups: that gets finite presentation of B from a quasi-retraction onto one germ; this gets finite discrimination of B from continuity of the engine in the space of marked groups, which the retraction cannot see (B = Z is finitely presented and decidable, and its engine is still not finitely presented).
  fp-decidable-vertex-groups-have-fp-stabilizer-engines: that conjectured "B finitely presented and decidable suffices"; this refutes it at B = Z and replaces the hypothesis by "B isolated", which is necessary.
---

**ESTABLISHED** (lane proof, bh-free-56, 2026-09-18; elementary given Nekrashevych's theorem
and the parent nodes; not reviewed; no priority claimed).

**Notation.** As in `free-product-boundary-groupoids-carry-the-vertex-group-homology`, with
`k = 2`: `B` is an infinite finitely generated group, `D = Z/2 * B = <a> * B`, `T` is the
Bass–Serre tree of `D` with the valence-2 vertices suppressed (vertices `D/B`, edges `D/<a>`),
`X` is `T` compactified by its `B`-vertices, and `F_B = [[D ⋉ X]]`. For `u ∈ D` let `h(u)` be
the half-tree of the edge `u<a>` on the side of the vertex `uB`; then `h(ua)` is its complement
and `d·h(u) = h(du)`.

**Isolated groups** (Cornulier–Guyot–Pitsch, arXiv:math/0511714). A finitely generated group is
isolated in the space of marked groups iff it is finitely presented and *finitely
discriminable*: some finite `F ⊂ B − {1}` meets every nontrivial normal subgroup. Isolated
groups have solvable word problem.

## Statement

If `F_B` is finitely presented, then `B` is isolated. The same holds if `D(F_B)` is finitely
presented, since then `F_B` is (`fp-stabilizer-engines-need-fp-vertex-groups`, step 1).

**Corollaries.**
1. **Reid's group** `F_Z` and its simple derived group are not finitely presented, since `Z` is
   not finitely discriminable. This settles the open item of
   `reid-higman-thompson-variant-d-zero-abelianization`; see
   `reid-higman-thompson-variant-is-not-finitely-presented`.
2. `F_B` and `D(F_B)` are not finitely presented for any infinite residually finite `B`: for
   example `Z^d`, free groups, `SL_n(Z)`, or any finitely generated linear group. Finite-index
   normal subgroups avoid every finite set.
3. `fp-decidable-vertex-groups-have-fp-stabilizer-engines` is false at `B = Z`. The corrected
   conjecture is `isolated-vertex-groups-have-fp-stabilizer-engines`. Its hypothesis is now
   necessary, and it subsumes both earlier necessary conditions.

## Proof

**Step 0: two facts about finite discrimination.**
- *(i) It fails exactly when proper quotients converge.* If `F` discriminates, every proper
  quotient `B/N` kills some `f ∈ F`, so it stays outside the neighbourhood `{f ≠ 1 : f ∈ F}`.
  If no finite set discriminates, list `B − {1} = {b_1, b_2, ...}` and choose
  `1 ≠ N_m ◁ B` avoiding `b_1, ..., b_m`. Then `B/N_m → B`.
- *(ii) Finite presentation is openness.* If `B = <T | R>` is finitely presented, every marked
  group close enough to `(B, T)` satisfies `R`, so it is a marked quotient of `B`. Conversely,
  if `B` is not finitely presented, the truncations `<T | r_1, ..., r_m>` converge to `B` and
  are not quotients of it.

**Step 1: the engine is continuous in `B`.** Let `(B_n, T_n) → (B, T)` in the space of
marked groups.
- *Approximating groups.* Put `D_n = <a> * B_n` with its tree `T_n`. Let `X_n` be `T_n`
  compactified by its `B_n`-vertices if `B_n` is infinite, and the space of ends of `T_n` if
  `B_n` is finite. Put `F_n = [[D_n ⋉ X_n]]`. We may assume `|B_n| ≥ 3`.
- *Local faithfulness.* In both `X` and `X_n`, a nonempty open set contains three ends. A tree
  automorphism fixing three ends fixes an edge, and edges have trivial pointwise stabilizers.
  So a label that fixes a nonempty piece pointwise is `1`.
- *Encoding.* An element of `F_B` is a finite list of (piece, label) pairs. Pieces are Boolean
  combinations of half-trees `h(u)`, where `u` is a word in `a` and `T`. Labels are words.
  Products are computed formally: `d·h(u) = h(du)`, together with Boolean operations and
  concatenation of labels (`stabilizer-engines-of-non-fp-simple-groups-are-not-fp`, Lemma).
  - Reading the same words in `D_n` gives the formal image of every datum.
  - For a finite generating set `S` of `F_B`, fix data for each `s ∈ S`. Its image `s_n` is an
    element of `F_n` once the finitely many partition identities in that data hold in `X_n`.
- *Claim.* For every word `w` in `S`, `w = 1` in `F_B` iff `w_n = 1` in `F_n`, for all
  `n ≥ N(w)`.
- *Proof of the claim.* By local faithfulness, `w = 1` iff every nonempty atom of the computed
  data of `w` carries label `1`, and likewise in `F_n`. Only finitely many words of `D` occur
  in that data.
  - *Labels.* In the free product, a word is trivial iff iterated deletion of trivial
    `B`-syllables and cancellation of `aa` empties it. For large `n` each syllable is trivial
    in `B` iff it is trivial in `B_n`. So each label is `1` in `D` iff it is `1` in `D_n`.
  - *Pairwise position of half-trees.* The position of `h(u)` and `h(u')` (equal,
    complementary, nested, disjoint or co-disjoint) is read from the normal-form shape of
    `u^{-1}u'`: which `B`-syllables are trivial, and the first and last letters. For large `n`
    the shape is the same in `D_n`.
  - *Atoms.* A nonempty intersection of half-trees contains a vertex, and by Helly for subtrees
    it is nonempty iff the half-trees meet pairwise. It then contains a point of `X`. In `X_n`
    it also contains an end once `|B_n|` exceeds the number of half-trees involved: from the
    vertex, walk out along uncut edges.
  - So atom emptiness agrees for large `n`.

**Step 2: finite presentation forces marked quotients.** Suppose `F_B = <S | R>` is finitely
presented. Choose `S ⊇ {a} ∪ T`, where `a` and `t ∈ T` are single-piece data with labels `a`
and `t`.
- For `n ≥ max_{r ∈ R} N(r)`, the rule `s ↦ s_n` extends to a homomorphism `φ_n : F_B → F_n`.
- On `D` it is the marked map `D → D_n`. So `B_n` is a marked quotient of `B` for all large
  `n`. With Step 0(ii) this re-proves that `B` is finitely presented.

**Step 3: finite discrimination.** Suppose `B` is not finitely discriminable, and take proper
quotients `B_n = B/N_n → B` (Step 0(i)).
- By Step 2, `ker φ_n ⊇ N_n ≠ 1` for all large `n`.
- `D ⋉ X` is a minimal groupoid of germs on a Cantor set (parent node). By Nekrashevych
  (arXiv:1511.08241, the main theorem), the alternating full group `A(F_B)` is contained in
  every nontrivial normal subgroup of `F_B`. So `A(F_B) ⊆ ker φ_n`.
- Fix `1 ≠ x ∈ A(F_B)`, written as a word `w`. By Step 1, `φ_n(x) = w_n ≠ 1` for
  `n ≥ N(w)`. This is a contradiction. `∎`

**Calibration.**
- For finite `B` the tree is locally finite, and the engines are Higman–Thompson-type groups.
  These are finitely presented, and finite groups are isolated.
- For an infinite finitely presented simple `B`, such as Thompson's `T` or `V`, `B` is
  isolated and the theorem is silent.
- Step 3 is exactly the Houghton heuristic of `simple-inputs-have-finitely-presented-stabilizer-engines`,
  made precise.
  - Wrapping `Z` to `Z/n` turns the parabolic germ at a vertex into a rotation of order `n`.
  - Every relation of bounded length survives the wrapping, while `t^n ≠ 1` dies.
  - The far-commutation relations of the local `H_2` are the ones no finite presentation can
    supply.

## Lesson for general BH

**Continuity obstruction.** Suppose a host `H(B)` is built from the input by local rules, so
that it varies continuously with `B` in the space of marked groups. Suppose also that it has a
persistent monolith: a fixed nontrivial subgroup contained in every nontrivial normal subgroup.
This holds for every full group of a minimal groupoid, and for every simple host.

Then `H(B)` is finitely presented only if `B` is isolated. The proof is Steps 2–3: nearby hosts
become quotients, and the monolith cannot die.

Two things follow.
- **Local hosts need isolated inputs.** No construction that reads the input through local
  labels can make a non-isolated group, such as a residually finite one, into a subgroup of a
  finitely presented simple group at its own emitter. The input must first be pushed into an
  isolated group. That is Cornulier–Guyot–Pitsch Question 4
  (`every-decidable-group-embeds-in-an-isolated-group`), a Boone–Higman-type step in its own
  right.
- **Track C reduces to two open statements.** It becomes Question 4 plus
  `isolated-vertex-groups-have-fp-stabilizer-engines`.

A universal host must therefore be discontinuous in its input. Higman-type and Clapham-type
encodings, and type (A) actions on an extra, non-approximable set, all have this property.
