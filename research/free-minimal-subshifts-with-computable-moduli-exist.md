---
rg: 2
id: free-minimal-subshifts-with-computable-moduli-exist
kind: claim
title: Every infinite finitely presented group with solvable word problem carries a (not necessarily effective) minimal free subshift whose recurrence modulus and freeness radius are bounded by computable functions
distinct_from:
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2) and asks for an effectively closed subshift; this asks for no effectiveness at all, only computable upper bounds on two growth functions of some minimal free subshift. (M2) implies this, and the gap between them is exactly the choice of a computable path in a Pi01 class.
  gjs-countable-groups-have-free-minimal-subflows: that gives a free minimal subflow of 2^G for every countable group with no control on its moduli; this asks that the recurrence modulus and freeness radius of one such subshift be computably bounded.
  tower-classes-are-computably-bounded-pi01-classes: that is the ESTABLISHED equivalence between this statement and nonemptiness of some tower class; this is the OPEN existence statement itself.
---

**OPEN.** Statement (N).

**Statement (N).** Let `Λ` be an infinite finitely presented group with
solvable word problem. Then there are:
- a finite alphabet `A`;
- a nonempty minimal free subshift `Y ⊆ A^Λ`, which need not be effectively
  closed;
- computable functions `f̄` and `φ`, with `φ` nondecreasing;

such that `f_Y ≤ f̄` and `R_Y(s) ≤ φ(|s|)` for all `s ≠ 1`. The moduli are
those of `tower-classes-are-computably-bounded-pi01-classes`:
- `f_Y(r)` is the radius within which every `B(r)`-pattern of `Y` occurs in
  every point;
- `R_Y(s)` is the radius within which every point differs from its `s`-shift.

**Equivalent form (ESTABLISHED, `tower-classes-are-computably-bounded-pi01-classes`, part 4).**
(N) holds for `Λ` iff some computable datum `D` has a nonempty tower class
`T_D`, that is, iff some computable finitely branching tree of finite
patch-family sequences is infinite.

**Why it matters.**
- *Necessary for (M2).* By the same claim, (M2) for `Λ` gives a computable
  member of some `T_D`, so `T_D ≠ ∅`.
- *A refutation target.* If (N) fails for a single infinite finitely presented
  `Λ` with solvable word problem, then (M2) fails for `Λ`. That kills every
  route through (M2):
  - `minimal-free-sft-via-plane-constant-minimal-simulation`;
  - `effective-minimal-free-subshifts-via-overlap-recurrence`.

  The refutation needs no computability-theoretic argument beyond the growth
  of two functions.
- *Not sufficient by itself.* Going from (N) to (M2) needs a computable path in
  `T_D`. Methods that only prove `T_D ≠ ∅` stop there: compactness, Zorn, the
  local lemma plus compactness, Baire or measure genericity.

**Known instances (hand arguments).**
- *`Z^d`.* Products of Sturmian subshifts with computable slopes are effective,
  by the instance list of `decidable-fp-groups-have-effective-minimal-free-subshifts`.
  So their moduli are computable, and (N) holds.
- *Products.* (N) for `G_1` and `G_2` gives (N) for `G_1 x G_2`.
  - Take the product subshift, with alphabet `A_1 x A_2` and word length for the
    union of the generating sets.
  - Here `|(a,b)| = |a| + |b|`, so `B(r) ⊆ B_1(r) x B_2(r)`, and
    `(z_1,z_2)(a,b) = (z_1(a), z_2(b))`.
  - A `B(r)`-pattern of `Y_1 x Y_2` is therefore determined by a pair of
    patterns, one on `B_1(r)` occurring in `Y_1` and one on `B_2(r)` occurring
    in `Y_2`. Each such pair occurs in the product.
  - Such a pair occurs in any point at some `(c_1,c_2)` with `|c_i| ≤ f̄_i(r)`.
    So the recurrence bound of the product is at most `f̄_1(r) + f̄_2(r)`.
  - For `s = (s_1, s_2) ≠ 1`, pick a coordinate with `s_i ≠ 1`. Then the
    freeness radius is at most `φ_i(|s_i|) ≤ φ_i(|s|)`.
  - Minimality and freeness of the product are as in the (M2) product instance.

**Where (N) is not known.**
- Any infinite simple Kazhdan group, the inputs that
  `boone-higman-iff-simple-kazhdan-decidable-inputs` needs.
- The Gao–Jackson–Seward subflows (context) have finite moduli, but nothing
  known here bounds them computably. `gjs-guided-blueprints-are-computable-over-decidable-groups`
  gives a computable blueprint layer, not a bound on `f_Y`.

## Attempts

None beyond the evidence above.
