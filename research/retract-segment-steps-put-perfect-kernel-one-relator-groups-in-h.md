---
rg: 2
id: retract-segment-steps-put-perfect-kernel-one-relator-groups-in-h
kind: claim
title: A cyclic Magnus segment step needs Z to see only one edge element, primitively, since the segment then retracts onto that edge group, which puts every perfect-kernel survivor and so every torsion-free two-generator one-relator group of length at most 13 in H
distinct_from:
  magnus-segment-steps-put-one-relator-groups-in-h: its hnn step needs a map to Z nonzero on both edge elements (rational window space); this needs one edge element only, with value +-1 (integral window lattice), and closes exactly the 12 perfect-kernel survivors it left open. Its item 5 asks for a nonabelian target Q; item 3 here shows no bounded-length poly-residually-nilpotent Q exists, and item 1 shows none is needed.
  vertex-injective-quotients-give-hughes-free-division-rings: its item 6 (retract trees) is the engine; this applies it to cyclic Magnus segment steps, where the retraction is a map to Z, instead of to the whole Magnus HNN with rank-m edge groups, where its own "where it stops" says the retract condition fails.
  edge-injective-quotients-give-hughes-free-division-rings: item 2 there needs f(a) f(c) != 0 on both edge elements of a cyclic HNN; here one edge element may be invisible to every map to Z.
  kaplansky-zero-divisor-conjecture: this adds no case of the conjecture; groups in H are locally indicable, and torsion-free one-relator groups already satisfy it (Higman; Brodskii, Howie; Lewin-Lewin for the division-ring embedding).
artifacts:
  - experiments/perfect-kernel-segment-targets-2026-09-17/retract_segment_certify.py
  - experiments/perfect-kernel-segment-targets-2026-09-17/survivors.txt
  - experiments/perfect-kernel-segment-targets-2026-09-17/census-L13.txt
  - experiments/perfect-kernel-segment-targets-2026-09-17/survivor_structure.py
  - experiments/perfect-kernel-segment-targets-2026-09-17/nielsen_search.py
---

**ESTABLISHED** (written proof, unreviewed) by
[[retract-segment-steps-perfect-kernel-one-relator-proof]]. New class for Hughes-free existence in
positive characteristic and for crossed products; nothing new for the zero-divisor conjecture (see the end).

**Setting.** `𝓗` is the class of hereditarily Hughes-free embeddable groups of
[[vertex-injective-quotients-give-hughes-free-division-rings]]. `G = <a, t | r>` with `t` of exponent sum `0`,
Magnus rewrite `r' ∈ F(a_0, …, a_m)`, `m ≥ 1`, exponent vector `e = (e_0, …, e_m)`, segments
`S_[0,n] = <a_0, …, a_{n+m} | r'_0, …, r'_n>` (so `S_[0,-1]` is free on `a_0, …, a_{m-1}`), as in
[[magnus-segment-steps-put-one-relator-groups-in-h]]. The *integral window lattices* are `Λ_0 = Z^m` and
`Λ_{n+1} = {(w_1, …, w_m) : ∃ w_0, (w_0, …, w_{m-1}) ∈ Λ_n, Σ e_i w_i = 0}`; `Λ_{n+1}` is the set of top windows
of homomorphisms `S_[0,n] -> Z`.

## Theorem

1. **Retract segment step.** Suppose that for some `α, β ∈ F(a_0, …, a_{m-1})` the substitution
   `a_m = α^{-1} σ β^{-1}` turns `r'` into a cyclic word `σ^{-1} x σ y` with `x, y ≠ 1` in `F(a_0, …, a_{m-1})`.
   Suppose that for every `n ≥ 0` the functional `c_x` or the functional `c_y` takes the value `1` on `Λ_n`
   (i.e. the gcd of its values on `Λ_n` is `1`). Then `G ∈ 𝓗`. The same holds from the bottom.
   - For `n ≥ 0`, `S_[0,n]` is the HNN extension of `S_[0,n-1]` along `<x_n> -> <y_n^{-1}>`, where `x_n, y_n`
     are `x, y` shifted by `n`. If `ψ: S_[0,n-1] -> Z` has `ψ(x_n) = 1`, then `g ↦ x_n^{ψ(g)}` retracts
     `S_[0,n-1]` onto the edge group `<x_n>`. Item 6 of the vertex-injective lemma (retract trees) then climbs
     the step. Only one edge element has to be seen by `Z`.
   - The chain `Λ_0 ⊇ Λ_1 ⊇ …` is constant once two consecutive terms agree, so the condition is decidable
     whenever the chain stabilizes, and `retract_segment_certify.py` decides it exactly (Hermite normal form).
2. **The perfect-kernel family.** Let `r'` have span `2` and `e = (0, ±1, 0)`, and let `a_2` (or `a_0`) occur
   exactly twice in `r'`, with opposite signs, so `r' = a_2^{-1} x a_2 y` cyclically. If `a_1` has exponent sum
   `±1` in `x` or in `y`, then `G ∈ 𝓗`. Here `H_1(S_[0,n]) = Z a_0 ⊕ Z a_{n+2}` for `n ≥ 0`, so `Λ_n = {(0, w)}`
   for `n ≥ 1`, and the condition is only about the exponent of `a_1`. Since `e_1 = ±1` is the sum of the two
   `a_1`-exponents, this holds whenever one of them is `0`.
3. **No bounded-length target meets the exact HNN criterion; none is needed.** For every span-2 rewrite with
   `e = (0, ±1, 0)`:
   - **(weights)** for any group `Q`, any map `S_[0,n] -> Q` and the lower-central weights `w_i` of the images of
     `a_i`, `w_{j+1} ≥ w_j + w_{j+2}`. Two consecutive relations force `w_{j+1} = w_{j+2} = ∞`.
   - So for `n ≥ 1` every map from `S_[0,n]` to a residually nilpotent group kills `a_1, …, a_{n+1}`. The largest
     residually nilpotent quotient of `S_[0,n]` is `F(a_0, a_{n+2})`, and `S_[0,n]` is not residually nilpotent.
   - A map from `S_[0,n]` to a group with a normal series of length `k` and residually nilpotent factors kills
     `a_j` for `k ≤ j ≤ n + 2 - k` once `n ≥ 2k - 1`. For the 12 survivors the interior letters have a common
     normal closure (`survivor_structure.py`), so such a map kills all of them.
   - Hence, for the untwisted steps of the 12 survivors, the target `Q_n` of item 5 of
     [[magnus-segment-steps-put-one-relator-groups-in-h]] at the step `S_[0,n] ⊂ S_[0,n+1]` (its "nonabelian
     `Q`") cannot be free, a RAAG, residually torsion-free nilpotent, or poly-(residually nilpotent) of length at
     most `(n+2)/2`. There is no uniform target in any of these classes.
     Item 1 does not produce one: the target it uses at step `n` is built from the whole tree of the step.
4. **Decisive computation.** `retract_segment_certify.py` adds item 1 to the landed certifier (hierarchy rules plus
   rule 1 of the segment-step node).
   - All 12 survivors of that node's census, including `r_6 = AABabaBAAbb` and `r_8 = AABBAAbaBab`, are
     certified, each by one untwisted retract step from the top (`survivors.txt`).
   - The full census up to length 13 leaves nothing uncertified (`census-L13.txt`). Item 1 is needed for
     2 relators of length 11, 10 of length 12 and 28 of the 30660 of length 13; everything else was already
     certified by the landed rules and rule 1.

   So **every torsion-free two-generator one-relator group with relator of length at most 13 lies in `𝓗`.** For
   each, every crossed product `E * G` over every division ring `E`, in every characteristic, has a Hughes-free
   division ring, and so does every crossed product over every subgroup.
   - `nielsen_search.py` records the dead end before this: no Nielsen image of a survivor (up to 4 elementary
     moves, length ≤ 22) is certified by the landed rules without item 1.

## What is new, and what is not

- **Nothing for the zero-divisor conjecture.** Torsion-free one-relator groups are locally indicable, so their
  crossed products over domains have no zero divisors and their group algebras embed in division rings.
- **Hughes-free existence.** For these 12 groups in characteristic `p`, and for crossed products in every
  characteristic, it was open here: [[magnus-segment-steps-put-one-relator-groups-in-h]] records the literature
  (char 0 locally indicable: Jaikin-Zapirain and López-Álvarez; virtually compact special in every characteristic:
  Fisher and Sánchez-Peralta; FSP Question 7.13 for primitivity rank 2 open). All two-generator relators have
  primitivity rank at most 2. I have not decided which of these groups are virtually compact special; for any that
  are, only the crossed-product statement is new.
- **The mechanism.** Earlier rules asked `Z` to see both edge elements of a cyclic step (item 2 of the
  edge-injective lemma, rule 1). In a perfect-kernel segment one edge element is always in the interior and
  invisible to every abelian, nilpotent or bounded-length solvable target (item 3). Retracting onto the other edge
  element avoids looking at the invisible one.

## Where it stops

- Item 1 needs the top (or bottom) letter to occur exactly twice after a twist, and one edge element to be
  `Z`-primitive at every level. When `a_m` occurs three or more times the step is an amalgam along the rank-`m`
  window, not a cyclic HNN, and neither this rule nor rule 1 applies.
- The census stops at length 13 here (about 10 minutes single-threaded; length 14 is about three times that).
  No relator up to length 13 needs a step beyond item 1. Where the first one appears, if it does, is the next
  computation.
