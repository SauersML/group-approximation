---
rg: 2
id: aperiodic-sft-gated-models-break-refinement-relations
kind: claim
title: Gated rule actions on colourings with an illegal window violate a fixed refinement relator of the derived full group of an aperiodic Z^2-SFT
distinct_from:
  labbe-relator-shifts-carry-patch-rich-periodic-points: That asks for periodic points of relator shifts carrying large legal patches, for some extensions; this proves that gated extensions of every radius give none, because a refinement relator of bounded length fails at the gate boundary.
  minimal-free-sft-full-group-pattern-models-are-exact: That treats validly coloured Z^d-sets, which have no defects; this treats colourings with illegal windows under gated rules.
  zd-derived-full-group-fp-forces-finite-type: That concerns colourings whose small windows are all legal; this concerns colourings with illegal windows, where rules are switched off near the defects.
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `X ⊆ A^(Z^2)` is a free minimal subshift of finite type and `G = D([[Z^2 ~ X]])`.
- For `R` large, `S` is the set of rule 3-cycles `s(pi, e)` of legal `B(R)`-patterns `pi` in
  directions `e ∈ {±e_1, ±e_2}`, which generates `G`.
- `W(p, e)` are ChJN's nested commutator words of `zd-derived-full-group-fp-forces-finite-type-proof`.
- The **refinement relators** at scale `R` are
  `s(pi, e) = prod_(p ∈ L_(B(R+1)), p|B(R) = pi) W(p, e)`, one for each legal `pi` and each `e`.
  They hold in `G`, since the right-hand factors are commuting 3-cycles on the cylinders of the
  extensions of `pi`. Their lengths are bounded by a constant `L_4(R)`.

**Gated models.**
- Fix a gate radius `rho` and an arbitrary *active set* `Act ⊆ Z^2`, and let `c : Z^2 -> A` be any
  colouring.
- The firing set is `F = {m ∈ Act : c|(m + B(rho)) is legal}`.
- Each `s(pi, e)` acts by the 3-cycle `(m, m+e, m-e)` at every `m ∈ F` with `c|(m + B(R)) = pi`,
  and trivially elsewhere.
- This is the "gated" extension of the relator-shift criterion
  (`zd-subshift-full-group-lef-via-periodic-relator-shifts`), with `Act = Z^2` and `rho = R'`.

**Statement.** There are constants `R_0` and `K`, depending only on `X`, such that for every
`R >= R_0` and `rho >= R + K` the following hold.
1. Every gated model is well defined: each `s ∈ S` acts by a permutation.
2. If `F` is nonempty and `F ≠ Z^2`, some refinement relator fails at a point of `F` adjacent to
   `Z^2 \ F`.
3. Consequently, a gated model satisfying all refinement relators has `F = ∅` (the action is
   trivial) or `F = Z^2`. In the second case `c` is legal everywhere, so `c ∈ X`.
4. For a periodic colouring `F = Z^2` is impossible, since `X` is aperiodic. So gated periodic
   models of the relators of length `<= L_4(R)` carry the trivial action.
   - Consequently, for the generating set `S`, hypothesis (H1) of the relator-shift criterion fails
     for every gated extension once `2n >= L_4(R)`.
   - Other generating sets are not covered: gating their generators directly need not agree with
     gating the words that express `S`.

**What survives.** Spatial approximants whose extended rules on illegal windows move points in
non-standard ways (not switched off), and non-spatial marked groups.

**Proof:** `aperiodic-sft-gated-models-break-refinement-relations-proof`.
