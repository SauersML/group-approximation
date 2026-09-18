---
rg: 2
id: window-shannon-certificates-force-rank-condition
kind: claim
title: If every Bernoulli window configuration of a group has a finite-window Shannon certificate, every field crossed product over it and over its finite-index overgroups has the rank condition; so the torsion-free window conjecture implies the rank condition over all virtually torsion-free groups
distinct_from:
  twisted-linear-profile-deficits-are-rank-condition-failures: that proves the gate for profile-level proofs using full translation invariance on all of G; this checks that the minimal-window LP, with translation invariance only inside the window, is inside that gate configuration by configuration, and transfers the conclusion along finite-index overgroups so that it reaches groups with torsion.
  torsion-free-windows-have-minimal-shannon-certificates: that is the open conjecture; this derives from it an independent ring-theoretic prerequisite that can fail on its own.
  virtually-hughes-free-field-crossed-products-are-stably-finite: that proves the rank condition over the virtual Hughes-free class; this says a refutation of the torsion-free window conjecture follows from any rank-condition failure over a virtually torsion-free group, which by that claim must contain a finitely generated subgroup outside that class.
  some-field-crossed-product-fails-the-rank-condition: that asks for any witness; this identifies which witnesses (virtually torsion-free groups) also refute the torsion-free window conjecture.
artifacts:
  - research/artifacts/twisted-linear-entropy-profiles-2026-09-17.md
  - research/artifacts/shannon-window-certificates-2026-09-17.md
---

Notation as in `research/artifacts/shannon-window-certificates-2026-09-17.md`, Section 2: for finite `E ∋ 1`, `F`
and a finite window `Y ⊇ F`, `LP_Y(E,F)` is the minimum of `h(y_f0) + h(x_1 y_F) - h(y_F)` under (P), (I), (D),
(T) on `V = {x_g : g ∈ YE ∪ {1}} ∪ {y_g : g ∈ Y}`. The minimal window is `Y = F`.

**Theorem.**

1. **Profiles are LP points.** Let `R = K*G` be a crossed product over a commutative field (any `σ`, `α`). If
   some twisted linear profile over `R` with support `E` and reader set `F` has `Phi < 1`, then
   `LP_Y(E ∪ {1}, F) <= Phi < 1` for every finite `Y ⊇ F`. So that configuration has no finite-window
   Shannon certificate at `G`, and not even a non-Shannon (entropic) one.
2. **Gate at `G`.** If every configuration at `G` has `LP_Y >= 1` for some finite `Y`, then every field crossed
   product over `G` has the rank condition.
3. **Transfer.** Suppose every torsion-free group `N` has the property of item 2. Then every field crossed
   product `K*G'` has the rank condition whenever every finitely generated subgroup of `G'` is virtually
   torsion-free.
4. **Decomposition.** `torsion-free-windows-have-minimal-shannon-certificates` implies prerequisite
   **(RC-vtf)**: every field crossed product over a group whose finitely generated subgroups are virtually
   torsion-free has the rank condition. This covers every finitely generated linear group in characteristic 0,
   by Selberg's lemma (classical import). So one rank-condition failure over such a group refutes the torsion-free
   window conjecture. Examples of such groups: `Q(x,y) ⋊ SL_3(Z)` by projective substitutions, twisted group
   algebras over `Sp_4(Z)`, and `F_p(x_g) ⋊ Γ` for a lattice `Γ`.

**What this changes.**
- The torsion-free conjecture is not a purely local fact about torsion. Its truth needs (RC-vtf), and (RC-vtf)
  is sensitive to finite-index overgroups with torsion. By `virtually-hughes-free-field-crossed-products-are-stably-finite`,
  (RC-vtf) is only in doubt for groups containing a finitely generated subgroup outside the virtual Hughes-free
  class, e.g. a Kazhdan subgroup. The conjecture's census (free, `Z^d`, `H_3`, Hantzsche–Wendt, all virtually
  Hughes-free) never touches those groups.
- The known torsion fakes (`Z/3`, `Z/4`, `Z/5`, `(Z/2)^2`, `D_inf`, `Z/7`) are **not** of this kind. Crossed
  products over those groups have the rank condition (amenable), so linear profiles do not explain them.
- Direction of the transfer: rank-condition failure passes *down* to finite-index subgroups (through
  `K*G' ⊂ M_n(K*N)`), not up. Unlike Shannon fakes, which `D_inf` shows need not come from torsion-free
  subgroups, a linear-profile fake at a virtually torsion-free group always gives one at a torsion-free
  subgroup.

**ESTABLISHED 2026-09-17** by [[window-shannon-certificates-force-rank-condition-proof]] (items 1–3; item 4
uses Selberg's lemma only for the linear-group examples).
