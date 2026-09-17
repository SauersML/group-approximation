---
rg: 2
id: fpbs-malnormal-measured-absorption-cap
kind: claim
title: Zero-cost absorption by arbitrary partial isomorphisms with infinite contact never leaves the orbit relation of an almost malnormal subgroup
distinct_from:
  fpbs-wq-normal-subgroup-cost-transfer: that is the positive group-element absorption C(a|W(H)) <= C(a|H); this shows that measurable partial isomorphisms with arbitrary Borel labels (normalizers, quasi-normalizers, window-trick maps) reach no further than W(H), whatever the action and the starting subrelation.
  fpbs-malnormal-subgroup-relations-finite-contacts: that counts graphing edges between two subgroup classes and caps contact repair by <Q(Lambda)>; this is about the contact relation phi(S) ∩ S of a single partial isomorphism, for any Borel subrelation S of a subgroup orbit relation, and caps transfinite zero-cost absorption chains at the almost malnormal hull.
  fpbs-wq-normal-hull-is-almost-malnormal: that is the group-theoretic hull; this is a measure-theoretic statement about the full pseudogroup whose invariant is that hull.
artifacts:
  - research/artifacts/fpbs-measured-absorption-cap-2026-09-17.md
---

**ESTABLISHED** through `fpbs-malnormal-measured-absorption-cap-proof`.

Let `Gamma` be countable and `a` a free p.m.p. action on `(X, mu)`. For
`Lambda <= Gamma` put `Q(Lambda) = {g : Lambda ∩ g^{-1} Lambda g infinite}`.

For a Borel subrelation `S ⊆ E_a` and `phi ∈ [[E_a]]` with label `gamma`
(`phi x = gamma(x) x`), let:
- `S_phi = {(x, y) ∈ S : x, y ∈ dom phi, (phi x, phi y) ∈ S}`, the pull-back
  of `phi(S) ∩ S`;
- `D_phi(S)` be the union of its infinite classes.

Adding `phi|D_phi(S)` to `S` costs nothing (Lemma 0 of the artifact). This
**infinite-contact step** contains:
- wq-normal absorption;
- normalizers and partial normalizers;
- quasi-normalizers;
- the Gaboriau--Tucker-Drob window condition `phi(S) ∩ S` ergodic.

1. **Theorem A.** If `S ⊆ E_{a|Lambda}`, then `gamma(x) ∈ Q(Lambda)` for almost
   every `x ∈ D_phi(S)`. No assumption is made on `S` (ergodicity, finite
   cost, group generation) or on the Borel label `gamma`.
2. **Cap.** If `Lambda` is infinite, every transfinite chain of
   infinite-contact steps starting from a subrelation of `E_{a|Lambda}` stays
   inside `E_{a|W(Lambda)}`. Here `W(Lambda)` is the wq-normal (smallest almost
   malnormal) hull of `fpbs-wq-normal-hull-is-almost-malnormal`. For every
   infinite almost malnormal `M`, `E_{a|M}` is closed under infinite-contact
   steps. In particular `N_{[E_a]}(E_{a|M}) = [E_{a|M}]`.
3. **Attained.** The infinite-contact closure of `E_{a|Lambda}` is exactly
   `E_{a|W(Lambda)}`, for every free action.
4. **Companion (finite cost as vanishing stage relative cost).** If
   `Gamma = ∪ M_n` increasingly with each `M_n` finitely generated, then the
   following are equivalent:
   - `C(a) < ∞`;
   - `relC(E_a | E_{a|M_n}) < ∞` for some `n`;
   - `relC(E_a | E_{a|M_n}) -> 0`.

**Obstruction for `fpbs-locally-free-malnormally-exhausted-finite-cost`.**
- **Invariant.** `W(H)` for finitely generated `H`, which is proper in that
  class.
- **Step.** A successor step of a zero-cost absorption chain with label outside
  `W(H)` on a non-null set. By item 1 such a map has finite contact there, so
  the chain cannot leave `E_{a|W(H)}`.
- **Consequence.** Every proof of finite cost for `Gamma_mal` must pay for
  finite-contact partial maps with total mass tending to 0 (item 4). Measurable
  labels do not help.
- **Not excluded.**
  - chains that first pay a finite-contact step and only then absorb;
  - repairs that never create contact;
  - methods not presented as chains.

This gives no lower bound on relative cost.
