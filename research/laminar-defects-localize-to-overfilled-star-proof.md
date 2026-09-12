---
rg: 2
id: laminar-defects-localize-to-overfilled-star-proof
kind: route
title: Atom additivity of the lifted trace plus the sofic realization theorem applied to one star
target: laminar-defects-localize-to-a-nonsofic-overfilled-star
requires:
  - sofic-amalgam-finite-subgroup-idempotent-traces-are-strict
  - lifted-trace-detects-finite-subgroup-projectives
  - nested-two-finite-subgroup-idempotents-have-strict-rank
artifacts:
  - research/artifacts/laminar-cycle-overfilled-stars-2026-09-12.md
---

Proof: Section 1 of the artifact (Theorem 1.1, Corollaries 1.2 and 1.3).

1. **Atom traces.** A nonzero laminar combination is a sum of distinct nonzero atoms. The lifted trace is
   additive, and `t_p(alpha_y) = r(y) - sum r(children)`.
2. **Some atom is overfilled.** A nonpositive total forces some atom of `d` to have
   `sum r(children) >= r(parent)`.
3. **The star is a laminar family.** The parent with its children is laminar, and `alpha_y` is one of its
   atoms.
4. **No sofic realization.** Theorem 2.6 of the `w4-kap-join` artifact (the sofic-realization form of
   `sofic-amalgam-finite-subgroup-idempotent-traces-are-strict`), applied to the star alone, would make
   that atom's trace positive. So no sofic group contains the star.
5. **Shape.** TFR1 gives `m >= 2`. A forest star has a virtually free, hence sofic, amalgam (Corollary 2.4
   of that artifact), so the star has a cycle.
