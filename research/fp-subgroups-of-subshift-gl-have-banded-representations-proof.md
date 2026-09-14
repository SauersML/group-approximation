---
rg: 2
id: fp-subgroups-of-subshift-gl-have-banded-representations-proof
kind: route
title: Periodic ring models applied to relators give genuine banded representations
target: fp-subgroups-of-subshift-gl-have-banded-representations
requires:
  - subshift-lef-models-period-below-twice-recurrence
artifacts:
  - research/artifacts/sk-lef-embedding-d-z-family-2026-09-13-part2.md
---

1. Fix a finite presentation `⟨S | Rel⟩` and list the products that evaluate `ρ(v)` for the relators and for the words
   of length ≤ r, together with the differences `ρ(g)−ρ(h)`, `g ≠ h ∈ B(r)`.
2. The periodic models `Φ(Σ f_ju^j) = Σ D_y(f_j)P^j`, applied entrywise with large window and period, preserve the
   list and keep its nonzero elements nonzero (required claim).
3. `π(s) = Φ(ρ(s))` kills every relator, so it defines a homomorphism of `Γ` into `GL_(mN)(F_2)`.
4. `π` is injective on `B(r)`.
5. `|j| ≤ w` gives the banding.
6. Linear orbit growth: `R_X` is simple, so the orbit representation on `⊕_Z F_2^m` is faithful, and each generator
   moves supports by at most `w`. Artifact §2–§3.
