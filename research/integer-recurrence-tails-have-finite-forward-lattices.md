---
rg: 2
id: integer-recurrence-tails-have-finite-forward-lattices
kind: claim
title: Finitely many eventually integral recurrence tails admit a faithful finite-rank forward lattice with injective shift
artifacts:
  - research/artifacts/beyond-polynomial-germs/recurrence-and-matrix-proofs.md
---

For finitely many eventually integral rational constant-coefficient
recurrence profiles, including `1`, choose a common sufficiently late
cutoff and remove zero-root transients. The ℤ-span `L` of their actual
forward shifted tails is finitely generated free abelian, embeds in the
group of germs, satisfies `σL⊂L` with injective `σ`, and the full
positive/negative shift group is `⋃_(j≥0)σ⁻jL`. The same construction
can include finitely many profiles from both ends of bilateral sequences,
viewed as functions of one forward index.

## Attempts

The artifact's Section 2 embeds `L` in `ℤ^d` by the first `d` values
of a common recurrence with nonzero extreme coefficients; backward
propagation excludes nonzero eventually-zero tails. This is a concrete
submitted proof pending review. The statement concerns the selected
forward span, not all eventually integral solution germs, which can
contain `ℤ[1/2]`. No incoming proof route is added until the cutoff,
integral lattice and exact direct-limit claims have been checked.
