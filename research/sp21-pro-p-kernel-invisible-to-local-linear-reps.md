---
rg: 2
id: sp21-pro-p-kernel-invisible-to-local-linear-reps
kind: claim
title: Every continuous representation of the pro-p completion of an Sp(n,1) lattice subgroup over a local field has finite image on the pro-p congruence kernel
distinct_from:
  sp21-lattice-positive-characteristic-images-finite: that removes infinite linear images of the lattice itself over fields of positive characteristic; this concerns continuous representations of the pro-p completion over local fields of every characteristic, and bounds them on the congruence kernel
  sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel: that shows a finite-rank completion has finite kernel; this shows every local-field linear quotient of the completion sees only a finite part of the kernel, whatever its rank
artifacts:
  - research/artifacts/sp21-torsion-growth-certificate-shape-2026-09-12.md
---

**ESTABLISHED.** Setting:
- `Γ`, `p` and `Γ(p)` are as in
  `sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`;
- `Δ <= Γ(p)` has finite index;
- `N = ker(Δ̂_p ->> Δ̄_p)` is the pro-p congruence kernel;
- `F` is a local field, of any characteristic and residue characteristic;
- `ρ: Δ̂_p -> GL_m(F)` is continuous.

Then `ρ(N)` is finite.

**Consequence for Gromov's question.**
- An infinite pro-p congruence kernel admits no faithful continuous linear
  representation over a local field.
- So infinite rank of `Δ̂_p` (failure of the congruence subgroup property at `p`)
  cannot be witnessed by any continuous linear quotient of `Δ̂_p` over a local
  field.
- Any Golod–Shafarevich witness for the open claim
  `sp21-lattice-pro-p-completions-have-finite-rank` must be non-linear in this
  sense.

**Proof** (route `sp21-pro-p-kernel-invisible-to-local-linear-reps-proof`, artifact
§4), in three cases:
1. **Positive characteristic.** `ρ|_Δ` has finite image by
   `sp21-lattice-positive-characteristic-images-finite`, and `Δ` is dense in
   `Δ̂_p`.
2. **Characteristic 0, residue characteristic `ℓ != p`.** A compact pro-p subgroup
   of `GL_m(F)` meets an open pro-ℓ subgroup trivially, so it is finite.
3. **Characteristic 0, residue characteristic `p`.**
   - The image `P_2` of `(π, ρ)` in `Δ̄_p × ρ(Δ̂_p)` has finite rank and contains
     `Δ` densely.
   - The proof of Theorem A in `research/artifacts/hyperbolic-rf-pro-p-2026-09-12.md`
     applies verbatim to `(P_2, pr_1)`. So `ker(pr_1) ≅ ρ(N)` is finite.

**Trust surface.** Case 3 carries Theorem A's conditions:
- Margulis's arbitrary-field superrigidity with no boundedness hypothesis;
- Raghunathan vanishing.

`research/artifacts/review-backlog-2-2026-09-12.md` §14 passes Theorem A under
exactly that form. Case 2 uses no superrigidity, and case 1 uses only
`sp21-lattice-positive-characteristic-images-finite`.

No novelty claimed.
