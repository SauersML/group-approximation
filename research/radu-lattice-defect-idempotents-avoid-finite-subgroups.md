---
rg: 2
id: radu-lattice-defect-idempotents-avoid-finite-subgroups
kind: claim
title: Over every F_p, idempotents on finite subgroups of Radu's lattice give no corner witness and no stable-finiteness defect
distinct_from:
  radu-bmw-lattice-has-no-invariant-output-injective-automata: that excludes injective automata with output symmetry over any alphabet; this excludes linear corner witnesses and defect idempotents built on finite-subgroup algebras, in every characteristic.
artifacts:
  - research/artifacts/radu-lattice-binary-algebra-splittings-2026-09-12.md
---

**ESTABLISHED** by `radu-lattice-defect-idempotents-avoid-finite-subgroups-proof`.

The finite subgroups of Radu's BMW lattice `Gamma_R` have order at most four. The order-four ones are
conjugate to the Klein groups `<a,x>`, `<a,y>` and `<b,x>`, and every finite subgroup injects into
`Gamma_R^ab = (Z/2)^3`. Let `p` be any prime and `H` any finite subgroup.
1. **No corner witness.** If `e in M_m(F_p[H])` is idempotent and `C e B = I_m` over `F_p[Gamma_R]`,
   then `e = I_m`.
2. **No finite-subgroup defect.** If `B A = I_n != A B` over `M_n(F_p[Gamma_R])`, the defect idempotent
   `I_n - A B` is not conjugate into `M_n(F_p[H])`.

For `p = 2` the augmentation does the work, since `F_2[H]` is local. For odd `p`, characters of `Gamma_R`
extending the characters of `H` do.
