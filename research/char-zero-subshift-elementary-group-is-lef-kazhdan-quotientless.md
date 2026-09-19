---
rg: 2
id: char-zero-subshift-elementary-group-is-lef-kazhdan-quotientless
kind: claim
title: EL_3 over the integer crossed product of a minimal subshift is LEF, Kazhdan and has no finite quotients, with root elements of infinite order
distinct_from:
  lef-kazhdan-group-without-finite-quotients-exists: that group is EL_3 over LC(X,F_q) x Z, in characteristic p, where every root element has order p; this is the characteristic-zero form over LC(X,Z) x Z, which surjects onto the prime-field form for every p and embeds in their product.
  finite-model-subshift-elementary-groups-simple-kazhdan-lef: that is the finite-field simple group; this group is not simple, since it has the congruence quotients, but still has no finite quotients.
  kazhdan-rational-relation-cover-reduction: that proves the reduction and the root-element obstruction (RE); this supplies a quotientless Kazhdan base where the premise of (RE) fails at every root element.
  torsion-free-lef-kazhdan-non-rf-seed: that seed is torsion-free with finite quotients; this group is quotientless but has torsion, like every elementary group of rank at least three.
artifacts:
  - research/char-zero-subshift-elementary-group-proof.md
  - research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md
  - research/lef-kazhdan-group-without-finite-quotients-exists.md
  - research/relation-cover-sofic-envelope-forces-trivial-kernel.md
---

**ESTABLISHED.** Proof: `char-zero-subshift-elementary-group-proof`.

**Setting.** `X` is an infinite minimal subshift over a finite alphabet, with shift `T`.
`R_0 = LC(X,Z) ⋊_T Z`, where `u f u^-1 = f ∘ T^-1`, and `Q_0 = EL_3(R_0)`.

**Statement.**
1. **(T).** `Q_0` has property (T).
2. **LEF.** There is an injective unital ring map `Ψ : R_0 -> prod_ω M_(N_k)(Z)`. Hence every
   finitely generated subgroup of `GL_3(R_0)` is LEF, and in particular `Q_0` is.
3. **No finite quotients.** `Q_0` has no nontrivial finite quotient.
4. **Congruence ideals.** Every nonzero two-sided ideal of `R_0` contains `d R_0` for some
   integer `d ≥ 1`. For each prime `p`, `R_0 / p R_0 = LC(X,F_p) ⋊ Z` is simple.
5. **Residual structure.** `Q_0` surjects onto `EL_3(LC(X,F_p) ⋊ Z)` for every prime `p`,
   and `Q_0` embeds in the product of these groups over all `p`. It is not simple.
6. **Roots and torsion.** Every root element `e_ij(r)`, `r != 0`, has infinite order.
   `Q_0` still has elements of order 2, e.g. `diag(-1,-1,1) ∈ EL_3(Z) ≤ Q_0`.

**What it does and does not do.**
- The group `Q_0` is a characteristic-zero input for the relation-cover program of
  `kazhdan-rational-relation-cover-reduction`. Consider a Kazhdan cover `P ->> Q_0` sending
  root elements to root elements. The premise of (RE), a root element of `P` mapping to
  prime order, never holds, so the characteristic-p kill of Attempt 2 of
  `relation-cover-rational-lifting-over-quotientless-kazhdan` does not apply. The torsion
  of `Q_0` is of Weyl, sign and unit type.
- `Q_0` has torsion. So by item 2 of `relation-cover-sofic-envelope-forces-trivial-kernel`,
  no cover over it satisfies both (RLT) and the permutation-module envelope. A cover over
  `Q_0` needs (RLT) at lifts of `diag(-1,-1,1)`-type elements, together with a soficity
  argument for `K` outside permutation-module envelopes.
- For (L2) of `torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical`, `Q_0` is a
  LEF quotientless Kazhdan kernel. Its standard automorphisms with inner powers all give LEF
  mapping tori, by `quotient-permuting-and-ambient-inner-mapping-tori-are-lef`.
