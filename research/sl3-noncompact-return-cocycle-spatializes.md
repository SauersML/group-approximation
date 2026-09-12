---
rg: 2
id: sl3-noncompact-return-cocycle-spatializes
kind: claim
title: The compressed noncompact lattice returns spatialize coherently over one profinite-corner embedding
distinct_from:
  sl3-homogeneous-quotient-crossed-product-is-connes-embeddable: that is stated as embeddability of the original homogeneous crossed product; this is the concrete finite-corner condition on one embedding and the full twisted return equations, equivalent by the established cocycle-spatialization theorem.
  free-lattice-ce-is-joint-ultrapower-spatialization: that rank-one criterion has freely chosen generator implementers and no relator equations; this requires the cocycle multiplier and every relation of the higher-rank cocompact lattice to close in one relative commutant.
---

For the dyadic `SL_3` data, the finite profinite corner `B`, cocycle action
`(beta,c)`, and cocompact lattice `Lambda'` of
`sl3-homogeneous-ce-is-common-cocycle-spatialization`, there exist one
trace-preserving embedding `pi:B->R^omega` and unitaries
`U_g in R^omega`, `g in Lambda'`, satisfying both equations `(HCS3)`.

Equivalently, after choosing a finite presentation of `Lambda'`, all
noncompact return automorphisms are spatial over one copy of `B` and the
resulting relative-commutant multiplier satisfies the finitely many twisted
relator equations.  Separate cyclic spatializations do not establish this
claim.

## Audited assembly attempts

- **Residual finite orbit blocks.**
  `sl3-lattice-returns-have-no-canonical-rf-or-free-assembly` proves that the
  right-lattice action is faithful in `Out(Q)`.  A block labelling over a
  finite quotient `Lambda'/H` would have to identify `alpha_g` and
  `alpha_(gh)` up to an inner coordinate change, forcing `alpha_h` inner.
  Thus no nontrivial residual quotient gives an exact canonical orbit sum,
  even after finite amplification.  A noncanonical ultrapower embedding may
  still spatialize those kernel returns; that is exactly the claim here.
- **Free or amenable assembly.**  Every single cyclic return crossed product
  is embeddable by amenable permanence, but the cocompact lattice has
  property (T), hence property FA, and admits no Bass--Serre decomposition
  into those cyclic pieces.  Individual spatializations therefore have no
  free-generator universal property with which to assemble their
  implementers.
- **Untwist only the compression cocycle.**  Replacing the comparison
  partial isometries by `v'_g=b_gv_g`, `b_g in U(B)`, changes the cocycle
  action by

  ```text
  beta'_g=Ad(b_g) beta_g,
  c'(g,h)=b_g beta_g(b_h)c(g,h)b_(gh)^*.
  ```

  Thus making `c'=1` is exactly a nonabelian coboundary problem.  Even a
  solution only converts `(HCS3)` into the requirement that the resulting
  honest action `beta'` be spatial over one embedding `pi`; it supplies no
  such embedding or implementers.  Cocycle untwisting alone therefore does
  not prove the claim.
