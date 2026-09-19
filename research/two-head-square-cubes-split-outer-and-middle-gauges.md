---
rg: 2
id: two-head-square-cubes-split-outer-and-middle-gauges
kind: claim
title: The two fixed-flag head-square cubes split into independent outer and middle actor gauges
artifacts:
  - research/two-head-square-cube-product-model-proof.md
distinct_from:
  constant-outer-weyls-retain-an-sl3-spectator-on-the-deep-star: that enlarges the outer `S_3` relations to the full constant `SL_3(F_2)` and retains a regular multiplicity gauge; this computes the sharper simultaneous two-cube product decomposition on one eighth atom.
  head-square-whitehead-loop-preserves-deep-star-flag: that constructs one odd corrected-Whitehead cube on an invariant positive flag and leaves its chart transition explicit; this combines both adjacent cubes on one eighth atom and proves that their shared braid does not cancel the transitions.
  moving-order-seven-stage-gauges-have-coboundary-drift: that uses seven moving cuts for one Singer actor and arbitrary stage charts; this has one fixed all-positive cut and gives an exact product-group factorization of the two simultaneous gauges.
  support-return-selector-occurrence-fence: that leaves independent signs on two transported support-Whitehead charts; this realizes the full two-row outer and middle actor groups on the same fixed star atom.
  binary-leavitt-two-shared-gauge-selector-compiler: that needs two odd rows to attach the conjugate corrected-Whitehead gauges to unequal selector occurrences; this proves that the two cube rows and both Coxeter braids still separate into independent actor factors.
---

On the three-cell positive marked-star carrier put

```text
Q_+++=E(1+Z_1)(1+Z_2)(1+Z_3)/8.                      (TSC1)
```

Every middle prefix root `X_i,Y_i,J_i`, every outer Weyl `L_i`, and every
outer-corrected word `U_i=L_iJ_i`, for `i=1,2`, reduces `Q_+++`.  Indeed the
middle roots act linearly on the three `Z` signs and fix their all-positive
character, while the outer Weyls fix the `Z` roots.

The two fixed-flag cube loops are

```text
(X_iU_i)^3=L_i,                 i=1,2,                (TSC2)
```

where `X_i=H_i^2`.  On `Q_+++`, the complete actor table splits as two
commuting factors:

```text
G_out=<L_1,L_2> ~= S_3,
G_mid=<X_1,Y_1,X_2,Y_2> ~= GL_3(F_2),
U_i=L_iJ_i,              J_i=X_iY_iX_i.               (TSC3)
```

Both `L_1,L_2` and `J_1,J_2` satisfy their Coxeter braids.  Consequently
the braid for `U_1,U_2` is the diagonal product of two independent braid
identities.  Substituting `(TSC2)` into the outer braid merely recovers the
middle braid; it gives no mixed odd-parity equation isolating either
`U_i`.

This independence has an exact finite common-carrier model of the complete
displayed `Z`-actor/cube table.  Use the regular representation of the
abelian sign group `<Z_1,Z_2,Z_3>` and tensor the canonical actor
implementers by

```text
lambda_(S_3) tensor lambda_(GL_3(F_2)).                (TSC4)
```

Assign `L_i` to left translation by `(ell_i,1)`, every middle word `g` to
left translation by `(1,g)`, and `U_i` to `(ell_i,J_i)`.  Every named `Z`
covariance, both cube relations, both factor braids, and the corrected
Whitehead braid hold exactly.  The all-positive character is fixed by the
canonical label actions, so `Q_+++` is nonzero and the restrictions there
are precisely the regular reservoir operators in `(TSC4)`.

In this model the two corrected gauges are nontrivial conjugate
involutions, while

```text
D_(U_i)D_(L_i)^(-1)=lambda_(1,J_i) !=1.               (TSC5)
```

Thus even on one fixed eighth atom, with zero leakage and both odd cube
loops present, the shared outer `S_3` braid cannot cancel the independent
middle actor gauge.  Any mixed product of the displayed relations projects
separately to the two factors in `(TSC3)`; cancellation in the outer factor
does not imply cancellation in the middle factor.

The remaining occurrence must therefore couple the two factors rather
than add another word internal to either one.  Concretely it must identify
one forked middle-root chart with an anchored outer chart in a way that is
not respected by the product model `(TSC4)`, while preserving at least the
quarter source atom.

This is a scoped exact finite model of the named sign/actor/cube table, not
of the omitted forked `A`-arm covariances and not a representation of the
full infinite Steinberg group.  Thus an additional full-packet occurrence
can still cross the fence, but the two cubes, common sign atom, and braids
alone cannot.  No Property `(T)`, Kazhdan input, canonical trace, heavy
computation, or literature theorem is used.

DERIVATION
two-head-square-cube-product-model-proof
