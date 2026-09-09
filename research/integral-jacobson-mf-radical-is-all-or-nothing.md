---
rg: 2
id: integral-jacobson-mf-radical-is-all-or-nothing
kind: claim
title: Every MF homomorphism of the integral Jacobson elementary group is injective or trivial on the finitary special linear subgroup
distinct_from:
  binary-jacobson-mf-radical-dichotomy: that is the two-valued radical over the binary field, obtained from simplicity of the finitary kernel; this is the integral ring, whose finitary kernel has congruence quotients and is not simple, and the dichotomy comes instead from extracting a transvection and the trivial-or-infinite-order principle.
  integral-jacobson-elementary-group-is-not-mf: that is the open target; this is the theorem that whichever way it goes, the MF radical is either trivial or the whole finitary special linear group, so a single MF homomorphism nontrivial on one transvection would decide it.
  integral-jacobson-defect-has-no-normal-kazhdan-subgroup: that shows the criterion has no normal Kazhdan instance over the integral ring; this shows what its central infinite cyclic instance still forces.
  integral-jacobson-sign-quotient-is-residually-finite: that gives the upper bound on the radical and the residually finite quotient, consumed here; this is the lower alternative and the exclusion of every intermediate radical.
artifacts:
  - research/artifacts/jacobson-exact-torsion-radical-and-integral-dichotomy-2026-09-09.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED.**  Let `J = Z<s,t | ts = 1>`, `G_n = EL_n(J)`,
`N_n = SL_fin(Z)` its relative elementary subgroup
(`integral-jacobson-symbol-kernel-is-finitary-general-linear`).  For
every `n >= 4` and every homomorphism `phi : G_n -> M` with `M` MF,

```text
ker(phi) cap N_n = 1     or     N_n <= ker(phi).                        (AN1)
```

Consequently

```text
G_n is MF        or        Rad_MF(G_n) = SL_fin(Z),                      (AN2)
```

and no proper nontrivial intermediate MF radical is possible.  The
theorem does not decide which alternative holds; that is
`integral-jacobson-elementary-group-is-not-mf`.

**Reformulation.**  Since `Rad_MF(G_n) <= N_n` always
(`integral-jacobson-sign-quotient-is-residually-finite`), `(AN2)` says:
`G_n` is MF iff some MF homomorphism is nontrivial on the single
transvection `zeta = diag(1,1,1,1 + f_12)`, and by
`central-defect-element-mf-image-is-trivial-or-infinite` such an image
of `zeta` has infinite order.  So the integral question is exactly
whether one integral finitary transvection can be kept alive, with
infinite-order image, by an operator-norm approximate representation of
`G_4` whose restriction to the symbol part may be taken residually
finite.

**Contrast with the binary field.**  Over `F_2` the finitary kernel
`SL_fin(F_2)` is simple, so the dichotomy there is immediate.  Over `Z`
the kernel `SL_fin(Z)` surjects onto every `SL_fin(Z/m)`, so a priori an
MF homomorphism could kill a congruence subgroup and keep a finite
quotient; `(AN1)` excludes this, because any nontrivial kernel element
yields a transvection, hence a torsion image of the central defect
element `zeta`, which the criterion forbids.

Derivation: `integral-jacobson-mf-radical-is-all-or-nothing-proof`.
