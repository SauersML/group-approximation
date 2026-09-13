---
rg: 2
id: exact-kazhdan-radical-kernel-cannot-be-lef
kind: claim
title: An exact Kazhdan MF-radical kernel over the integers is never LEF
distinct_from:
  mapping-torus-mf-radical-lies-in-finite-residual: That gives the algebraic finite-residual bound; this combines it with the Ozawa--Thom weak-quasidiagonality theorem and LEF-to-MF to exclude every nontrivial LEF Kazhdan kernel.
  simple-kazhdan-groups-have-full-mf-radical: That proves intrinsic full MF radical for simple Kazhdan groups; this needs no simplicity and instead proves that a no-finite-quotient Kazhdan group cannot be LEF.
  torsion-free-kazhdan-alternating-mother-limit-gate: That studies a particular family of finite marked quotients; this is the general obstruction which proves that its proposed simple/no-finite-quotient LEF limit cannot exist.
---

**Correction (2026-09-12).** The general statement (EKL2) below is **false**.
`lef-kazhdan-group-without-finite-quotients-exists` gives `EL_3(LC(X,F_q) ⋊ Z)`, for an infinite
minimal subshift `X`: an infinite LEF Kazhdan group with no nontrivial finite quotient. The step
"operator-MF implies weak quasidiagonality" fails (`operator-mf-group-not-weakly-quasidiagonal-exists`).
The proof route of this node was already invalidated by
`mf-to-weak-qd-citation-has-unproved-lifting-step`.

The mapping-torus statement (EKL1) is not refuted. It is **open**, and needs an argument that uses
more than "LEF plus Kazhdan plus no finite quotients". So the closing paragraph below does not
hold as written: marked limits of finite groups are not excluded as kernels by (EKL2), and the
alternating-mother branch is not closed by it.

Let `K` be a finitely generated property-`(T)` group, let `phi` be an
automorphism, and put

```text
G = K semidirectProduct_phi Z.
```

If

```text
Rad_MF(G) = K x {0},                                    (EKL1)
```

then either `K=1` or `K` is **not LEF**.  In particular, every nontrivial
kernel in the torsion-free exact-radical-over-`Z` target is necessarily a
sofic-but-non-LEF Kazhdan group.

The more general statement behind this is:

```text
a countable LEF property-(T) group with no nontrivial finite quotient
is trivial.                                               (EKL2)
```

Indeed, LEF implies operator-MF.  Dadarlat records that operator-MF implies
weak quasidiagonality, while Ozawa--Thom Proposition 3.19 says that every
infinite weakly quasidiagonal Kazhdan group has an infinite residually finite
quotient.  Such a quotient has a nontrivial finite quotient, contradicting
the hypothesis.  A finite nontrivial group is itself a nontrivial finite
quotient, so the only remaining possibility is the trivial group.

By `mapping-torus-mf-radical-lies-in-finite-residual`, `(EKL1)` forces `K`
to have no nontrivial finite quotient.  Applying `(EKL2)` proves the claim.

Consequently, no marked limit of finite groups can be the desired kernel:
every such limit is LEF.  This closes the alternating-mother branch outright.
It also shows that an explicit finite-permutation construction of the kernel
cannot proceed through exact local models; genuinely Hamming-approximate,
non-LEF sofic models are compulsory.

## Attempts

- **Via (EKL2) and Ozawa--Thom.** Dead. The route is invalidated, and (EKL2) is false (see the
  correction above).
- **What remains.** Any proof of (EKL1) must use the exact-radical structure of the mapping torus,
  not only the absence of finite quotients of `K`.
