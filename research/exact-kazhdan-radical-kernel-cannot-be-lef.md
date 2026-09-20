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
- **Torsion-free repair of (EKL2) (calibration, 2026-09-18, swarm-0917-w13-titz-last1).**
  Summit-hard.
  - The repair: "a torsion-free LEF Kazhdan group without nontrivial finite quotients is trivial"
    (EKL2-tf).
  - Why it is summit-hard: by `hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan`, (EKL2-tf)
    implies that every torsion-free cocompact `Sp(n,1)` lattice has a non-residually-finite
    torsion-free hyperbolic quotient.
  - The mechanism: the Olshanskii--Osin--Sapir torsion-free Tarski monster over the lattice agrees on
    each finite ball with a hyperbolic stage. So if the stages are residually finite, the monster
    is LEF, and it is also Kazhdan and quotientless.
  - Which arguments die: every argument from intrinsic properties of `K` alone (torsion-free,
    Kazhdan, quotientless, sofic). It would answer Gromov's residual finiteness question.
  - What (EKL1) must use: `ψ`, finite presentation of `K ⋊_ψ Z`, or the exact radical.
- **Finite-image exact models add nothing beyond stage lifts (finite-models, 2026-09-19,
  swarm-0917-w19-titz-follow).** Class kill: `finite-image-exact-kazhdan-torus-models-reduce-to-stage-lifts`.
  - The setting: covariant corona models of `K ⋊_φ Z` whose kernel lifts are exact on a finite Shalom
    presentation `R_Γ` of a Kazhdan cover of `K` and have finite images. No spectral gap is assumed, and
    character fields and element orders are arbitrary (Weil or cuspidal representations, for example).
  - The mechanism:
    - a wrap of defect below `κ` forces an exact multiplicity-free wrap, so the stage automorphism is an
      isometry;
    - the Frobenius core `<{m : ‖m-1‖ < 1/2}>` is then abelian, normal and invariant;
    - dividing by it produces finite stage lifts of a `φ`-invariant quotient `K/N`.
  - The consequence: any such model that is nontrivial on `K` yields a LEF torus quotient `(K/N) ⋊ Z` with
    `N ≠ K`. So a proof of (EKL1) through finite-image exact models is no stronger than the combinatorial
    stage-lift criterion.
  - What (EKL1) must still use: infinite exact images, which are dense Kazhdan subgroups of compact
    semisimple groups (genuine representations of the finitely presented `G_Γ`), or lifts that are exact on no
    finitely presented Kazhdan cover. (EKL1) stays **open**.
- **Elementary kernels via the unit-torus radical (2026-09-19, swarm-0917-w14-titz-last1, family
  group-rings).** This gives a new refutation decomposition. (EKL1) stays OPEN.
  - Established: `unit-radical-saturates-elementary-mapping-torus`. For `K = E_n(S)`, `n >= 3`, with the
    entrywise `sigma`:
    - the MF radical of the unit torus `C semidirect_sigma Z` pushes into the first diagonal slot;
    - commutators with root elements put `c - 1` into a `sigma`-invariant level ideal of
      `Rad_MF(K semidirect Z)`;
    - so `E_n(S, I_C) <= Rad_MF`.

    If `I_C = S`, the radical is exactly `K x {0}`. `K` is then LEF whenever `S` is a LEF ring, and it is
    Kazhdan by EJK whenever `S` is finitely generated.
  - So (EKL1) is refuted by `lef-ring-with-saturating-unit-torus-radical`. That claim has two
    prerequisites, each of which can fail:
    - (Q1) a non-MF `Z`-extension of a LEF unit group of a finitely generated LEF ring;
    - (Q2) saturation of the ideal, which is automatic for `sigma`-simple `S`, or for minimal full-group
      units.
  - Class kills proved there:
    - rings with a nonzero finite quotient die at the finite residual, including residually finite
      rings and group rings (augmentation);
    - amenable `C` dies by TWW, which includes commutative units and minimal `Z`-subshift full groups;
    - `sigma` with a power inner in a LEF overring dies. Equivalently, the skew Laurent ring must not
      be LEF.
  - Unresolved:
    - (Q1) itself;
    - the dynamical instantiation with proper colourings of the `alpha`-orbit of a generating set, where
      the colouring graph has infinite degree and the obvious finite-model argument breaks;
    - whether the non-finitely-generated kernel of `mf-not-closed-under-integer-extensions` embeds
      `sigma`-equivariantly in the derived full group of a finitely generated LEF crossed product.
