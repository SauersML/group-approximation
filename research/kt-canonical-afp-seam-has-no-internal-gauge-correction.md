---
rg: 2
id: kt-canonical-afp-seam-has-no-internal-gauge-correction
kind: claim
title: The canonical Kun--Thom AFP seam cocycle has no coboundary inside the pasted crossed product
distinct_from:
  kt-c-normalization-seam-is-a-relative-commutant-cocycle: that gives the abstract coboundary equation in `R^omega`; this proves it has no solution in the canonical CE amalgam algebra itself.
  kt-full-actor-cocycle-loops-admit-exact-wreath-wall: that gives a coherent coboundary after passing to the exact non-CE wreath algebra; this shows the opposite behavior in the CE free-amalgam paste and locates the needed correction outside both vertex algebras.
  kt-c-normalization-is-the-first-finite-normalizer-seam: that proves individual seam words have trace zero; this excludes every nonzero simultaneous intertwiner, which is stronger than checking the traces of the words.
---

**ESTABLISHED INTERNAL NO-GO.**  Let

```text
M=R rtimes P_A,
P_A=H_A *_<A> S,
N=ker(P_A->G).                                          (KIN1)
```

In the `q=2` specialization,

```text
R' cap M=L(N).                                          (KIN2)
```

There is no nonzero `z in L(N)` satisfying

```text
z u_(C gamma C^(-1))=u_(alpha_C(gamma)) z
                                                (gamma in Gamma). (KIN3)
```

In particular no internal unitary gauge makes the cocycle `(KCC1)` a
coboundary.  The compatible AFP lift cannot be corrected to close the first
mixed seam while remaining inside its own crossed product.

This does not prove that the cocycle stays nontrivial in
`U(R' cap R^omega)`.  An embedding `M->R^omega` can have a much larger
relative commutant than `R' cap M`.  The positive Kun--Thom branch now has a
sharply localized requirement: manufacture in that **extrinsic** relative
commutant a unitary satisfying `(KIN3)`, while also preserving the external
`SL_3(Z)` relators.  Conversely a theorem that every such intertwiner lies
in (or is controlled by) `L(N)` would refute the normalizer lift and produce
the explicit nonhyperlinear finitary extension.

DERIVATION
kt-canonical-afp-seam-internal-no-go-proof
