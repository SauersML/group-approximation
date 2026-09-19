---
rg: 2
id: shulman-presentation-double-has-a-faithful-fold-trace-model
kind: claim
title: Shulman's presentation double has a faithful MF model whose trace kills the entire fold kernel
distinct_from:
  leavitt-presentation-double-fd-radical-is-fold-kernel: that computes what every exact finite-dimensional representation kills; this constructs an operator-norm faithful approximate model of the full double whose normalized trace nevertheless has exactly that folded behavior.
  common-padding-erases-julia-derivation-density: that proves one intrinsic rank density can be diluted; this identifies the complete limiting trace and shows norm faithfulness survives while every fold-kernel moment vanishes.
  shulman-presentation-double-witnesses-have-adjoint-normal-form: that extracts one Julia normal form with an operator-visible fold word; this proves that the same algebra-MF conclusion admits faithful coordinates whose trace is completely blind to every fold word.
---

**ESTABLISHED CONSTRUCTION-TRACE NO-GO.** In the Leavitt presentation-double
setup, put

```text
P=F *_K F,                    B=C*(P),
p:P->F                         (the fold).
```

Let `tau_F` be the canonical trace of the free group and define

```text
tau_fold=tau_F C*(p).                                      (SFT1)
```

Then `tau_fold` is an MF trace on `B`, and there is an asymptotically
isometric operator-norm MF model of the **whole** Shulman amalgam `B` whose
normalized traces converge to `tau_fold`.

Indeed, choose finite quotients of the residually finite free group `F`
whose regular characters converge pointwise to `tau_F`; composing their
exact representations with `C*(p)` gives MF-trace coordinates for
`tau_fold`.  Shulman's symmetric-amalgam theorem supplies independent
faithful MF coordinates for `B`.  Apply
`faithful-mf-models-realize-all-mf-traces`: repeat the folded trace block
with overwhelming multiplicity and retain one copy of the faithful Shulman
block.  The maximum norm still detects every nonzero element of `B`, while
the normalized trace converges to `(SFT1)`.

The faithful model may moreover be made **exactly equivariant under the
vertex swap**.  If `s` is the automorphism interchanging the two copies and
`Theta_n` is the model above, put

```text
Psi_n(a)=Theta_n(a) directSum Theta_n(s(a)).             (SFT1*)
```

The two-by-two block flip `J_n` then satisfies the exact coordinate identity

```text
J_n Psi_n(a) J_n^*=Psi_n(s(a)).                          (SFT1**)
```

Since `p s=p`, the folded trace is swap invariant, so `Psi_n` still induces
`tau_fold`.  Thus even imposing the most natural symmetry of Shulman's
symmetric double does not select a fold-visible trace.

The model also has the correct canonical trace on **both vertex copies**:

```text
tau_fold C*(i_0)=tau_F=tau_fold C*(i_1).                 (SFT1***)
```

Hence faithful norm approximation, exact swap covariance, and canonical
vertex marginals can all hold simultaneously while every mixed fold word is
trace-null.  The missing datum is genuinely a mixed moment, not a marginal
or symmetry condition.

For every `w in ker(p)`, this faithful model therefore satisfies

```text
tr((u_w-1)^*(u_w-1))->0.                                (SFT2)
```

By `leavitt-presentation-double-fd-radical-is-fold-kernel`, this kills the
entire nontrivial finite-dimensional radical of `P`.

Consequently neither faithfulness of Shulman's norm-corona embedding nor
the Julia construction, exact coordinate-level vertex-swap covariance, nor
canonical traces on both vertices selects a fold-visible trace.  More
generally,
`faithful-mf-models-realize-all-mf-traces` says that the traces obtainable
from faithful MF coordinates are exactly the MF traces already present on
`B`; construction language adds no smaller canonical subclass.  Proving
that some such trace sees a fold word is new trace data, not a consequence
of symmetric-amalgam MF permanence.

DERIVATION
shulman-faithful-fold-trace-model-proof
