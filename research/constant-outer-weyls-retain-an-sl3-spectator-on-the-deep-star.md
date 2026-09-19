---
rg: 2
id: constant-outer-weyls-retain-an-sl3-spectator-on-the-deep-star
kind: claim
title: Full constant-outer SL3 relations retain a nontrivial S3 spectator on the deep star atom
artifacts:
  - research/constant-outer-weyl-sl3-spectator-proof.md
distinct_from:
  two-head-square-cubes-split-outer-and-middle-gauges: that gives an `S_3 times GL_3(F_2)` product model for the two reduced cube loops; this shows that even adjoining every relation of the larger constant outer `SL_3(F_2)` cannot authenticate its `S_3` inertia action on the deep atom.
  same-center-pauli-actors-have-whitehead-sign-quotient: that twists the two prefix Whiteheads by the scalar sign character of their internal `S_3`; the full constant outer group `SL_3(F_2)` is simple and has no such character, but its regular representation still supplies a nontrivial multiplicity gauge on the `S_3` inertia subgroup.
  marked-star-outer-corrected-whiteheads-are-quarter-swaps: that proves the corrected words have conjugate reservoir gauges; this proves the constant outer Weyl factors in those words are not label-only on the deep star atom.
  head-square-whitehead-loop-preserves-deep-star-flag: that derives the odd loop and records the transition equation `(HSW5)`; this gives the promised exact finite spectator satisfying that equation with nonidentity right-hand gauge.
  finite-prefix-labelled-windows-remain-projective: that gives natural permutation models for consistently prefix-labelled root windows; this isolates the independent constant-outer quotient of the mixed marked-star/HSW relation packet.
---

**ESTABLISHED SCOPED FENCE.**  Let

```text
K=SL_3(F_2)                                             (OWS1)
```

be the constant elementary subgroup on the three outer marked-star
coordinates, and let

```text
S=<L_1,L_2><=K                                         (OWS2)
```

be its permutation-matrix subgroup.  Thus `S` is `S_3` and the two
constant outer Weyls are its adjacent transpositions.

Consider the finite ordinary-word relation packet used by the marked-star
construction and the head-square loop.  It contains:

1. the full finite multiplication relations of the constant outer `K`;
2. the literal marked/star Pauli commutator and covariance rows;
3. the prefix and asymmetric-head words `J_i,H_i,X_i`;
4. `U_i=L_iJ_i` and the two identities

```text
(X_iU_i)^3=L_i,                  (U_iX_i)^3=L_i.       (OWS3)
```

This scoped relation packet has a quotient

```text
q:Gamma_packet -> K                                  (OWS4)
```

which keeps every constant outer word and kills every named nonconstant
Leavitt root occurrence.  In particular

```text
q(L_i)=ell_i,       q(J_i)=q(X_i)=q(H_i)=1,
q(U_i)=ell_i.                                         (OWS5)
```

All marked/star rows become identities after the nonconstant roots are
killed.  The HSW rows remain valid because `ell_i^2=1`, so

```text
(q(X_i)q(U_i))^3=ell_i^3=ell_i=q(L_i),                (OWS6)
```

and similarly in the reverse order.  No coefficient product in this
packet produces a nontrivial constant outer root: its outputs are again
`q`, a prefix idempotent, or a prefix arm.  Thus `(OWS4)` respects the
entire displayed relation table, not only `(OWS3)`.

Let `lambda_K` be the left regular representation of `K`.  Tensor any
finite moving-chart realization of the marked/star packet by
`lambda_K o q`.  Since every involution defining the positive deep star
atom maps to the identity under `q`, that atom changes from `E` to

```text
E tensor I_(ell^2 K)                                  (OWS7)
```

and retains exactly the same positive normalized density.  On it,

```text
L_i=(outer label swap) tensor lambda_K(ell_i).         (OWS8)
```

The second factor is not the identity.  Restriction of the regular
`K`-module to `S` is `[K:S]=28` copies of the regular `S_3`-module, so the
two gauges are conjugate nontrivial involutions satisfying the braid.  More
quantitatively,

```text
tr_K(lambda_K(ell_i))=0,
||lambda_K(ell_i)-I||_op=2,
||lambda_K(ell_i)-I||_2^2=2.                          (OWS9)
```

In the extracted HSW transition equation, the spectator assignment is

```text
D_(X_i)=I,                 D_(U_i)=D_(L_i)=lambda_K(ell_i), (OWS10)
```

and three occurrences on the left multiply to the same involution on the
right.  Hence `(HSW5)` is exact while `D_(L_i)` and `D_(U_i)` remain
maximally nontrivial.

Therefore neither the finite `SL_3(F_2)` relations nor their coupling to
the literal marked/star rows authenticate the constant outer Weyl as a
label-only operator.  The fact that `SL_3(F_2)` has no sign quotient is
irrelevant: finite relations permit its regular multiplicity module.

This is intentionally a fence for the stated finite relation packet, not a
quotient of the full binary-Leavitt Steinberg group.  Full coefficient
saturation can express constant roots from nonconstant Leavitt data and is
not killed by `(OWS4)`.  A successful continuation must use precisely such
a coefficient-sensitive mixed occurrence on the same deep atom, or another
ordinary word which compares the actual `L_i` gauge with an identity-outer
gauge.  Adding more relations internal to the constant outer finite group
cannot do so.

No Property `(T)`, canonical trace, stability theorem, computation, or
literature input is used.

DERIVATION
constant-outer-weyl-sl3-spectator-proof
