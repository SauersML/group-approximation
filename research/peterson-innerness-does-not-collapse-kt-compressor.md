---
rg: 2
id: peterson-innerness-does-not-collapse-kt-compressor
kind: claim
title: Peterson innerness does not upgrade the Kun--Thom compressor to a normalizer
distinct_from:
  approximate-collapse-for-kt-compressor: that asks for compressor collapse in arbitrary matrix-ultraproduct representations; this proves that Peterson's factorial-relative-commutant innerness theorem cannot establish it, even in the exact self-ultrapower model.
  kt-compressor-pair-group-factor-ultrapower-has-no-leak: that proves relative-commutant equality in the actor's own group-factor ultrapower; this uses that theorem to calibrate, and rule out, a proposed deformation-rigidity shortcut.
  factorial-commutant-regular-embeddings-are-congruence: that is an open classification of extreme matrix-ultraproduct embeddings; this concerns only the logical output of Peterson Theorem 5.2 for an already coordinatewise-inner compressor automorphism.
---

**ESTABLISHED.**  Take the Kun--Thom Theorem E pair with `q=2`,

```text
Gamma = EL_r(F_2[x_1,...,x_d]) <
G = EL_r(F_2[x_1^(+-1),...,x_d^(+-1)]) rtimes SL_d(Z),
```

and a positive strict compressor `t`, with

```text
Lambda=t Gamma t^(-1)<Gamma.                            (PIC1)
```

Put `B=L(G)`, `M=L(Gamma)`, and regard `M` as the constant subfactor of
`B^omega`.  Then:

1. `M` is a property-`(T)` factor;
2. its relative commutant in `B^omega` is scalar,

   ```text
   M' cap B^omega = C;                                  (PIC2)
   ```

3. the constant coordinate automorphisms

   ```text
   alpha_n=Ad(u_t) in Aut(B)                            (PIC3)
   ```

   lie in the connected component of the identity;
4. nevertheless

   ```text
   alpha(M)=L(Lambda)<L(Gamma)=M                         (PIC4)
   ```

   is a proper inclusion.

Consequently Peterson, arXiv:2605.16669, Theorem 5.2 applies to this exact
configuration and concludes only that `alpha|M` is implemented by a unitary
of `B^omega`.  The conclusion is already witnessed by the constant unitary
`u_t`.  It does **not** say that the implementer belongs to `M`, that it
normalizes `M`, or that `alpha(M)=M`.  In particular, factoriality of the
relative commutant does not turn the one-sided Kun--Thom compression into the
relative-commutant collapse needed by `kt-centralizer-normalization-hs`.

There is an exact algebraic reason no refinement of the implementing unitary
inside the theorem's conclusion can help.  If `u` implements `alpha|M`, then
all other implementers are precisely

```text
u U(M' cap B^omega).                                    (PIC5)
```

Indeed, two implementers differ by a unitary commuting with `M`, and the
converse is immediate.  Multiplication by such a commutant unitary leaves the
range algebra unchanged:

```text
(uc) M (uc)^* = u M u^* = alpha(M).                     (PIC6)
```

In the scalar-commutant calibration `(PIC2)`, even this freedom is only a
phase.  Thus Peterson's theorem is not merely quantitatively too weak here;
its entire conclusion is orthogonal to the missing surjectivity.

This does not refute `approximate-collapse-for-kt-compressor`.  It removes a
specific proposed proof mechanism.  A positive argument must use information
which compares the *range* `alpha(M)` with `M` inside a matrix ultraproduct --
for example approximate congruence collapse, a Cartan/coordinate carrier, or
an equivalent source-specific control of the ambient bimodule.  Factorial
relative commutant plus coordinatewise innerness supplies none of these.

DERIVATION
`peterson-innerness-kt-calibration-proof`
