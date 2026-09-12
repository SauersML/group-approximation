---
rg: 2
id: full-label-chord-normalization-kills-the-hilbert-hotel
kind: claim
title: Full-label chord normalization kills the Gram spectator and the Hilbert-hotel return together
artifacts:
  - research/artifacts/full-label-chord-normalizer-dichotomy-2026-08-21.md
distinct_from:
  translation-reset-leaves-a-compressed-gram-spectator: that constructs the saturated residual Gram when the chord is unconstrained on the scalar reset multiplicity; this tests the most direct mixed chord--reset constraint and proves that it overcorrects.
  two-fixed-packet-reynolds-actions-leave-a-gram-spectator: that concerns invariance of the Gram under packet averaging; this imposes ordinary group-word covariance on the chord itself and classifies its exact normalizer fiber.
  functorial-packet-return-firewall: that rules out every functorial construction of the proper return using the regular trace; this gives the explicit finite-label normalizer mechanism and a dimension-free defect floor on the saturated escape.
---

Let a fixed negative-central-character reset label act on `V`, and let its
group-algebra image contain projections `H_0<=E_0`.  Put

```text
d=dim(V),       r=rank(E_0),       s=rank(H_0),
0<s<r,          F_0=E_0-H_0.                              (FNC1)
```

The most direct mixed constraint is to make the chord `U` commute with a
finite group-word menu spanning the full reset label algebra.  Equivalently,
one may impose

```text
[U,w]=1                 (w in W),                         (FNC2)
```

where `W` is a fixed finite Weyl/reset group whose selected representation
spans `End(V)`.  In every amplification `V tensor K`, `(FNC2)` forces

```text
U=I_V tensor U_K.                                      (FNC3)
```

Consequently, for `E=E_0 tensor I`, `H=H_0 tensor I`, `F=E-H`, and
`X=FUE`,

```text
X^*X=F,                    E-X^*X=H.                    (FNC4)
```

Thus `(FNC2)` removes the residual projection `E_0 tensor Q`, but it also
makes source fullness impossible in a properly infinite amplification:
the finite label rank deficit survives unchanged even though the external
multiplicity is infinite.

There is a dimension-free quantitative obstruction on the saturated model
of `translation-reset-leaves-a-compressed-gram-spectator`.  Let

```text
q=E_0 tensor Q,          rank(Q)/N=s/r,
h=s/d,
D_W(U)^2=|W|^(-1) sum_(w in W)||[U,w]||_2^2.            (FNC5)
```

Then

```text
D_W(U)^2 >= (h/4)(1-s/r)>0.                             (FNC6)
```

Indeed Weyl averaging is the conditional expectation onto
`I_V tensor M_N`, and

```text
||q-H||_2^2=2h(1-s/r).                                  (FNC7)
```

Polarizing the conditional expectation of `U` gives a commutant unitary
within twice the expectation distance, while the compressed Gram is
`2`-Lipschitz in `U`.  This yields `(FNC6)`.  Hence `(FNC2)` is a concrete
finite ordinary-word test with a dimension-independent floor on the exact
saturated spectator.

The same dichotomy covers a third transverse fixed chart.  If fixed label
algebras `A_1,...,A_k` jointly generate `End(V)` and the chord is required to
implement prescribed automorphisms on all of them, then any implementer has
the form

```text
U=u_0 tensor U_K.                                      (FNC8)
```

The multiplicity gauge `U_K` remains, but cancels from every compression
Gram built from label projections.  No residual `Q` survives; equally, no
proper Hilbert-hotel isometry from a larger finite label cut to a smaller
one survives.

Full generation is stronger than necessary for this negative conclusion.
If the charts generate a fixed algebra `C` containing `E_0,F_0` and their
covariance forces `U^*F_0U` back into `C`, then the Gram is localized in
`C`, but the induced finite-label automorphism preserves ordinary matrix
rank.  Since `rank(F_0)<rank(E_0)`, exact source fullness is again impossible
in every amplification.  If the covariance does not control the support
cuts in this way, it has not authenticated the Gram and leaves a relative
commutant gauge available.

Therefore neither side of this fixed-chart normalizer dichotomy closes the
Fanizza cell.  The remaining mixed relation must be sensitive to the scalar
multiplicity coordinate in finite matrices while **not** forcing the chord
into the normalizer of a fixed finite label algebra in the exact infinite
marked representation.
