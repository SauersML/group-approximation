---
rg: 2
id: tfd-deck-gap-is-morita-neutral-to-a-rectangular-qutrit-head
kind: claim
title: The finite-deck TFD gap tensorizes past a trace-one-eighteenth rectangular head
artifacts:
  - research/tfd-deck-gap-and-qutrit-bimodule-tensor-countermodel-proof.md
distinct_from:
  tfd-tensorization-gaps-every-finite-deck-packet: that proves the complete return Laplacian is uniformly coercive away from the normal fixed space; this shows that the normal fixed space may carry an arbitrary finite multiplicity cokernel
  raw-root-hecke-gap-is-blind-to-qutrit-one-over-eighteen-cokernel: that tensors the two-root Hecke carrier with the qutrit regular bimodule; this tensors the fixed arithmetic deck-gap theorem with the same bimodule
  finite-same-trace-tags-have-a-commutant-or-absorber-dichotomy: that classifies the finite tag itself; this proves that the new arithmetic TFD selector does not remove its commutant alternative
---

Let `Gamma` have property `(T;FD)`, let
`Lambda triangleleft Gamma` have finite index, and let the complete
Schreier-return Laplacian be the one in `(FDP3)`. Let `F` be a finite
group and let `q in C[F]` be a self-adjoint projection of regular trace
`alpha`.

There is an exact finite-dimensional rectangular occurrence with target
head density `alpha` which satisfies simultaneously:

~~~text
- every Gamma/Lambda relation and every complete Schreier return;
- full left-F covariance;
- TS=I, ST=I-Q, QS=0, and TQ=0;
- Q=I tensor R(q), where R(q) is right multiplication by q.
                                                               (TDQ1)
~~~

In particular, every return energy in `(FDP4)` is exactly zero, while

~~~text
tr(Q)=alpha.                                                 (TDQ2)
~~~

For the abelian qutrit head torus
`B=<H> times C`, `|B|=18`, and `q=Ee_b), left and right
multiplication agree and `alpha=1/18). Thus the head is the literal
qutrit atom. For the full finite head group
`F_0=<C,H,C_1,W>`, `|F_0|=288`, right multiplication gives the
full-`F_0)-covariant commutant copy of the same rank-sixteen atom.

More generally, tensoring any finite-dimensional `Gamma)-representation
with a finite multiplicity space gives

~~~text
L_ret(pi tensor I)=L_ret(pi) tensor I,
P_Lambda(pi tensor I)=P_Lambda(pi) tensor I.              (TDQ3)
~~~

Hence the property-`(T;FD)` inequality is sharp and unchanged, but it
contains no term which can see a projection in the multiplicity factor.

Consequently the new finite-host deck gap cannot be composed formally
with a finite qutrit tag, a finite Hecke gap, or safe rectangular
covariance to kill the Jacobson head. Such a juxtaposition has the exact
finite model above. A successful composition must add one genuinely mixed
nonfinite relation whose compression acts on the equality router or on the
multiplicity factor. The concrete endpoint cubics might do this; no such
estimate is proved here. The non-hyperlinearity root remains open.

DERIVATION
tfd-deck-gap-and-qutrit-bimodule-tensor-countermodel-proof
