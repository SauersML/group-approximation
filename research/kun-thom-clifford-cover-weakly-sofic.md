---
rg: 2
id: kun-thom-clifford-cover-weakly-sofic
kind: claim
title: The Kun--Thom Clifford cover is weakly sofic and not sofic
distinct_from:
  weakly-sofic-not-sofic: That is the separation statement, witnessed by the plain Z/2-lamp wreath; this is the same permanence argument applied to the Clifford central cover, which is the group whose hyperlinearity is this graph's Q3.4 target, and it additionally realizes the anticommuting Clifford wall.
  invariant-graph-clifford-phase: That classifies the central lamp quotients and computes the image of the marked word in them; this adds an approximation property of one such quotient and draws the consequence for the wall.
  kun-thom-clifford-radical-phase: That is the algebraic detector, an exact phase computation in the Clifford crossed product; this is an approximation property of the Clifford cover group, proved from a permanence theorem, and says nothing about the phase.
  kun-thom-clifford-crossed-product-ce: That asks whether the Clifford crossed product is Connes embeddable, i.e. whether the cover is hyperlinear, and is open; this proves the strictly weaker approximation property of weak soficity, which does not bear on hyperlinearity.
  kun-thom-clifford-relative-wall: That is the open normalized-Hilbert--Schmidt construction target; this proves that its algebraic content is already realized in the bi-invariant-metric category, which is why it calibrates rather than solves that target.
  kun-thom-clifford-extension-not-weak-mf: That is a negative operator-norm result about the same group, saying it has no matrix microstates in the MF sense; this is a positive result in the disjoint category of finite groups with bi-invariant metrics, where no matrix norm is involved at all, so the two coexist and together separate the two approximation classes on one explicit group.
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

Let `Gamma<G` be the Kun--Thom Theorem E pair, `S` a `G`-invariant graph on
`X=G/Gamma` with `b_S(o,y)=1`, `Vtilde_S` the central `F_2`-extension of
`directSum_X F_2` with commutator form `b_S`, and `E_S=Vtilde_S semidirect G`.
Then `E_S` is **weakly sofic** and **not sofic**.

`Vtilde_S` is locally finite, hence sofic; `E_S/Vtilde_S=G` is residually
finite; Glebsky's permanence theorem applies.  Nonsoficity is the established
radical phase: the marked word `x` lies in `Rad_sof(H)` and maps to `z!=1`.

**Consequence for Question 3.4.**  Composed with the established
`hilbert-embeddable-length-hyperlinearity`, this makes the Clifford cover a
proven member of the family targeted by
`hilbert-embeddable-witness-for-kun-thom-wreath`: if the Glebsky witnesses for
`E_S` have conditionally negative definite lengths, then `E_S` is hyperlinear
and nonsofic.  The composite models are HS-almost-multiplicative but need not
be operator-norm almost multiplicative, since a unitary of trace near one may
have eigenvalues near `-1` on a corner of vanishing rank; that is exactly the
defect profile required by `wall-models-avoid-norm-microstates`, so the two
routes are consistent.

**Consequence for the wall.**  Since the wall normal form
(`relative-wall-commutant-growth`) is a statement about an arbitrary target
group, the full Clifford wall -- an involution centralizing
`pi(t Gamma t^(-1))` whose `Gamma`-conjugate anticommutes with it -- is
realized in a metric ultraproduct of finite groups with bi-invariant metrics,
with the radical word surviving.  Hence **no purely group-theoretic argument
can refute the wall**: every no-go must use the metric.  The growth index of
`compressor-growth-index-homomorphism` is such a tool, since it needs a trace
and a Pimsner--Popa index that a metric ultraproduct of finite groups does
not carry.
