---
rg: 2
id: klingen-rational-twisted-fibres-fail-llp
kind: claim
title: Every rational Klingen fibre C*(Z^2 x| SL_2(Z), sigma_{p/q}) of Sp4(Z) contains C*(Z^2 x| SL_2(Z)) as a conditionally expected subalgebra, so fails the LLP
distinct_from:
  sp4-mod3-twisted-fibres-have-llp: that is the mu_3-twisted algebra of the whole lattice Sp_4(Z) from Deligne's triple cover; this is about twisted algebras of the quotient Z^2 x| SL_2(Z) of the Klingen subgroup E by its long-root centre Z.
  metaplectic-half-shift-preserves-twisted-fibre-llp: that is a permanence statement between Maslov twisted fibres of Sp_4(Z); this is a structural failure statement for every rational fibre of the Klingen extension Z -> E -> Z^2 x| SL_2(Z).
  e6-llp-reduces-to-base-plus-one-odd-fibre: that reduces LLP of a finite Deligne cover to Maslov fibres of Sp_4(Z); this shows the fibrewise sufficient condition is unavailable for the infinite-centre Klingen extension.
  klingen-central-quotient-is-min-inexact: that is inexactness of the quotient sequences after tensoring with B(l^2); this is a conditional expectation from a rational fibre onto an untwisted copy of C*(Z^2 x| SL_2(Z)).
  klingen-twisted-fibres-all-fail-llp: that is failure of the LLP at every fibre (rational or not), by a twisted ISW max/min estimate; this is the stronger structural statement at rational fibres only, namely that the untwisted C*(Z^2 x| SL_2(Z)) sits inside A_{p/q} with a ucp conditional expectation.
  sp2g-z-full-c-star-algebra-has-llp: this is a fence on the Farah--Fritz--Winter fibrewise route, not a decision of the root.
artifacts:
  - research/artifacts/klingen-central-quotient-2026-09-16.md
---

**CLAIM.**  Let `E = Z x_c Lambda <= Sp_4(Z)` be the Klingen extension of
`Lambda = Z^2 x| SL_2(Z)`, with `c((v,g),(w,h)) = omega(v, g w)`
(`klingen-central-quotient-is-min-inexact`; artifact §0).  For `t in R` let
`A_t = C^*(Lambda, exp(2 pi i t c))`.  This is the fibre of the `C(T)`-algebra
`C^*(E)` at `u_z = e^{2 pi i t}` (Packer–Raeburn; Farah–Fritz–Winter
arXiv:2603.18456v2, Proposition `c ext struct`).  Then:

```text
for every rational t = p/q, A_t contains a copy of C^*(Lambda_q), where
Lambda_q = qZ^2 x| SL_2(Z) is isomorphic to Lambda, as the range of a ucp
conditional expectation.  In particular A_t does not have the local lifting
property.
```

**Proof idea.**  On the index-`q^2` subgroup `Lambda_q`, the cocycle is
`t c = pq omega(v, g w)`, an integer, so the twist is identically `1`.

- The standard conditional expectation `C^*(E) -> C^*(E_q)`, onto the preimage
  `E_q` of `Lambda_q`, is `C^*(E_q)`-bimodular.
- So it maps `(u_z - zeta) C^*(E)` into `(u_z - zeta) C^*(E_q)`, and descends to a
  ucp retraction of `A_t` onto a copy of `C^*(Lambda_q) = C^*(Lambda)`.
- `C^*(Lambda)` fails the LLP (Ioana–Spaas–Wiersma, arXiv:2006.01874,
  Corollary B), and the LLP passes to ranges of ucp conditional expectations.

**Relation to the all-fibres statement.**  The failure of the LLP holds at every
`t in R` (`klingen-twisted-fibres-all-fail-llp`, artifact §4A).  What this node
adds at rational `t` is the conditional expectation onto the untwisted algebra.
So every property that passes to conditionally expected subalgebras, and fails
for `C^*(Z^2 x| SL_2(Z))`, also fails for `A_{p/q}`.

**Consequences.**

- Farah–Fritz–Winter Corollary `c ext` ("all fibres LLP implies `C^*Gamma` LLP")
  is never applicable to `(E, Z)`.
- No LLP proof for the root can go through Klingen fibres, since `C^*(E)` is a
  conditionally expected subalgebra of `C^*(Sp_4(Z))`.
