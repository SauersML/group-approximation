---
rg: 2
id: deligne-central-radical-from-opnorm-sector-emptiness
kind: route
title: Spectrally cut the order-three central image into Maslov sectors
target: deligne-triple-cover-central-generator-is-mf-radical
requires:
  - deligne-nontrivial-maslov-opnorm-sectors-are-empty
---

Let `Theta:E_3 -> prod U(d_n)/directSum U(d_n)` be a norm-corona
homomorphism.  Exact functional calculus in the corona splits the image of
the central order-three unitary into its `1,omega,omega^2` spectral
projections.  Centrality makes these reducing projections for the image of
`E_3`.  A nonzero `omega` or `omega^2` corner, lifted coordinatewise after
the standard order-three spectral correction, produces a pointwise
operator-norm asymptotic projective representation of `Sp_4(Z)` with the
corresponding nontrivial Maslov multiplier.  The required claim excludes
both corners.  Hence `Theta(z)=1`; as `Theta` was arbitrary, `z` lies in the
MF radical.

Conversely, any such projective point-norm model lifts the defining central
extension to a norm-corona homomorphism with `z` equal to the corresponding
nontrivial scalar.  Thus the required sector-emptiness claim is not a
weaker hidden substitute: it is exactly the central MF-radical gate.

