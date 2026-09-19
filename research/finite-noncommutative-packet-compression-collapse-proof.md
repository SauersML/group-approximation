---
rg: 2
id: finite-noncommutative-packet-compression-collapse-proof
kind: route
title: Exactify the packet, self-normalize by displacement rank, and transport the primitive
target: finite-noncommutative-packet-compression-collapse
requires:
  - finite-group-corona-tail-exactification
  - finite-packet-covariance-polar-correction
  - scaled-kazhdan-transport
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
  - GroupApproximation/Sofic/ScaledKazhdanTransport.lean
  - GroupApproximation/Sofic/InvolutionRankMass.lean
---

Choose a finite symmetric generating set `S` of the finitely generated Kazhdan source.  Tail
exactification gives exact coordinate representations `V_n` of the finite
packet.  For each `a in S`, compare `Ad(U_(a,n)) V_n` with the exact packet
automorphism induced by `a`; finite averaging and polar decomposition replace
`U_(a,n)` by `Uhat_(a,n)=z_(a,n)U_(a,n)`, with `z_(a,n)->1`, so covariance is
exact.

Put `b_n(g)=V_n(gkg^(-1))-V_n(k)` and
`w_n=sum_(a in S) rank b_n(a)`.  If the mark survives, pass to a subsequence
with `w_n>=1`.  Because the packet is fixed and finite, nonzero singular values
of all generator differences have a common positive floor `eta`, hence

```text
sum_a ||b_n(a)||_2^2 >= eta^2 w_n.
```

Exact covariance plus rank subadditivity gives
`rank b_n(g)<=|g|_S w_n`, hence every fixed cocycle value has `O(w_n)`
Frobenius mass.  The weighted Hilbert ultraproduct therefore carries the
adjoint representation of the ambient group and a genuine nonzero cocycle
`b|_L`.

Delorme property-(T) makes this cocycle a coboundary `b(g)=xi-Sigma(g)xi`.
The compressed subgroup fixes `k`, so `xi` is `sLs^(-1)`-fixed and
`zeta=Sigma(s)^(-1)xi` is `L`-fixed.  Diagonalize a representative of `zeta`
from ultrafilter invariance to cofinite scaled asymptotic commutation and
apply `ScaledKazhdanTransport.scaled_transport_both` at the weight `w_n`.
Its forward half says the representative of `xi=Sigma(s)zeta` is also
`L`-asymptotically invariant.  The coboundary identity then makes every
`b_n(a)` have `o(w_n)` mass, contradicting the displayed lower bound.

This route is a complete paper proof.  Its use of
`ScaledKazhdanTransport.scaled_transport_both` is kernel-checked; the new
finite-packet assembly described above is the remaining Lean translation
boundary.
