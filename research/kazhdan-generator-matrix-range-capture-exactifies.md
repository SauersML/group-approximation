---
rg: 2
id: kazhdan-generator-matrix-range-capture-exactifies
kind: claim
title: Generator-level capture by the full group matrix range flexibly exactifies a Kazhdan microstate
distinct_from:
  kazhdan-weak-ucp-stability-is-flexible-stability: that starts with Dogon's global weak-ucp dilation hypothesis and identifies the resulting stability notion; this isolates the finite generator-level matrix-convex input actually used by the Kazhdan corner argument.
  property-t-alone-cannot-correct-tracial-choi-lifts: that proves property T cannot manufacture completely positive coordinate lifts; this theorem assumes precisely that missing matrix-range capture and proves that no further global lifting input is needed.
  kazhdan-almost-invariant-corner-near-invariant-projection: that corrects an almost-invariant corner inside an already genuine representation; this first obtains that corner from a ucp point in the full group matrix range.
---

Let `Gamma=<S>` be finitely generated and Kazhdan, with `S=S^(-1)`, and
write `u_s in C^*(Gamma)` for its canonical unitaries.  At matrix size `d`
put

```text
MR_d(Gamma,S)
 = { (Phi(u_s))_(s in S) : Phi:C^*(Gamma)->M_d is ucp }.          (GMR1)
```

Let `phi_n:Gamma->U(d_n)` be asymptotically multiplicative.  If

```text
dist_(2,S)((phi_n(s))_(s in S),MR_(d_n)(Gamma,S)) -> 0,            (GMR2)
```

then `(phi_n)` is flexibly Hilbert--Schmidt correctable: there are genuine
finite-dimensional representations `rho_n` and finite-rank identifications
whose dimension ratios tend to one and which approach `phi_n` on every fixed
group element in normalized Hilbert--Schmidt norm.

Thus weak ucp-stability of a Kazhdan group needs no global pointwise lifting
theorem beyond `(GMR2)`: complete positivity on the fixed generator operator
system is enough.  The remaining issue is not Kazhdan averaging, word
propagation, or congruence classification.  It is the matrix-order statement
that the prescribed generator tuple approaches the full-group matrix range.

Proof: `kazhdan-matrix-range-capture-proof`.

