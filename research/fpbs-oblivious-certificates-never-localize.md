---
rg: 2
id: fpbs-oblivious-certificates-never-localize
kind: claim
title: Base-oblivious source certificates, including lifts from the forgotten factor, never satisfy block localization
distinct_from:
  fpbs-relative-cycle-block-localization: that is the open universal localization premise; this proves it fails, with an explicit invariant, for the whole class of certificates whose label occupancy does not see the base
  fpbs-relative-cycle-block-rounding-bound: that proves rounding from localization; this shows that bound's premise cannot be met by base-oblivious certificates
  fpbs-relative-cycle-dpp-disconnects: that kills a deletion rule for one example; this kills a certificate class for every partition and every block size
artifacts:
  - research/artifacts/fpbs/docs/oblivious-occupancy-localization-obstruction.md
---

**ESTABLISHED.** Let Gamma be infinite and finitely generated, pi:Y->X a
free p.m.p. factor, and Phi a finite-label generating source graphing.
Suppose Phi is base-oblivious: each label's conditional occupancy p_s(x)
is a.e. constant. The main example is the lift of a graphing of a to
a x b -> b. Let S be the labels with p_s>0, so H = Cay(Gamma,S). Let
rho_s be the finite-cycle weight of an s-edge in H, and
D(Phi) = sum over infinite-order s of (1-p_s) rho_s. For every measurable
partition into blocks of at most M vertices,

    (1+2 d M^2) Tr(P_out K) >= 2 d M D(Phi).

If Gamma is torsion-free, non-cyclic, with beta_1^(2)(Gamma)=0, and
c(Phi)<4/3, then D(Phi)>=1/12, and the left side is at least 2/3 for all
blocks and all M. So the weighted boundary premise (14) of
`fpbs-relative-cycle-block-localization` fails uniformly on this class.
That includes the lifted graphings of a that witness C(a x b)<=C(a) in
`fpbs-bernoulli-lower-bound-from-block-localization`, and it holds already
on Z^2, where fixed price holds and a base-lifted certificate has K=0. The
obstruction concerns only the weighted boundary estimate. It does not
address the retraction residual Tr(R K R^*) of Section 7 of the exchange
artifact, where parallel bridges may cancel.
