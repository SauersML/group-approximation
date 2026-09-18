---
rg: 2
id: fpbs-cycle-tail-not-a-group-ring-chain-invariant
kind: claim
title: Short and long chord graphings of the Bernoulli shift have unipotently isomorphic group-ring chain complexes but cycle tails differing by the chord mass
distinct_from:
  fpbs-cycle-tail-gap-near-minimum-iff-cost-betti-gap: that uses long chord insertion to show a lower gap for tau_L near the minimum is equivalent to g>0; this compares a short and a long chord on the same set and shows their augmented chain complexes and finite-cycle modules are isomorphic over Z[Z/2 wr Gamma] by a unipotent map, so tau_L is not a function of any length-blind group-ring invariant
  fpbs-graphing-cost-betti-cycle-dimension-identity: that proves c = 1 + beta_1 + z; this shows z is carried by the isomorphism while z_L is not
  fpbs-bernoulli-cycle-tail-compactness: that is the open compactness target; this is an established invariance lemma that blocks group-ring rank transplants to it and asserts nothing about whether tails vanish
artifacts:
  - research/artifacts/fpbs/docs/cycle-tail-unipotent-chord-swap-2026-09-17.md
---

**ESTABLISHED** through `fpbs-cycle-tail-not-a-group-ring-chain-invariant-proof`.

Let Gamma be infinite and finitely generated, b its Bernoulli shift on
2^Gamma, R the orbit relation, and A the ring of finite sums
sum f_g u_g with f_g locally constant and Z-valued. Then A tensor Q is
Q[Z/2 wr Gamma]. Let Phi be a cylinder graphing generating R, and let
L >= 3. There are a clopen set U of positive measure and gamma_s, gamma_l
in Gamma such that Phi_s = Phi cup gamma_s|U and Phi_l = Phi cup gamma_l|U
are simple cylinder graphings generating R, with the following properties.

1. c(Phi_s) = c(Phi_l) = c(Phi) + mu(U).
2. There is W : C_1(Phi_s) -> C_1(Phi_l) with partial_1^l W = partial_1^s.
   W and W^{-1} are unipotent with finite propagation and entries in A,
   and W Z(Phi_s) = Z(Phi_l).
3. tau_L(Phi_l) = tau_L(Phi) + mu(U) and tau_L(Phi_s) <= tau_L(Phi).

Consequently, no identity expresses tau_L = z - z_L through length-blind
data. Length-blind data here means anything invariant under such
isomorphisms: cost, z, L2-Betti numbers, Tor over A, every Sylvester rank
function including mod-p and finite-quotient ranks, Fuglede--Kadison
determinants, and K-classes. The cycle tail is an invariant of the
propagation filtration of A only.

Scope: the swap costs mu(U), and near the minimum the short-chord mass is
at most L eps. So this does not exclude length-blind bounds that tend to 0.
It shows that group-ring rank methods, which see only z = c - 1 - beta_1,
get no leverage from the tail formulation.
