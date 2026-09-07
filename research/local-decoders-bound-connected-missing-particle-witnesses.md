---
rg: 2
id: local-decoders-bound-connected-missing-particle-witnesses
kind: claim
title: A supplied local decoder confines every minimal missing finite configuration to a bounded connected particle cluster
distinct_from:
  nonlinear-certificate-fibers-are-all-surjective-or-all-strict: that propagates fiberwise surjectivity across independent certificates; this glues attained particle clusters using an actual local decoder and bounds the size of a missing connected witness.
artifacts:
  - research/artifacts/conservative-syndrome-update-audit-2026-09-07.md
---

Let G be any group and let tau,sigma:{0,1}^G->{0,1}^G be cellular
automata with

    tau(0)=0,                 sigma tau=id.

Choose finite memories M for tau and S for sigma, both containing 1_G,
using the convention that an output at g reads inputs at gM or gS.
Put

    D=S^(-1) M^(-1) M S,             K=|MS|.

The finite set D is symmetric and contains 1_G. Join two occupied sites
p,q by an edge when p^(-1)q belongs to D.

If a finite binary configuration y splits into D-connected components
y_1,...,y_r and every y_i is attained by tau, then y is attained as well.
Its preimage is the disjoint union of sigma(y_1),...,sigma(y_r). Thus
attained separated output clusters have compatible local preimages.

If tau is nonsurjective, it has a missing finite configuration with at
most K particles. A missing finite configuration having the smallest
particle number is D-connected. Consequently nonsurjectivity has a
witness, up to translation, among the FINITE family of nonempty subsets

    T subset D^(K-1),     1_G in T,     |T|<=K,

whose D-induced graph is connected. Equivalently, attaining every member
of that finite family suffices to prove surjectivity of tau. This is a
finite mathematical criterion for a supplied encoder-decoder pair, not a
claim that group-word equality or membership in the image is decidable.

Conservation of particle number is not needed for this theorem. If tau
is also binary particle-number-conserving, the earlier conservative
audit shows that the zero-, one-, and two-particle sectors are all
attained. Any missing witness above must then have between 3 and K
particles. The proof does not automatically supply the connected lifts
in that remaining finite range.

A nontrivial example is the binary rule on Z which simultaneously swaps

    11 0100 11  <->  11 0010 11

and changes only the two interior payload bits. Adjacent-11 marker
positions are unchanged, active payloads are disjoint, and their
eligibility is unchanged. This is a conservative nonlinear involution,
so its explicit decoder supplies every required connected lift. It
illustrates local cluster correction; it is surjective and supplies no
strict full-shift embedding.
