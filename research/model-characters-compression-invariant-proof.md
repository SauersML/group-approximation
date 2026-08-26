---
rg: 2
id: model-characters-compression-invariant-proof
kind: route
title: Trace invariance under conjugation, and lamp stabilizers
target: model-characters-of-compressed-pairs-are-compression-invariant
requires: []
---

The proofs are in the claim: (1) is the trace property of `tau` applied to
`pi(t) pi(gamma) pi(t)^*`; (2) uses that in the criterion form the conjugates `q_x = pi(g) q pi(g)^*`
are distinct for distinct cosets, so `Ad pi(g)` fixes `q` iff `g in Gamma`;
an element of `ker(pi)` fixes every `q_x`, hence lies in every conjugate
`g Gamma g^(-1)`.  (In a faithful model of `W`, `E` or `D` the statement is
vacuous, since `G` embeds in each of them and `pi` is then injective.)
For the core of
the Kun--Thom subgroup: an element of `EL_r(F_q[x_1..x_d])` lies in
`A EL_r(F_q[x_1..x_d]) A^(-1) = EL_r(F_q[x^(A e_1), ..., x^(A e_d)])` for every
non-negative `A in SL_d(Z)` only if all its entries are polynomials in the
monomials of every cone `A . N^d`; the intersection of these cones over all
such `A` is `{0}` (for any nonzero `v in N^d` some non-negative `A` has
`A^(-1) v notin N^d`, e.g. a transvection subtracting a coordinate), so the
entries are constants.
