---
rg: 2
id: dyadic-rordam-identical-pairing-destroys-sdr
kind: claim
title: An identical paired branch destroys Hall's condition on an infinite singleton seed
invalidates: [stw99-lxvi-via-dyadic-rordam-tower]
distinct_from:
  dyadic-rordam-tower-realizes-finite-car-corner: that is the proposed construction; this isolates a finite Hall obstruction already at the first paired step, before any limit or proper-infiniteness argument.
  uniformly-doubled-rordam-steps-force-proper-infiniteness: that uses a rank-versus-dimension argument at late high-multiplicity stages to prove the limit projection properly infinite; this proves the claimed SDR ledger is impossible at each identical paired step, using only the infinite singleton seed and finite branch data.
artifacts:
  - research/artifacts/stw99-lxvi-dyadic-rordam-v4-audit-2026-08-30.md
---

Let the seed multiset be `({a_i})_{i in N}`, with the `a_i` distinct, and
let every branch have the finite-set form

`alpha_beta(J) = nu_beta(J minus E_beta) union I_beta`,

where `E_beta` and `I_beta` are finite and `nu_beta` is injective.  Fix
any finite branch history before a step whose branch list contains two
identical copies of one branch `beta`.  Then the output multiset at that
step does **not** satisfy Rordam's Hall condition from Proposition 3.2.

Indeed, outside a finite set of seed indices, the sets transported along
the fixed history have the form

`J_i = C union {u_i}`,

where `C` is finite and independent of `i`, while the `u_i` are pairwise
distinct and lie outside `C`.  After the identical paired branch, the two
copies belonging to seed `i` are both

`K_i = C' union {v_i}`,

with the same properties.  For any `N > |C'|`, take both copies of
`K_i` for `N` good indices.  This finite sublist has `2N` members but its
union has size `N + |C'| < 2N`.  Hence it has no system of distinct
representatives.

Consequently, no choice of a sparse pairing schedule or finite size floor
`h(n)` can establish the proposed (V4) ledger.  The tensor coordinates
added along one fixed branch history are common to all seed summands;
freshness across different branches does not make them private across the
infinitely many seeds.  Repair requires changing the architecture (for
example, parent-dependent coordinate supply or a different finiteness
certificate), not merely increasing the finite branch sets or separating
paired steps further.
