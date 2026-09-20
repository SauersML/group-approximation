---
rg: 2
id: multiscaling-polynomial-germ-towers-have-f-infinity-actors
kind: claim
title: Finite multiscaling affine polynomial germ towers have F_infinity marked stabilizers and clopen actors
distinct_from:
  polynomial-valuation-germ-towers-are-f-infinity: that treats one scalar q and cyclic successive germ quotients; this requires simultaneous independent scalings, vector polynomial profiles, and higher-rank successive germ quotients.
artifacts:
  - research/artifacts/polynomial-germ-unitriangular-manuscript-2026-09-20.md
---

**OPEN — uniform multiscaling finiteness and actor theorem; submitted argument pending independent review.**

Let `S` be a nonempty finite set of primes, let `R_S=Z[S^-1]`, and
choose a prime `p∉S`. For every `m≥2`, use the left-coset tree of
`δ_p^j UT_m(Z_p)` and its affine self-similar group
`A_S=UT_m(R_S)⋊Z^S`, where `e=(e_s)` scales entry `(i,j)` by
`∏_{s∈S}s^{(j-i)e_s}`. For every `d≥0` and finite root number `r≥1`,
form the analogue `B^S_{d,r}` of the manuscript's full polynomial germ
group, with centered germs

`y↦δ_p^k (∏_{s∈S}δ_s^{P_s(ν(y))})(y)`, `P_s∈P_d`.

The proposed theorem asserts all of the following:

* The affine action is faithful and self-similar, and its finite-root RN
  group is the degree-zero full group `B^S_{0,r}`.
* The groups `B^S_{d,r}` are countable full groups with the specified
  germs `J^S_d=P_d^S⋊Z`. They and every pointwise or setwise stabilizer
  of a finite subset of their rational marked set `⊔_r UT_m(R_S)`
  have type `F_∞`. The marked action is highly transitive.
* The action on proper nonempty clopens is faithful and oligomorphic.
  The pointwise stabilizer of every finite family of clopens is a finite
  product of restriction groups `B^S_{d,u}`; each corresponding setwise
  stabilizer is a finite extension. In particular **all finite-subset
  stabilizers of this clopen action have type `F_∞`**.

## Attempts

Artifact §10 proposes replacing the scalar ascending HNN construction
by commuting ascending HNN maps for the primes in `S`. The rational
marked-fixer base then has local factor `Z^{S×F}`. The polynomial germ
step has normal quotient `J^S_d/J^S_{d-1}≅Z^S`. The punctured induction
would use `1→Fix_{B^S_{d-1,r}}(F)→C→(Z^S)^F→1` and the analogous
sequence after fixing further marked points.

These are unresolved substantive assertions: check the simultaneous
HNN normal forms and injectivity at every stage, the affine sections,
all supported germ realizations, and the germ-groupoid equality away
the punctures. The scalar argument is not automatically a proof of
these vector-valued statements. The finite-root SZ construction, BHM
application on a punctured Hausdorff space, and clopen atom restriction
identifications need the same full hypothesis checks as in the scalar
case. SZ and BHM are explicit classical inputs recorded in artifact §2;
the clopen actor conclusion is exactly what BZ would subsequently use.
No arithmetic replay, source-audit status, or Lean theorem closes this gate.
