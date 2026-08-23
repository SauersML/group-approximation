---
rg: 2
id: canonical-or3-nonincidence-cap-commutator-payment
kind: claim
title: Canonical OR3 links pay every nonincidence cap commutator
distinct_from:
  raw-prefix-covariance-reduces-to-nonincidence-cap-commutators: that proves this payment is sufficient and gives a minimal exact witness that it is necessary; this must derive the payment from ordinary actuator words on canonical matrix types.
  full-support-factor-refutes-exact-exhaustive-typed-cap-chain: that forbids imposing the payment as representation-universal exact typed rows; this asks for a canonical-matrix-only estimate which need not hold in the full-support perfect factor.
---

**OPEN.**  Fix the `R_edge`/OR3 instance and its finite context order.  In a
canonical finite-matrix tuple, exactify the local Fano packets and select a
profile `q_1,...,q_m` with the positive sequential mass supplied by
`fano-maximal-cap-overlap-has-positive-sequential-mass`.  Construct ordinary
actuator words with bounded overlap and an exact marked infinite completion
such that their squared normalized-HS energy `E_word` forces

```text
sum_(j,x: x notin c_j) ||[B_x,q_j]||_2^2
 <= C E_word+o(1),                                    (NCP1)
```

or the strictly weaker prefix-compressed version sufficient term-by-term in
`(RPC3)`.  The constant may depend on the fixed instance and profile menu,
but not on matrix dimension.

By `raw-prefix-covariance-reduces-to-nonincidence-cap-commutators`, the
ordinary incidence coefficient rows already pay all pairs with `x in c_j`,
and one common coarea threshold pays the source-cut boundary.  Hence `(NCP1)`
is sufficient for `(SPA12)`, polar correction, and the common-source POVM
decoder.

The estimate must be genuinely canonical-matrix-only.  Adding the
commutators in `(NCP1)` as exact relations would produce the exhaustive typed
chain forbidden by the full-support perfect factor.  Moreover the exact
seven-dimensional triangle in the reduction claim has zero incidence energy
but nonincidence energy and raw-prefix energy both equal to `1/7`; no proof
from local cap identities alone can establish `(NCP1)`.  A successful
actuator must therefore charge the first context omitted by each transported
variable, rather than adding another local cap label or repeating the
incidence covariance rows.

## Attempts

- **Impose every nonincidence commutator as a relator.**  This makes `(NCP1)`
  immediate, but it is exactly the representation-universal exhaustive typed
  chain ruled out by
  `full-support-factor-refutes-exact-exhaustive-typed-cap-chain`; the intended
  full-support perfect model does not extend.
- **Derive the missing rows by occurrence-local telescoping.**  The exact
  seven-dimensional Berge triangle in
  `raw-prefix-covariance-reduces-to-nonincidence-cap-commutators` has all
  occurrence rows zero while the first omitted-context term has squared norm
  `1/7`, so no local rearrangement or better Cauchy--Schwarz estimate can work.
- **Live attack.**  Charge only the prefix-compressed nonincidence terms on
  canonical matrix types, using a cycle actuator coupled to the common mark.
  This is weaker than globally centralizing every cap and is the remaining
  opening not covered by either exact-completeness obstruction above.
- **Finite Bass--Serre actor and canonical moment tests.**
  `canonical-fano-free-product-defeats-finite-actor-payment` computes a free
  Fano-cap commutator of canonical squared norm `1/2`.  Every finite
  graph-of-groups actor extends on that same canonical base type with zero
  actor defect.  Hence neither finite packet transport nor canonical side
  tests can prove the uncompressed `(NCP1)`.  The live attack must use the
  weaker prefix-compressed payload and a genuinely non-Bass--Serre two-cell
  or infinite actor tied to it.
- **Prefix-compress inside a selected finite type.**
  `canonical-b7-or3-corner-defeats-finite-prefix-actors` lifts the complete
  seven-dimensional triangle, including its Gram cut, into the rational
  natural block of `B_7`.  Its selected canonical source has mass `1/46080`
  and its prefix defect has squared norm `1/92160`; every finite Bass--Serre
  actor still extends with zero defect.  Thus selected-type compression does
  not rescue a finite actor.  The sole remaining opening is a
  payload-sensitive non-Bass--Serre two-cell or an infinite actor which fails
  canonical extension while retaining the exact marked completion.
