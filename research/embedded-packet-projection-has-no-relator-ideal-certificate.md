---
rg: 2
id: embedded-packet-projection-has-no-relator-ideal-certificate
kind: claim
title: A nonzero projection in an embedded finite packet cannot be a defining-relator defect
invalidates:
  - mixed-cnot-joint-exit-first-hit-transducer-via-endpoints
distinct_from:
  exact-five-fourths-projection-return-collapses-the-packet: that rules out conjugating five-fourths of a packet below one copy of its carrier; this rules out declaring even one nonzero embedded packet projection to be a sum of defining-relator errors.
  trace-functorial-bcs-signal-groupification-impossible: that uses functoriality of a tracial signal recurrence; this is the elementary group-algebra obstruction for a sparse relator-ideal certificate.
---

Let

```text
Gamma=<S | R>
```

be a group presentation and suppose a finite group `H` embeds in `Gamma`.
If `0!=A in C[H]`, there is no identity in the free group algebra of the
form

```text
A=sum_t lambda_t V_t (r_t-1) W_t,       r_t in R,       (EPC1)
```

where `V_t,W_t` are arbitrary free-group-algebra expressions. More generally,
there is no dimension-independent inequality

```text
||pi(A)||_2^2 <= C sum_(r in R_0)||pi(r)-I||_2^2        (EPC2)
```

for every tracial unitary representation `pi` of `Gamma`, for any finite
`R_0 subset R` and finite `C`.

Indeed `(EPC1)` maps to `A=0` in `C[Gamma]`, contradicting injectivity of
`C[H]->C[Gamma]`. For `(EPC2)`, use the left regular representation of
`Gamma`: all relators have zero defect, whereas the canonical trace is
faithful and gives `||A||_2>0`.

In particular, a nonzero joint spectral atom or sum of atoms in an embedded
mixed-CNOT, Schur, or full-V4 packet cannot itself have a sparse
defining-relator certificate. Such a packet projection may be used as source
mass in a routing/capacity inequality, but the paid quantity must be leakage,
cross-Gram overlap, or another mismatch involving data outside the embedded
packet.
