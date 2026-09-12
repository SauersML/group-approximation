---
rg: 2
id: canonical-finite-packet-data-stop-at-scalar-overlaps
kind: claim
title: Canonical finite-packet data determine Plancherel masses and scalar overlaps but not reservoir ownership
distinct_from:
  near-regular-finite-character-fixes-plancherel-types: that proves the one-subgroup Plancherel multiplicities; this computes the exact two-subgroup overlap and finite-conjugation checksum and then proves those scalar data do not align multiplicity coordinates.
  finite-product-selected-type-mark-does-not-align-carriers: that gives the C2 free-product overlap-with-zero-meet example; this supplies the general intersection-character formula and independent multiplicity-gauge countermodel.
  relative-fixed-algebra-payment-lemma: that assumes an averaged no-capture inequality; this computes when canonical finite-subgroup moments can certify such an inequality and when they cannot.
---

Let `F,K<=Gamma` be finite, let `rho in Irr(F)`, `sigma in Irr(K)`, and let
`q_rho^F,q_sigma^K` be their rational or complex central isotypic
idempotents. Put `L=F cap K`. Then

```text
tau_Gamma(q_rho^F q_sigma^K)
 =d_rho d_sigma |L|/(|F||K|)
   <Res_L^F rho,Res_L^K sigma>.                         (CFP1)
```

Canonical-delta microstates, after fixed finite-group exactification, have
the same limiting overlap. Their `rho` multiplicity satisfies

```text
m_(rho,n)/d_n -> d_rho/|F|,
rank(q_(rho,n))/d_n -> d_rho^2/|F|.                    (CFP2)
```

For a finite conjugation packet `K`, the canonical Reynolds checksum is

```text
||E_K(q_rho)||_2^2
 =|K|^(-1)sum_(k in K)tau(q_rho kq_rho k^(-1)),         (CFP3)
```

with every summand computed by `(CFP1)` using
`F cap kFk^(-1)`. Hence canonical data give a positive finite-packet
no-capture gap exactly when conjugation moves the selected central sector.

These conclusions exhaust the unconditional ownership information. In
`Gamma=F times K`, `q_rho^F` is fully captured by the `K`-commutant. In
`F times C_m`, projections `q_rho e_A` realize arbitrary rational fractions
of the selected carrier entirely inside the `F` multiplicity commutant.
Finally, exact multiples of the regular representation of `F times K` retain
the canonical character after independently rotating the `K`-action inside
each `F`-isotypic multiplicity reservoir. All masses and scalar overlaps stay
fixed while the physical cross-context coordinates change arbitrarily.

Thus canonical character can authenticate scalar packet leakage when group
combinatorics already moves a sector. It cannot create a common reducing
carrier, a reservoir gauge, or cross-context ownership.
