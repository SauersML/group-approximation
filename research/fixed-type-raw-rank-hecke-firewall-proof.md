---
rg: 2
id: fixed-type-raw-rank-hecke-firewall-proof
kind: route
title: Freeze the finite type menu and spectator-amplify every raw-rank trigger
target: fixed-type-and-raw-rank-selectors-do-not-evade-hecke-firewall
requires:
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - vanishing-loss-center-chain-authentication-hits-affine-firewall
  - near-regular-finite-character-fixes-plancherel-types
  - packet-natural-selectors-cannot-extract-one-bounded-copy
  - separate-packet-calculi-have-no-common-matching
  - amplification-natural-words-cannot-read-packet-multiplicity
---

Let `I=Irr(K)`.  After fixed finite-group exactification, retaining whole
isotypic carriers is multiplication by

```text
z_(s,n)=sum_(rho in A_(s,n)) e_rho,
z_(r,n)=sum_(rho in A_(r,n)) e_rho                    (1)
```

for subsets `A_(s,n),A_(r,n) subseteq I`.  The pair of subsets takes values
in the finite set `2^I times 2^I`; choose a subsequence on which it is the
constant pair `(A_s,A_r)`, and denote the corresponding central projections
by `z_s,z_r`.

The matrices `Q_n,P_n` are evaluations of fixed elements of the exactified
finite packet.  Near-regular finite character convergence therefore gives

```text
tr_n(Q_n(1-z_(s,n))) -> tau(Q(1-z_s)),
tr_n(P_n(1-z_(r,n))) -> tau(P(1-z_r)).                 (2)
```

All factors in each product commute.  If both discarded masses tend to
zero, faithfulness of `tau` implies `Q(1-z_s)=P(1-z_r)=0`.  Hence the cuts
retain all of `Q,P` in the tracial ultraproduct.  The requested comparison
and relative-polar estimates then satisfy the hypotheses of the established
vanishing-loss firewall, which gives a fixed positive lower bound on their
error.  They cannot tend to zero.

If a rule cuts a proper part of one multiplicity reservoir using only the
represented packet, Schur naturality gives the zero-or-identity alternative.
If it constructs the two cuts separately, independent Haar gauges force
every natural rectangular matching to vanish.  Finally, tensoring the whole
matrix tuple by `I_l` preserves every normalized word trace and normalized
Hilbert--Schmidt defect while multiplying ambient dimension, kernel rank,
and packet multiplicity by `l`.  Therefore none of those raw integers can
be authenticated by an ordinary finite presentation.  These three cases
prove the stated scope.
