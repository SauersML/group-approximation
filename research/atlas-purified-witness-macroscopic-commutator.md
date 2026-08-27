---
rg: 2
id: atlas-purified-witness-macroscopic-commutator
kind: claim
title: A purified positive Atlas witness has a fixed macroscopic commutator spectrum
distinct_from:
  leavitt-regular-atlas-block-monomial-gap: that gives an order-one normalized-HS commutator somewhere in each certificate; this upgrades it, after irreducible purification and passage to one subsequence, to one fixed coefficient pair with a uniform singular-value threshold on a positive fraction of the growing multiplicity space.
  leavitt-atlas-full-coefficient-purification: that removes convex mixtures and internal centers; this records the quantitative noncommutative carrier which necessarily survives inside the selected full matrix block.
  atlas-linear-energy-controlled-by-full-packet-defect: that is the existing smallest direct exclusion lemma for the positive Atlas target; this is a necessary shape theorem for any putative positive witness and does not claim the missing nonlinear energy domination.
artifacts:
  - notes/ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md
---

Assume the equivalent positive Atlas target of
`leavitt-atlas-full-coefficient-purification` is feasible.  Then, after
passing to a subsequence, its witnesses may be chosen with

```text
U_i in U(20160 r_i),                    r_i -> infinity,
D(U_i)=M_(r_i)(C),                      F_(r_i)(U_i) -> 0,
```

and there are one **fixed** pair `H_i,K_i` of real-or-imaginary block
coefficient positions, a constant `c_0>0`, and spectral projections

```text
P_i = 1_[c_0/4,infinity)( |[H_i,K_i]| )
```

such that

```text
tr_(r_i)(P_i) >= 3 c_0^2/64                         (MAC1)
```

for all sufficiently large `i`.  In particular,

```text
rank([H_i,K_i])/r_i >= 3 c_0^2/64.                  (MAC2)
```

Thus a positive certificate cannot hide its coefficient noncommutativity in
an `o(r_i)` corner or in a full-rank cloud whose singular values all tend to
zero.  The remaining positive target is genuinely a full-coefficient,
positive-density noncommutative transport.  This does not by itself exclude
that target: the existing smallest direct exclusion lemma remains
`atlas-linear-energy-controlled-by-full-packet-defect`.
