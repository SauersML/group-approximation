---
rg: 2
id: finite-trace-profile-net-is-dimension-free
kind: claim
title: Fixed finite HS tests have a dimension-free compact trace-profile space
artifacts:
  - research/artifacts/nonhyperlinear-finite-moment-sparsification-2026-08-18.md
---

Fix finitely many free-group words `W`.  For a unitary tuple
`U in U(n)^k`, retain only the real normalized trace profile

```text
M_W(U) = (Re tr_n(w(U)))_(w in W) in [-1,1]^W.
```

The closure of the profiles arising in **all** finite matrix dimensions is a
compact subset of the fixed cube `[-1,1]^W`.  Hence for every `eta>0` it has a
finite sup-norm `eta`-net with cardinality bounded, for example, by

```text
(ceil(2/eta)+1)^|W|,
```

independently of matrix size.

For a finite relator menu `S` and finite test set `B`, taking

```text
W = S union {a^{-1}b : a,b in B, a != b}
```

loses none of the normalized-Hilbert--Schmidt information used by the
microstate test, since

```text
d_2(r(U),1)^2 = 2 - 2 Re tr_n(r(U)),

d_2(a(U),b(U))^2 = 2 - 2 Re tr_n((a^{-1}b)(U)).
```

In particular, a random-relator argument with a fixed finite menu never needs
a separate metric net of `U(n)^k` for each `n`.  Tensor amplification is
already identified at the profile level because normalized traces are
unchanged by `U -> U tensor I_m`.
