---
rg: 2
id: three-gauge-tests-leave-a-tensor-spectator
kind: claim
title: One cross-Gram overlap and two Pauli gauge tests leave an arbitrary tensor spectator
distinct_from:
  two-fixed-packet-reynolds-actions-leave-a-gram-spectator: that amplifies two fixed packets and shows their Reynolds maps miss the spectator; this allows a scalable second algebra and attacks exactly the proposed cross-Gram plus two-commutator analytic core.
  one-cross-gram-moment-extracts-the-common-polar-gauge: that correctly constructs a relative commutant unitary from near-full overlap; this shows that even zero deficit and a perfectly locked gauge do not imply fullness.
  two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge: that correctly places the exposed gauge near the Pauli commutant; this separates that conclusion from identifying a named reservoir algebra with the whole commutant.
---

The conjunction of a full cross-Gram overlap and two exact mixed Pauli
commutators does not force two named commuting algebras to be mutual
commutants on their common corner.  For every `m>=1` and `s>=2`, on

```text
H=C^2 tensor C^m tensor C^s
```

take the common corner `P=1`, let `A=M_2 tensor I_m tensor I_s` be generated
by Pauli `X,Z`, and let the scalable named reservoir be
`B=I_2 tensor M_m tensor I_s`.  Set both packet transports equal to the
identity.  Their cross-Gram deficit is zero, the resulting relative polar
gauge is `V=1`, and both commutators `[V,X]` and `[V,Z]` vanish.  Nevertheless

```text
A'=I_2 tensor M_m tensor M_s  strictly contains B,
B'=M_2 tensor I_m tensor M_s  strictly contains A,
W*(A,B)=M_2 tensor M_m tensor I_s  is not End(H).
```

Thus these three scalar/norm tests authenticate a relative gauge but cannot
eliminate an unused multiplicity factor.  The exact missing hypothesis is
joint fullness (equivalently, spectator elimination): for commuting unital
finite-dimensional star subalgebras of one full matrix corner,
`W*(A,B)=P M_d P` implies `A'=B` and `B'=A`.  A quantitative extraction
theorem must therefore supply a dimension-free robust joint-fullness
estimate in addition to the three gauge tests.
