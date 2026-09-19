---
rg: 2
id: one-bounded-type-coefficient-separator-proof
kind: route
title: Approximate the bounded-type central projection and use orthogonal right corners
target: one-bounded-type-coefficient-separates-unbounded-exits
requires:
  - kazhdan-bounded-types-form-central-summand
  - regular-trace-forbids-universal-bounded-type-placement
  - toeplitz-self-embedding-fixes-unbounded-congruence-types
---

The group algebra is norm dense in `C*_max(Lambda)`, so a selfadjoint `a`
satisfying `(BTC1)` exists.  In any representation,

```text
||pi(a)-P||_op <= epsilon.                               (BTP1)
```

Therefore

```text
||Z(1-P)||_2
 <= ||Z(1-pi(a))||_2+||Z(pi(a)-P)||_2
 <= eta+epsilon||Z||_2
 = eta+epsilon sqrt(q).                                 (BTP2)
```

Right multiplication by the complementary projections `P` and `1-P` gives
orthogonal Hilbert--Schmidt components, without any commutation assumption
between `Z` and `P`.  Since `Z` is a projection,

```text
q=||Z||_2^2=||ZP||_2^2+||Z(1-P)||_2^2.                 (BTP3)
```

Also

```text
||ZP||_2^2=tr(PZP)<=tr(P).                              (BTP4)
```

Combining `(BTP2)--(BTP4)` proves `(BTC3)` and hence `(BTC4)`.

If `P=0`, then `(BTP2)` read in the opposite direction gives

```text
eta=||Z(1-pi(a))||_2
 >= ||Z||_2-||Zpi(a)||_2
 >= (1-epsilon)sqrt(q),
```

which is `(BTC5)`.  The congruence exits of
`toeplitz-self-embedding-fixes-unbounded-congruence-types` have `P=0` for
every fixed cutoff below their irreducible degree.  The regular representation
also has `P=0` by `kazhdan-bounded-types-form-central-summand`, while
`regular-trace-forbids-universal-bounded-type-placement` gives positive packet
mass.  Hence the same coefficient both excludes the finite stationary exits
and exposes the exact regular-character firewall.

