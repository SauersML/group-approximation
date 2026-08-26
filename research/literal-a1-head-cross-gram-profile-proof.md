---
rg: 2
id: literal-a1-head-cross-gram-profile-proof
kind: route
title: Take the minimum cross energy over the finitely many literal-head irreducibles
target: literal-a1-head-forces-arbitrary-profile-native-cross-gram
requires:
  - full-q-a1-projective-head-is-a-literal-finite-subgroup
  - full-q-a1-binary-extension-closes-zero-cross-block
  - finite-group-opnorm-support-profile
---

By the projective matrix-unit lift, the subgroup `H_A` in `(LAG2)` is
literally isomorphic to the finite group `P_A`.  The central-support audit
therefore proves in the actual complex group algebra corner

```text
F in (F C[H_A] F) h (F C[H_A] F).                     (1)
```

Let `sigma` range over the finite set `Irr(H_A)`.  If `sigma(F)!=0`, equation
`(1)` implies `sigma(h)!=0`.  Define

```text
kappa=min_(sigma(F)!=0)
  Tr(sigma(h)^*sigma(h))/Tr(sigma(F)).                 (2)
```

Every term in `(2)` is positive and there are finitely many terms, hence
`kappa>0`.

Restrict an arbitrary exact finite-dimensional representation `pi` of
`Delta` to `H_A` and decompose it as

```text
pi|_(H_A)=direct_sum_sigma sigma^(m_sigma).             (3)
```

Both traces in `(LAG3)` are additive across `(3)`.  Applying `(2)` in every
summand gives

```text
Tr(pi(h)^*pi(h))
 =sum_sigma m_sigma Tr(sigma(h)^*sigma(h))
 >=kappa sum_sigma m_sigma Tr(sigma(F))
 =kappa Tr(pi(F)),                                     (4)
```

which proves the exact assertion without choosing a trace profile.

For an operator-norm asymptotic representation, retain the fixed finite
relation table of `H_A`.  `finite-group-opnorm-support-profile` changes its
lifts, in the same dimension and by operator norm `o(1)`, to an exact
representation of `H_A`.  Fixed-word telescoping and the finite signed
average defining `F` change both sides of `(4)` by `o(1)` in normalized
Hilbert--Schmidt norm.  Therefore

```text
||pi_n(FgF)||_(2,n)^2
 >=kappa tau_n(pi_n(F))-o(1).                          (5)
```

All constants depend only on the one finite head.  In particular no
dimension-dependent passage from Hilbert--Schmidt to operator norm occurs:
operator norm is used only to exactify the head, and `(4)--(5)` are trace
inequalities after that exactification.
