---
rg: 2
id: modular-vertex-restriction-cone-proof
kind: route
title: Use prime-to-p congruence surjectivity to identify every restriction fiber
target: modular-vertex-restriction-cone-has-singleton-fibers
requires:
  - sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
---

## Essential surjectivity and full faithfulness

By `sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`, every
finite-dimensional unitary representation of `A` factors through a
standard reduction

```text
r_m:A->Q_m=SL_2(Z/m),       gcd(m,p)=1,                 (MVP1)
```

and `r_m restricted to C` is surjective. Conversely, if a
`C`-representation `beta` factors through `Q_m`, composing
its quotient representation with `r_m` extends it to `A`. This
proves essential surjectivity of (MVC2).

Let `rho` and `sigma` be finite-dimensional `A`-representations.
Choose one prime-to-`p` level `m` through which both factor, by
replacing their two levels by a common multiple. Suppose `T` intertwines
their restrictions to `C`. For every `a in A`, surjectivity of
`C->Q_m` gives `c in C` with `r_m(c)=r_m(a)`. Therefore

```text
T rho(a)=T rho(c)=sigma(c)T=sigma(a)T.                  (MVP2)
```

Thus every `C`-intertwiner is already an `A`-intertwiner, proving
(MVC3). Taking `rho` and `sigma` to be two extensions of the same
object proves uniqueness. Direct sums and subrepresentations are preserved,
so this is an order equivalence of the finite-dimensional unitary
representation categories in (MVC2).

## Restriction matrix and Plancherel vector

Fix `m`. Because `C->Q_m` is onto, an irreducible representation
of `Q_m` remains irreducible after pullback to `C`, and two such
pullbacks are equivalent only when the quotient representations are
equivalent. The same labels describe their pullbacks to `A`. Hence the
restriction matrix in the `Irr(Q_m)` bases is the identity.

It follows immediately that every nonnegative multiplicity vector is
feasible and that its fiber is a singleton. If the same representation is
written at two nonminimal levels, inflate both to a common level; (MVP2)
shows that this bookkeeping creates no new endpoint type.

For a nonzero vector `M`, the fraction of total representation dimension
carried by `pi` is exactly the number `theta_pi` in (MVC3a). Conversely,
if all `theta_pi` are rational, choose a common positive integer `L` for
which every

```text
M_pi=L theta_pi/dim(pi)
```

is integral. This realizes the prescribed rational point. Rational points
are dense in the standard simplex, proving the projectivized cone statement.

The regular representation of `Q_m` decomposes as

```text
lambda_(Q_m)
 =direct_sum_(pi in Irr(Q_m)) pi tensor 1_(dim pi).      (MVP3)
```

Thus its multiplicity vector is (MVC4), and the normalized weight of the
`pi`-carrier is `dim(pi)^2/|Q_m|`. This is an integral point of
the feasible semigroup, not merely a real-cone limit.

The dual of a finite nonnegative orthant under the standard multiplicity
pairing is the same orthant. Every coordinate of the Plancherel vector
`(dim(pi))_pi` is strictly positive. Hence a nonzero dual vector has the
strictly positive pairing in (MVC4a), proving the fixed-level Farkas
assertion.

## Exact finite Plancherel windows

Let `F subset C` be finite. For every `g in F minus {e}` choose
one nonzero integer entry `a_g` of the matrix `g-I`. Define `P_F` and
`m_F` by (MVC5). Then

```text
gcd(m_F,p)=1,       m_F>|a_g|>0,
g mod m_F != I       for every g in F minus {e}.        (MVP4)
```

The first assertion follows from `m_F=1 mod p`; the second follows because
the positive product `P_F` is at least each factor `|a_g|`. Reduction of
`A` modulo `m_F` is therefore defined, and it is onto because its
restriction from `C` is onto. Pull back the left regular representation of
`Q_(m_F)=SL_2(Z/m_F)`. Its normalized character equals one on the kernel
of reduction and zero off that kernel. By (MVP4), it agrees with
`delta_e` on all of `F`, proving (MVC5)--(MVC6).

For the coefficient-table statement, fix finite `W,K subset C` and form

```text
S={h^(-1)wk: h,k in K, w in W, h^(-1)wk!=e}.           (MVP4a)
```

Apply the same explicit-modulus construction to `S`. Reduction modulo the
resulting `m` has the property

```text
h mod m = (wk) mod m       iff       h=wk              (MVP4b)
```

for `h,k in K` and `w in W`. It is injective on `K`, so define
`J_K delta_k=delta_(k mod m)`. The `(h,k)` matrix entry of the left side
of (MVC7) is one exactly when the left condition in (MVP4b) holds; the
corresponding matrix entry of the right side is one exactly when `h=wk`.
All entries agree, proving (MVC7).

Finally let `L` be any real affine functional depending on finitely many
character coordinates and nonnegative on all normalized endpoint
characters. Apply the construction to a finite set containing every
coordinate used by `L`. The resulting endpoint character and
`delta_e` have identical inputs to `L`, so

```text
L(delta_e)=L(chi_(Lambda_F))>=0.                         (MVP5)
```

Hence no finite-support Farkas separator exists. The argument concerns the
character cone only; it supplies no unitary alignment with a prescribed
coordinate representation.
