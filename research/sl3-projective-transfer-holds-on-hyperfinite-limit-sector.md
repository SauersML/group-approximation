---
rg: 2
id: sl3-projective-transfer-holds-on-hyperfinite-limit-sector
kind: claim
title: Projective trace-square transfer holds on the hyperfinite-limit sector of the SL3 arithmetic pair
distinct_from:
  exact-projective-codensity-has-a-uniform-trace-square-gap: that treats exact finite-dimensional representations in every trace sector; this promotes the estimate through approximate representations only when their limiting ambient character is von Neumann amenable.
  sl3-rigidity-stops-before-inner-adjoint-correction: that explains why rigidity does not correct the nonamenable regular inner-adjoint sector; this proves that the complementary amenable sector is completely correctable and hence cannot contain an enemy.
  sl3-odd-correctable-sector-has-uniform-projective-modulus: that closes a congruence sector by the arithmetic Weyl evaluation; this closes every hyperfinite-limit sector by flexible correction of the whole ambient tuple, without specifying congruence levels.
---

Put

```text
C=SL_3(Z),        A=SL_3(Z[1/2]),
h=diag(2,1,1/2).
```

Let `rho_n` be finite-dimensional unitary assignments for a fixed finite
presentation of `A`, with normalized-Hilbert--Schmidt presentation defect
tending to zero, and let `U_n` be auxiliary unitaries.  Pass to a tracial
matrix ultraproduct and write

```text
pi:A -> M,       N=pi(A)''.
```

Assume that `N` is amenable (equivalently, the character
`g |-> tau(pi(g))` is von Neumann amenable).  If

```text
sum_(c in S_C) (1-|tr([U_n,rho_n(c)])|^2) -> 0,          (HPT1)
```

then

```text
1-|tr([U_n,rho_n(h)])|^2 -> 0.                          (HPT2)
```

Thus every matrix-ultraproduct counterexample to
`projective-trace-square-transfer-for-sl3-pair` has a genuinely
nonamenable generated `A`-algebra.  In particular, character rigidity and
property `(T)` completely dispose of the hyperfinite part of the character
simplex; their known scope failure occurs only in the nonamenable regular
sector.

## Proof

Peterson--Thom/Bekka character rigidity for the higher-rank S-arithmetic
group `A` says that every amenable character is assembled from
finite-dimensional characters (the regular character is not amenable,
because `A` is nonamenable).  Equivalently, by the general character
criterion for hyperfinite Hilbert--Schmidt stability recorded in
`character-rigidity-equals-hyperfinite-hs-stability`, `A` is hyperfinitely
Hilbert--Schmidt stable.  Apply that theorem to `rho_n`.  After passing to a
subsequence and making the allowed flexible corner adjustment, there are
exact finite-dimensional representations

```text
sigma_n:A -> U(D_n),             D_n/d_n -> 1,          (HPT3)
```

such that the padded matrices `rho_n(s) direct_sum I_(D_n-d_n)` are
`o(1)`-close in normalized Hilbert--Schmidt norm to `sigma_n(s)` for every
fixed presentation generator `s`.  The equivalent partial-isometry
formulation gives the same conclusion after deleting and padding
`o(d_n)` dimensions.

Put

```text
Uhat_n=U_n direct_sum I_(D_n-d_n).
```

For fixed unitaries `U,X,Y`,

```text
||[U,X]-[U,Y]||_2 <= 2||X-Y||_2,
| (1-|tr([U,X])|^2) - (1-|tr([U,Y])|^2) |
  <= 4||X-Y||_2.                                      (HPT4)
```

Changing normalization from `d_n` to `D_n` and adding the identity corner
changes every displayed trace-square energy by `o(1)`, because
`D_n/d_n -> 1`.  Finite word telescoping transports the generatorwise
correction in `(HPT3)` to `S_C union {h}`.  Hence `(HPT1)` implies

```text
sum_(c in S_C)
 (1-|tr([Uhat_n,sigma_n(c)])|^2) -> 0.                 (HPT5)
```

The exact, dimension-independent theorem
`exact-projective-codensity-has-a-uniform-trace-square-gap` now applies to
`sigma_n` and `Uhat_n`:

```text
1-|tr([Uhat_n,sigma_n(h)])|^2
 <= K sum_(c in S_C)
       (1-|tr([Uhat_n,sigma_n(c)])|^2) -> 0.            (HPT6)
```

Equation `(HPT4)`, finite word telescoping, and `D_n/d_n -> 1` carry
`(HPT6)` back to the original corner, proving `(HPT2)`.

## Scope

The amenability assumption is essential to this argument.  Residual-finite
tensor camouflage can force the `A`-character of an arbitrary enemy to the
regular character without changing any projective commutator energy; its
GNS algebra is `L(A)`, which is nonamenable.  Dogon--Vigdorovich's
hyperfinite stability theorem deliberately does not correct that sector.
The exact central-HNN factor gives the simultaneous tracial calibration:
property `(T)`, character rigidity and all exact group relations coexist
there with maximal trace-square leakage.  Therefore the claim is a genuine
sector theorem, not a proof of the universal or canonical-regular transfer.
