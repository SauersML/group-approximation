---
rg: 2
id: rational-heisenberg-fd-radical-mf-proof
kind: route
title: A determinant identity at a dimension-dependent rational kills the centre, and local residual finiteness gives the matrix models
target: rational-heisenberg-fd-radical-is-commutator-and-mf
requires:
  - lef-implies-operator-mf
artifacts:
  - research/artifacts/torsion-free-cover-fd-radical-and-heisenberg-2026-09-08.md
---

## 1. Algebra

`(RH1)` is matrix multiplication of

```text
[ 1  a  c ]
[ 0  1  b ]
[ 0  0  1 ]
```

so `H` is a group.  Induction on `n` gives

```text
(a,b,c)^n = (na, nb, nc + C(n,2) ab),                                  (P1)
```

which for `n > 0` is the identity only when `a = b = 0` and then `c = 0`.  So
`H` is torsion-free.  Directly from `(RH1)`,

```text
[x(a), y(b)] = z(ab),                                                  (P2)
```

`z(c)z(c') = z(c+c')`, and `z(Q)` is central because the top-right entry is
untouched by triangular multiplication.  `(P2)` with `b = 1` realizes every
`z(c)`, so `[H,H] = Z`, and `H/Z = Q^2` is abelian.

## 2. Every exact finite-dimensional representation kills the centre

Let `rho : H -> U(d)`.  The unitaries `rho(Z)` commute with all of `rho(H)`,
so their joint eigenspaces are `H`-invariant; on one of them, of dimension
`m >= 1`, write

```text
rho(z(c)) = chi(c) I_m,      chi : Q -> U(1) a homomorphism.
```

Restrict `(P2)` to that block.  A commutator of invertible matrices has
determinant `1`, so

```text
chi(ab)^m = det( chi(ab) I_m ) = det( [rho(x(a)), rho(y(b))] ) = 1
```

for all `a, b in Q`.  Given `c in Q`, take `a = c/m` and `b = 1`:

```text
1 = chi(c/m)^m = chi( m (c/m) ) = chi(c).
```

So `chi` is trivial on every block, i.e. `rho(Z) = {I}`, and `rho` factors
through `H/Z = Q^2`.  Hence `Z <= Rad_fd(H)`.

Conversely characters of `Q^2` separate points: if `(a,b) != (0,0)`, say
`a != 0`, choose a real `t` with `ta` not an integer and use
`(a',b') -> exp(2 pi i t a')`.  Composing with `H ->> Q^2` gives a
one-dimensional unitary representation of `H` detecting any element outside
`Z`.  Therefore

```text
Rad_fd(H) = Z = [H,H] != 1,
```

which is `(RH2)`.  Note where the argument spends its hypothesis: the
rational `c/m` depends on the block dimension, and divisibility of `Q` is what
makes it available.

## 3. `H` is MF

Let `S` be a finite subset of `H`.  All coordinates appearing in `S` are
rationals, so they lie in `Z[1/N]` for `N` the product of their denominators,
and `<S>` is contained in `UT_3(Z[1/N])`.

`UT_3(Z[1/N])` is residually finite: given `h != 1`, some coordinate of `h` is
a nonzero `c in Z[1/N]`, say `c = u/N^k` with `u` a nonzero integer.  Choose a
prime `p` dividing neither `N` nor `u`.  Since `p` does not divide `N`, the
class of `N` is invertible in `F_p`, so

```text
Z[1/N] -> F_p,     1/N -> (N mod p)^-1
```

is a well-defined ring homomorphism, and it sends `c` to
`u (N mod p)^-k != 0`.  Applying it entrywise gives a group homomorphism
`UT_3(Z[1/N]) -> UT_3(F_p)` whose value at `h` is nontrivial.

So every finitely generated subgroup of `H` is residually finite, i.e. `H` is
locally residually finite.  By the reusable corollary chain recorded on the
prerequisite `lef-implies-operator-mf`, locally residually finite implies LEF,
and every countable LEF group is operator MF.  `H` is countable, so `(RH3)`
holds.

**The explicit models are the LEF windows.**  Choosing increasing primes
`p_n`, let `lambda_n` be the left regular permutation representation of
`UT_3(F_(p_n))` on `C^(p_n^3)`, and set `V_n(h) = lambda_n(hbar)` when all
coordinates of `h` reduce modulo `p_n`, and `V_n(h) = I` otherwise.  For fixed
`h, k` all denominators are invertible for large `n` and reduction respects
`(RH1)`, so `V_n(hk) = V_n(h) V_n(k)` for all large `n`.  For `h != 1` the
numerator and denominator of a nonzero coordinate have finitely many prime
divisors, so `hbar != 1` for large `n` and

```text
||V_n(h) - I|| >= ||(V_n(h) - I) e_1|| = ||e_(hbar) - e_1|| = sqrt 2.
```

The induced map into the norm-matrix corona is thus a well-defined injective
homomorphism, exhibiting `(RH3)` concretely.  There is no conflict with step
2: each `V_n` is a map that eventually respects any *specified* identity, not
an exact homomorphism, and which identities fail may depend on `n` -- in
particular on the moving element `c/m`.

## 4. The refuted inference

`H` is torsion-free by step 1, satisfies `Rad_fd(H) = [H,H] != 1` by step 2,
and is MF by step 3.  So no implication of the form

```text
K torsion-free countable, Rad_fd(K) = [K,K] != 1   ==>   Rad_MF(K) != 1
```

is available, which is the negative half of the target.

## Note on what is deliberately not used

Amenability of `H` is not invoked.  `H` is nilpotent, hence amenable, and
Tikuisis--White--Winter would give MF directly; but
`permutation-norm-models-certify-exactly-lef` records that this archive
certifies no amenable group outside the LEF class as MF, and the LEF route
above is entirely elementary.
