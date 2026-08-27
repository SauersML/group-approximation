---
rg: 2
id: infinite-cyclic-compression-lamp-mf-proof
kind: route
title: Slow bumps at separated finite-quotient sites represent the integer lamps
target: infinite-cyclic-compression-lamp-mf
requires: []
artifacts:
  - research/artifacts/unified-mf-compression-external-2026-08-15.md
  - GroupApproximation/Sofic/IntegerLampSurvival.lean
---

## Theorem

Let `H` be a countable residually finite group, let `L <= H` be finitely
generated, and suppose that, for some `t in H`,

```text
L_1 := t L t^{-1} < L
```

is a proper subgroup. Put `X = H/L_1`, with `H` acting by left translation,
and let

```text
W_Z = (direct_sum_(x in X) Z) semidirect H.
```

Then `W_Z` is MF. More precisely, it embeds faithfully in the unitary group
of a norm-matrix corona

```text
Q = product_n M_(d_n)(C) / direct_sum_n M_(d_n)(C).
```

The residual-finiteness hypothesis on `H` is essential to the construction
below: it supplies the finite quotients which simultaneously separate group
elements and finitely many lamp sites.

## Direct proof

### 1. Finite quotients separating the relevant sites

Enumerate the sites and choose representatives

```text
X = {x_1, x_2, ...},       x_j = r_j L_1,
```

and enumerate the nonidentity elements of `H` as `h_1, h_2, ...`. Fix a
finite symmetric generating set `T` of `L_1` and a real number `theta` such
that `theta/(2 pi)` is irrational.

For each `n`, consider the finite set of elements

```text
r_j^{-1} r_i w^{-1},
1 <= i != j <= n,          w in L_1,          |w|_T <= 3n.
```

Every such element is nontrivial: an equality `r_j^{-1}r_i = w in L_1`
would imply `r_i L_1 = r_j L_1`, contrary to `i != j`. Residual finiteness
therefore supplies a finite quotient

```text
q_n : H -> F_n
```

such that:

1. `q_n(h_i) != 1` for every `i <= n`; and
2. if `i != j <= n`, then `q_n(r_j^{-1}r_i)` is not represented by a
   `q_n(T)`-word of length at most `3n`.

Set `K_n = q_n(L_1)`. The compression disappears in every finite quotient:
because `L_1 = tLt^{-1} <= L`, the finite groups `q_n(L_1)` and `q_n(L)`
are both nested and conjugate, hence have equal cardinality. Consequently

```text
q_n(L_1) = q_n(L).
```

The model compensates for this finite-quotient collapse by using a slowly
varying phase rather than a two-valued lamp.

### 2. A slow phase bump

Let `ell_n` be word length on `K_n` with respect to `q_n(T)`, and define a
function on `F_n` by

```text
f_n(y) = max(1 - ell_n(y)/n, 0)    if y is in K_n,
         0                         otherwise.
```

Thus `f_n(e) = 1`, and `f_n` vanishes outside the radius-`n` word ball in
`K_n`. Let `lambda_n` be the left regular representation of `F_n` on
`l^2(F_n)`, precomposed with `q_n`, and define the diagonal unitary

```text
D_n delta_y = exp(i theta f_n(y)) delta_y.
```

For fixed `a in L_1`, write `m = |a|_T`. Left multiplication by `q_n(a)`
preserves `K_n`, and

```text
|ell_n(q_n(a)^{-1}y) - ell_n(y)| <= m.
```

Since `s |-> max(1-s/n,0)` is `1/n`-Lipschitz,

```text
||lambda_n(q_n(a)) D_n lambda_n(q_n(a))^* - D_n||
    <= |theta| m/n -> 0.
```

Let `D = [D_n]` in `U(Q)` and

```text
Lambda(h) = [lambda_n(q_n(h))].
```

Then `D` commutes exactly with `Lambda(a)` in the corona for every
`a in L_1`.

### 3. Put one integer lamp at every coset

For `x = rL_1 in X`, define

```text
U_x = Lambda(r) D Lambda(r)^*.
```

This is independent of the representative: if `r' = ra` with `a in L_1`,
then the equality follows from `[D,Lambda(a)] = 1`. All the `U_x` commute,
because at every finite stage they are permutation-conjugates of the same
diagonal matrix and hence are diagonal. They are also exactly covariant in
the corona:

```text
Lambda(h) U_x Lambda(h)^* = U_(hx).
```

For a finitely supported integer configuration

```text
b = sum_(x in X) m_x delta_x,
```

put `U(b) = product_x U_x^(m_x)`. Commutativity and covariance show that

```text
Phi(b,h) = U(b) Lambda(h)
```

defines a homomorphism `Phi : W_Z -> U(Q)`.

### 4. Every nonzero lamp configuration survives

Let

```text
0 != b = sum_(j in J) m_j delta_(x_j)
```

with `J` finite, and choose `j_0 in J` with `m_(j_0) != 0`. For `n` larger
than every index in `J`, evaluate the chosen finite-stage representative of
`U(b)` on `delta_(q_n(r_(j_0)))`.

The `j_0`-lamp contributes `f_n(e) = 1`. For `j != j_0`, its contribution is

```text
f_n(q_n(r_j^{-1} r_(j_0))).
```

By the separation imposed on `q_n`, this argument is either outside `K_n`
or has `q_n(T)`-word length greater than `3n`, and in either case its
`f_n`-value is zero. The resulting eigenvalue is therefore

```text
exp(i theta m_(j_0)) != 1,
```

where the inequality follows from the irrationality of `theta/(2 pi)`.
Consequently

```text
||U_n(b)-1|| >= |exp(i theta m_(j_0))-1| > 0
```

eventually, so `U(b) != 1` in the corona. Thus the entire lamp subgroup is
represented faithfully.

### 5. Every element with nontrivial `H`-part survives

Suppose `(b,h) in W_Z` with `h != 1`. The quotient-selection condition gives
`q_n(h) != 1` for all sufficiently large `n`. At such a stage,

```text
Phi_n(b,h) = U_n(b) lambda_n(q_n(h))
```

is a diagonal unitary times a nontrivial left translation. A nonidentity
left translation of a group has no fixed point, so it sends every standard
basis vector to an orthogonal one; the diagonal factor changes only its
phase. Hence

```text
||(Phi_n(b,h)-1) delta_y|| = sqrt(2)
```

for every `y in F_n`, and therefore `||Phi_n(b,h)-1|| >= sqrt(2)` eventually.
Thus `Phi(b,h) != 1`.

The homomorphism `Phi` is injective. If the matrix dimensions do not already
tend to infinity, repeat each coordinate by tensoring with identity matrices;
this changes none of the estimates or kernels. Hence `W_Z` embeds faithfully
in a norm-matrix corona and is MF.

## Identification with the integer replacement

In the two-state compression construction, the witness lamp is placed at the
site `tL in H/L`. There is an `H`-equivariant bijection

```text
H/L_1 -> H/L,       hL_1 |-> htL,
```

because `L_1 = tLt^{-1}`. It carries the root site `L_1` to `tL`.
Therefore the group above is, up to this relabeling of sites, exactly the
group obtained by replacing each `C_2` lamp in the compression wreath product
by an infinite cyclic lamp.

When `L` also has property `(T)`, this gives the sharp comparison with the
two-state construction. For

```text
W_2 = (direct_sum_(H/L_1) C_2) semidirect H,
```

the root lamp is an involution centralized by `L_1`, and its `L`-conjugates
commute. The finite-spectrum collapse theorem kills `[g,c]` in every MF
representation for `g in L`; choosing `g in L \ L_1` gives a nontrivial group
element and proves that `W_2` is not MF. The integer lamp has no corresponding
finite spectral decomposition. Its slowly varying phases are asymptotically
`L_1`-invariant in operator norm while retaining a fixed positive distance
from `1`, and separated finite-quotient bumps make the resulting corona model
faithful.

Thus the boundary exhibited here is spectral, not merely a slogan about
finite versus infinite lamp groups: the two-state lamp has rigid finite
spectrum and collapses, whereas the infinite cyclic lamp admits continuously
varying phases and a faithful MF model.

## Formalization status

The locality layer is kernel-checked in
`GroupApproximation/Sofic/IntegerLampSurvival.lean`. The theorem
`isOperatorMF_lampWreath` proves an operator-MF criterion for integer-lamp
wreath products from residually finite finite-window groups, and
`isOperatorMF_integerLampTelescope` proves the telescope instance under
residual finiteness and finite-index compression. The full group `W_Z` with
the compressing shift is not covered by that locality argument; its MF proof
is the slow-bump corona construction above and remains at Cairn proof level.
