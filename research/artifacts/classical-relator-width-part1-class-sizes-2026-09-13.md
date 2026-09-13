# Classical relator width, part 1: class sizes in symplectic, unitary and orthogonal groups

Lane `ex-weak-sofic-classical-covering`, 2026-09-13. Part 1 of 3. Elementary throughout.
Used by `simple-group-classical-width-is-finite-field-linear-soficity-proof`.

## 0. Setting

`q` is a prime power and `F_0 = F_q`. `V` is an `n`-dimensional space over `F`, carrying a
nondegenerate form of one of three types:
- **(Sp)** `F = F_q`, `beta` alternating;
- **(U)** `F = F_(q^2)` with `xbar = x^q`, `beta` hermitian, linear in the second variable;
- **(O)** `F = F_q`, a quadratic form `Q` whose polar form `beta(v,w) = Q(v+w) - Q(v) - Q(w)` is
  nondegenerate. So `n` is even when `q` is even. Odd-dimensional orthogonal groups in even
  characteristic are symplectic groups as abstract groups, so they are not needed.

Definitions:
- `I(V)` is the isometry group, and `Q_0` is any group with `I(V)' <= Q_0 <= I(V) ∩ SL(V)`.
  This includes `Sp(V)`, `SU(V)`, and `Omega(V)` for every standard definition, since `Omega`
  contains `O(V)'`.
- A vector `v` is *singular* if `beta(v,v) = 0` in cases (Sp) and (U), and `Q(v) = 0` in case (O).
- A *hyperbolic pair* is a pair of singular vectors `(e, f)` with `beta(e, f) = 1`.
- Put `q_F = |F|`, and let `F_0`-dimensions be `e_F = [F : F_0]` times `F`-dimensions.

Every isometry `g` preserves `beta`. If `g` fixes a subspace `A` pointwise, then
`beta(gv - v, a) = beta(gv, ga) - beta(v, a) = 0`, so `im(g - 1) <= A^perp`. With `A = ker(g - 1)`
and dimensions compared, **`im(g - 1) = ker(g - 1)^perp`**. (P0)

## 1. Hyperbolic pairs and singular vectors

**Lemma 1.1 (isotropy).** Let `R` be a nondegenerate subspace of `V`, of dimension at least `3` in
case (O) and at least `2` in case (U). Then `R` contains a nonzero singular vector.

*Proof.*
- **(Sp).** Every vector is singular.
- **(O), `q` odd.** Diagonalize `Q|_R = a x^2 + b y^2 + c z^2 + ...` with `a, b, c != 0`. The sets
  `{a x^2}` and `{-c - b y^2}` each have `(q+1)/2` elements, so they meet. The resulting `(x, y, 1)`
  is singular.
- **(O), `q` even.** Take `e, f in R` with `beta(e, f) = 1` and `v in {e,f}^perp ∩ R`, nonzero. If
  `Q(e) = 0` we are done. Otherwise `Q(x e + v) = Q(e) x^2 + Q(v)`, which vanishes for the unique
  square root `x = (Q(v)/Q(e))^(1/2)`.
- **(U).** Diagonalize `beta|_R = diag(alpha, alpha', ...)` with `alpha, alpha' in F_q^x`. The norm
  `x -> x^(q+1)` maps `F^x` onto `F_q^x`, since its kernel has order at most `q + 1`. So
  `x^(q+1) = -alpha'/alpha` has a solution, and `(x, 1, 0, ...)` is singular.

**Lemma 1.2 (splitting).** If `e in R` is singular and `R` is nondegenerate, there is `f in R` with
`(e, f)` a hyperbolic pair.

*Proof.* Pick `f_1 in R` with `beta(e, f_1) = 1`.
- **(Sp).** `f = f_1`.
- **(O).** `f = f_1 - Q(f_1) e`. Then `Q(f) = Q(f_1) - Q(f_1) beta(f_1, e) = 0`.
- **(U).** `f = f_1 + a e`, with `a in F` chosen so that `a + abar = -beta(f_1, f_1)`. The trace
  `F -> F_q` is onto.

**Corollary 1.3.** `V = L (+) L' (+) V_0` (orthogonal sum of `L (+) L'` and `V_0`), with:
- `L = span(e_1..e_m)` and `L' = span(f_1..f_m)` spanned by hyperbolic pairs `(e_i, f_i)`;
- all other pairings zero;
- `dim V_0 <= 2` in case (O), `dim V_0 <= 1` in case (U), and `V_0 = 0` in case (Sp).

*Proof.* By Lemmas 1.1 and 1.2, a nondegenerate `R` of dimension `>= 3` (O), `>= 2` (U, Sp) is
`span(e, f) (+) (span(e, f)^perp ∩ R)` with `(e, f)` hyperbolic. Iterate on the second summand.

**Lemma 1.4 (counting singular vectors).** Let `R` be nondegenerate of dimension `k >= 4`.
1. `R` has at least `(1/2) q_F^(k-1)` singular vectors.
2. For a singular `e in R`, at least `q_F^(k-2)` singular `f in R` satisfy `beta(e, f) = 1`.

*Proof.*
- **Setup.** By Lemmas 1.1 and 1.2, `R = H_0 (+) R'` with `H_0 = span(e, f_0)` hyperbolic.
  Write `v = x e + y f_0 + w` with `w in R'`. The value is
  - `Q(v) = x y + Q(w)` in case (O);
  - `beta(v,v) = Tr(xbar y) + beta(w,w)` in case (U);
  - `0` in case (Sp).
- **Item 1.**
  - (O): for each `w` the equation `x y = -Q(w)` has at least `q - 1` solutions. So there are at
    least `(q - 1) q^(k-2) >= (1/2) q^(k-1)` singular vectors.
  - (U): for each `w` there are at least `(q^2 - 1) q` pairs `(x, y)`, giving
    `(q^2-1) q · q^(2(k-2)) >= (1/2) q_F^(k-1)`.
  - (Sp): trivial.
- **Item 2.** `beta(e, v) = y` fixes `y = 1`.
  - (O): `x = -Q(w)` is then determined, giving `q^(k-2)` solutions.
  - (U): `Tr(x) = -beta(w,w)` has `q` solutions `x`, giving `q_F^(k-2) q` solutions.
  - (Sp): `x` is free.

## 2. A lower bound for `|Q_0|`

**Lemma 2.1.** Let `m` be the Witt index of Corollary 1.3, with `m >= 3`. Then
```text
|Q_0| >= (1/4) q^(E_0),   E_0 = 2 m^2 + m - 1   (Sp),   2 m^2 - m - 1   (O),   4 m^2 - 2   (U).
```
In terms of `n`: `E_0 >= n(n+1)/2 - 1` (Sp), `E_0 >= n(n+1)/2 - 3n - 4` (O), and
`E_0 >= n(n+1) - 3n - 4` (U).

*Proof.*
- **The three subgroups.**
  - *Levi.* `m(x)` acts as `x` on `L`, as the adjoint inverse `x^(-dagger)` on `L'` (with respect to
    the pairing `L' -> L^*`), and as `1` on `V_0`. It is an isometry.
  - *Unipotent radical.* For `S : L' -> L`, `u_S(a + b + c) = a + S b + b + c` (with `a in L`,
    `b in L'`, `c in V_0`) is an isometry iff `beta(Sb, b') + beta(b, Sb') = 0` for all `b, b'`,
    together with `beta(Sb, b) = 0` in case (O). This is a direct expansion using
    `beta(L, L) = beta(L', L') = 0`.
  - *Opposite radical.* The group `U^-` is defined with `L` and `L'` exchanged.
- **Sizes.** Identifying `L = (L')^*`, the admissible `S` are symmetric forms (Sp, `F_0`-dimension
  `m(m+1)/2`), alternating forms (O, `m(m-1)/2`), or skew-hermitian forms (U, `m^2`). So
  `|U| = |U^-| = q^(dim)`.
- **Inside `I(V)' <= Q_0`, all three cases.**
  - *Levi part.* `m : SL(L) -> I(V)` is a homomorphism, and `SL_m(q_F)` is perfect for `m >= 3`. So
    `m(SL(L)) <= I(V)'`.
  - *Radical.* `u_S u_(S') = u_(S + S')`, and `m(x) u_S m(x)^-1 = u_(x S x^dagger)`. So
    `[m(x), u_S] = u_(x S x^dagger - S)`. Its form is `B_S` transformed by the substitution `x^dagger`
    in `SL(L')`, minus `B_S`.
    - Substitutions `b_i -> b_i + lambda b_j` (`i != j`, `lambda in F`) applied to basis forms produce
      every admissible basis form. For alternating forms, `b_1^* ∧ b_2^*` under `b_1 -> b_1 + b_3` gives
      `b_3^* ∧ b_2^*`.
    - For symmetric and hermitian-type forms, a diagonal form under `b_1 -> b_1 + lambda b_2` gives an
      off-diagonal term plus a diagonal term in `b_2`, and off-diagonal terms are obtained as in the
      alternating case.
    - These differences span all admissible forms (a direct check on basis forms, using `m >= 3`). So
      `U <= I(V)'`, and likewise `U^- <= I(V)'`.
- **Big cell.** The map `U^- x m(SL(L)) x U -> Q_0` is injective.
  - `P = Stab(L)` contains `m(SL(L))` and `U`.
  - `U^- ∩ P = 1`: `u^-_(S') a = a + S' a` lies in `L` only when `S' = 0`.
  - `m(SL(L)) ∩ U = 1`: Levi elements preserve `L'`.
- **Count.** So `|Q_0| >= q^(2 dim) |SL_m(q_F)|`, and `|SL_m(q_F)| >= (1/4) q_F^(m^2 - 1)`.
- **In terms of `n`.** Write `n = 2m + e_0` with `e_0 = dim V_0`.
  - (O): `n(n+1)/2 - E_0 = m(2 e_0 + 2) + e_0(e_0 + 1)/2 + 1 <= 3n + 4`.
  - (U): `n(n+1) - E_0 = 2m(2 e_0 + 1) + e_0(e_0 + 1) + 2 <= 3n + 4`.
  - (Sp): `n(n+1)/2 - E_0 = 1`.

## 3. Class sizes from the fixed space

**Lemma 3.1 (stabilizer count).** Let `E <= V` have codimension `s`, `T = E^perp`, and put
`r = dim(T ∩ E)`. Then
```text
|Stab_(I(V))(E)| <= q_F^(s(s+1)/2 + r s + (n-s)(n-s+1)/2) .
```

*Proof.*
- **Basis.** Choose a basis `e_1, ..., e_n` in three blocks: a basis of `T`; then vectors of `E`
  completing it to a basis of `T + E`; then the rest.
- **Counting images.** `g in Stab(E)` also stabilizes `T = E^perp`, and it is determined by the
  images `g e_i`. Given `g e_1, ..., g e_(i-1)`, the image `g e_i` lies in the block's subspace
  (`T`, `E` or `V`). It satisfies the `i - 1` equations `beta(g e_j, g e_i) = beta(e_j, e_i)`, which
  are `F`-linear in `g e_i`. The restricted functionals `beta(g e_j, ·)|_A` have rank at least
  `(i - 1) - dim(span(g e_(<i)) ∩ A^perp)`.
- **Block `T`** (`i <= s`). Here `span ⊆ T` and `T ∩ T^perp = T ∩ E` has dimension `r`. So there are
  at most `q_F^(s - i + 1 + r)` choices.
- **Block `E`.** Here `span ⊇ T = E^perp`, so the rank is at least `i - 1 - s`. So there are at most
  `q_F^((n - s) - (i - 1 - s)) = q_F^(n - i + 1)` choices.
- **Last block.** The rank is `i - 1`, giving at most `q_F^(n - i + 1)` choices.
- **Total.** Multiply over `i`.

**Lemma 3.2 (class size).** Let `n >= 8` and `k in I(V)` with `s = rk(k - 1) <= n/4`. Then
```text
|k^(Q_0)| >= (1/4) q^(s(n - 2s) - 3n - 4) >= (1/4) q^(s n/2 - 3n - 4) .
```

*Proof.*
- **Conjugates and fixed spaces.** The conjugate `g k g^-1` has fixed space `gE`, where
  `E = ker(k - 1)`. So `|k^(Q_0)| >= [Q_0 : Stab_(Q_0)(E)] >= |Q_0| / |Stab_(I(V))(E)|`.
- **Exponents.** By (P0), `codim E = s`. Use Lemmas 2.1 and 3.1 with `r <= s`.
  - (Sp): the exponent is at least `n(n+1)/2 - 1 - (n(n+1)/2 - s(n-s) + r s) >= s(n - 2s) - 1`.
  - (O): subtract a further `3n + 3`.
  - (U): the stabilizer count is in powers of `q_F = q^2`. The exponent is at least
    `n(n+1) - 3n - 4 - (n(n+1) - 2 s(n-s) + 2 r s) >= 2 s(n - 2s) - 3n - 4`.
- **Final form.** `s <= n/4` gives `n - 2s >= n/2`.

**Remark.** Lemma 3.2 costs `O(n)` in the exponent. So it bounds covering numbers only for elements of
support `s >= c n` in dimension `n >= C/c`. Bounded supports in bounded dimension are handled by the
minimal-degree argument in part 3.
