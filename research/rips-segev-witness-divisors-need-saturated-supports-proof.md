---
rg: 2
id: rips-segev-witness-divisors-need-saturated-supports-proof
kind: route
title: Split witness elements by the 2x2 determinant; rank one factors, rank two turns every clean a-square into a contradiction, and Gamma realizes all extreme-coefficient data
target: rips-segev-witness-divisors-need-saturated-supports
requires: [rips-segev-witness-pairs-carry-no-zero-divisors, rips-segev-port-data-cannot-exclude-balanced-divisors]
---

**Conventions.**
- `G` is a torsion-free group, `a, b in G`, and `S = {1, a, b, ab}` has four distinct elements.  In the core `K`
  of a generalized Rips--Segev graph this holds, and `a, b, ab, a^{-1}b, b^{-1}ab` have infinite order (see
  `rips-segev-cores-have-no-infinite-cyclic-quotient-proof`, paragraph "In `K`").
- `beta = c_0 + c_1 a + c_2 b + c_3 ab` with `c_j in k`, `beta != 0`, and `D = c_0 c_3 - c_1 c_2`.
- For finite `X ⊆ G`, `Sigma ⊆ S` and `g in G`: `r_X(g)` is the number of pairs `(x, s) in X × S` with `x s = g`,
  and `r_{X,Sigma}(g)` the number with `s in Sigma`.  Likewise `l_X(g)`, `l_{X,Sigma}(g)` count pairs
  `(s, x)` with `s x = g`.

---

## 1. Rank one

**Lemma 1.**  If `D = 0` then `beta` is a non-zero-divisor in `k[G]`.

*Proof.*  `D = 0` says the matrix `M = [[c_0, c_2], [c_1, c_3]]` has rank one, since `beta = (1, a) M (1, b)^T`.
So `M = (x_0, x_1)^T (y_0, y_1)` with nonzero vectors, and `beta = (x_0 + x_1 a)(y_0 + y_1 b)`.  Each factor is
nonzero, with support of size one or two in a coset of `<a>` or `<b>`, so it is a unit or regular by Lemma 1.1 of
`rips-segev-cores-have-no-infinite-cyclic-quotient-proof`.  A product of non-zero-divisors is a non-zero-divisor. ∎

This covers every `beta` with at most two nonzero coefficients except `c_0 + c_3 ab` and `c_1 a + c_2 b`, which are
also regular by the same lemma (`ab` and `a^{-1} b` have infinite order).  Lemma 1 generalizes (T1) of
`rips-segev-witness-pairs-carry-no-zero-divisors` from four nonzero coefficients to any.

---

## 2. Rank two forces saturation

**Definition.**  Let `Sigma ⊆ S`.  A finite nonempty `X ⊆ G` is *right `Sigma`-saturated* if:
- (N) `r_{X,Sigma}(g) != 1` for every `g in X Sigma`;
- (C) for every `h in G` with `h, h a in X`: `r_X(h a) >= 3` or `r_X(h a b) >= 3`.

It is *left `Sigma`-saturated* if:
- (N') `l_{X,Sigma}(g) != 1` for every `g in Sigma X`;
- (C') for every `y in G` with `y, b y in X`: `l_X(b y) >= 3` or `l_X(a b y) >= 3`.

**Lemma 2.**  Suppose `D != 0`, `Sigma = supp beta` and `0 != alpha in k[G]`.
- (a) If `alpha beta = 0` then `supp alpha` is right `Sigma`-saturated.
- (b) If `beta alpha = 0` then `supp alpha` is left `Sigma`-saturated.

*Proof of (a).*  Put `X = supp alpha`.
- (N).  If `g = x s` with `s in Sigma` is the only such expression, the coefficient of `g` in `alpha beta` is
  `alpha(x) c_s != 0`.
- (C).  Let `h, h a in X`.  In `X × S`, the element `h a` has the expressions `(h a, 1)` and `(h, a)`.  The element
  `h a b` has `(h a, b)` and `(h, a b)`.  These are distinct pairs because `S` has four elements.  Suppose each of
  `h a` and `h a b` has no further expression in `X × S`.  The coefficients of `alpha beta` there give

      c_0 alpha(h a) + c_1 alpha(h) = 0,      c_2 alpha(h a) + c_3 alpha(h) = 0.

  (A pair with `c_s = 0` contributes zero, so the equations hold as written.)  The vector
  `(alpha(h a), alpha(h))` is nonzero, so the determinant `c_0 c_3 - c_1 c_2 = D` vanishes.  This is a
  contradiction.

*Proof of (b).*  The same with products `s x`.  For `y, b y in X`: `b y = 1 · (b y) = b · y` and
`a b y = a · (b y) = (a b) · y`.  The coefficients give `c_0 alpha(b y) + c_2 alpha(y) = 0` and
`c_1 alpha(b y) + c_3 alpha(y) = 0`, with determinant `D`. ∎

*Remark.*  (C) in the case `supp alpha = A` is exactly the "clean square" argument (T2) of
`rips-segev-witness-pairs-carry-no-zero-divisors`, and the gap argument of
`rips-segev-witness-supports-carry-no-zero-divisors`.  The point here is that it applies to every `alpha`.  Two support points `x, x'` share two products
`x s_1 = x' s_2`, `x s_3 = x' s_4` only if `s_1 s_2^{-1} = s_3 s_4^{-1}`.  In the free group on `a, b` the only
solution among distinct pairs of `S` is `1 · a^{-1} = b (ab)^{-1}` (and its reverse).  So (C) is the only
determinant constraint from a pair of support points that is present in every group.

---

## 3. Extreme coefficients carry no information

Let `beta` have all four coefficients nonzero, and write `beta = u + w b`, `u = c_0 + c_1 a`, `w = c_2 + c_3 a`.
Then `u_± = w_±`, so the offsets of `rips-segev-core-large-gap-two-layer-elements-are-regular` are `(0, 0)`.

**Extreme identities.**  Suppose `alpha beta = 0`.  For a left `<a>`-coset `T` meeting `supp alpha`, let `tau_T`
and `sigma_T` be the top and bottom coefficients of `alpha_T`, and `y_T`, `z_T` the top and bottom points of
`In_T = supp(alpha_T u)` and `Out_T = supp(alpha_T w)`, which coincide.  Then
- `(alpha u)(y_T) = c_1 tau_T`, `(alpha w)(y_T) = c_3 tau_T`;
- `(alpha u)(z_T) = c_0 sigma_T`, `(alpha w)(z_T) = c_2 sigma_T`.

The zero product reads `(alpha u)(g) = - (alpha w)(g b^{-1})` for all `g`.  At extreme points it gives an
*extreme coincidence equation* whenever `e b = e'` with `e in {y_T, z_T}` and `e' in {y_{T'}, z_{T'}}`, for instance
`c_1 tau_{T'} = - c_3 tau_T` when `y_T b = y_{T'}`.

*Extreme-coefficient data* means a port configuration with offsets `(0, 0)` (conditions (P1), (P2)), together with
nonzero scalars `tau_T, sigma_T` satisfying all extreme coincidence equations.

**Proposition 3.**  Suppose every line endpoint position `0, C_i` of `Gamma` is both a source and a target of
`b`-edges, and no `b`-edge joins two endpoint positions.  Then `Gamma`'s port configuration in `K`, with
**arbitrary** nonzero scalars `tau_T, sigma_T`, is extreme-coefficient data for every `(c_0, ..., c_3)` with all
entries nonzero.  Steenbock's explicit graphs satisfy the hypotheses.

*Proof.*
- The port configuration is Part 1 of `rips-segev-port-data-cannot-exclude-balanced-divisors-proof`:
  `Out_T = Src ∩ T`, `In_T = Tgt ∩ T`, offsets `(0, 0)`.  Its extreme points are images `g(v)` of line endpoints
  `v = v_{i0}` or `v_{i C_i}`.
- Let `e = g(v)` be an extreme out-point.  Then `e b = g(v')`, where `v'` is the head of the `b`-edge leaving `v`.  By
  hypothesis `v'` is not a line endpoint.
- An extreme in-point `e'` is `g(v'')` for a line endpoint `v''`.  Since `g` is injective on vertices (Steenbock,
  Theorem "gi"), `e b = e'` would force `v' = v''`, which is impossible.
- So there are no extreme coincidences, no equations, and every choice of scalars is admissible.
- *Steenbock's graphs.*  The labels `x_{i1} = b a^{-I_i1}` (source `0`, target `I_i1`), `x_{i2} = a^{C} b a^{-I_i2}`
  (source `C`, target `I_i2`), `y_{i3} = a^{O_i1} b a^{-C}` (source `O_i1`, target `C`), `y_{i4} = a^{O_i2} b`
  (source `O_i2`, target `0`).  Endpoint sources go to the interior targets `I_i1, I_i2`, and endpoint targets come
  from the interior sources `O_i1, O_i2`.  The Rips--Segev condition puts `I`, `O` strictly between `0` and `C`. ∎

**Consequence.**  No argument that uses only ports and extreme coefficients excludes a witness zero divisor.  Such
an argument would not even see `D`: Proposition 3 holds for `D = 0`, where regularity is true (Lemma 1), and for
`D != 0` alike.  So a proof must use interior coefficients.  Lemma 2 (C) is the interior constraint that sees `D`.

**Contrast with the port obstruction.**  The configuration realizing the port data is `Gamma` itself.  Its support
`A` (the union of the lines) is **not** saturated: a line interior index between consecutive distinguished
positions is a clean a-square (step 2 of `rips-segev-witness-supports-carry-no-zero-divisors-proof`).  So the port
obstruction does not extend to supports satisfying (C).

---

## 4. The reduction

**Theorem 4.**  Call `Sigma ⊆ S` *rank-two admissible* if it contains `{1, ab}` or `{a, b}`; these are the supports
of the `beta` with `D != 0`.  Suppose that for every rank-two admissible `Sigma`, `K` has no finite nonempty right
`Sigma`-saturated subset and no finite nonempty left `Sigma`-saturated subset.  Then every element of `k[K]`
supported on `{1, a, b, ab}` is a non-zero-divisor, for every field `k`.  The same then holds in `k[G(Gamma)]` for
every generalized Rips--Segev group over `Gamma`.

*Proof.*  Rank one is Lemma 1.  For rank two, a nonzero annihilator has saturated support by Lemma 2.  For
`G(Gamma)`, decompose `alpha` over cosets of `K`: a nonzero component `alpha_j in k[K]` annihilates `beta`
(`rips-segev-core-large-gap-two-layer-elements-are-regular-proof`, transfer paragraph). ∎

Only this direction is claimed: a saturated set need not carry a zero divisor.  Saturation is a statement about
finite subsets of `K`, with no field and no coefficients.

**Calibration.**
- *Unique-product groups.*  If `G` has unique products (for example `F_2`, the core of a cycle-free `Gamma`), no
  finite nonempty `X` satisfies (N) for any `Sigma` with `|Sigma| >= 2`: some product of `X Sigma` is unique.
  Consistent with regularity there.
- *Condition (N) alone is not enough in `K`.*  The witness `A` satisfies (N) with `Sigma = S` in `K`, since `K` has
  no unique products.  It fails (C), by Section 3.  So (C) carries the content of the reduction.
- *Torsion.*  In `Z/2 x Z/2 = <a, b>` put `beta = 1 + a + b - 3ab` over `Q` (`D = -4`) and
  `alpha = 1 + a + b + ab`.  Then `alpha beta = alpha · (1 + 1 + 1 - 3) = 0`.  Its support `X = {1, a, b, ab}` is
  right `S`-saturated: every product of `X S` has `r_X = 4`.  Saturated sets carrying rank-two zero divisors
  exist once torsion is allowed, so Theorem 4 is not vacuous.
