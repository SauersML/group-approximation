---
rg: 2
id: kms-hc1-iwahori-h2-serre-plus-kassel-all-degrees-proof
kind: route
title: Weight-by-weight 2-cocycle elimination on the Iwahori Lie algebra (four root-system types), closed by the exact integral table in degree <= 13 and by Kostant's Laplacian for the integral exponent
target: kms-hc1-iwahori-h2-serre-plus-kassel-all-degrees
requires: [kms-hc1-iwahori-integral-h2-serre-plus-hc1, kms-hc1-a2-iwahori-towers-deviate-only-at-kassel-degrees]
artifacts:
  - experiments/kms-hc1-iwahori-h2-all-degrees-2026-09-18/cocycle_check.py
  - experiments/kms-hc1-iwahori-h2-all-degrees-2026-09-18/cocycle90.out
  - experiments/kms-hc1-iwahori-laplacian-2026-09-17/lap.py
  - experiments/kms-hc1-iwahori-laplacian-2026-09-17/linkage.py
  - experiments/kms-hc1-iwahori-laplacian-2026-09-17/h2z120.out
---

Notation of the target claim. Fix a prime `p >= 5` and work over `F_p`.

## 0. Set-up

**Basis.**

- For a finite root `alpha` of `A_2`, put `e_alpha(a) = t^a E_alpha`. It has
  weight `alpha + a delta` and exists for `a >= eps(alpha)`, where
  `eps(alpha) = 0` if `alpha > 0` and `1` if `alpha < 0`.
- For `H` in the Cartan `h` of `sl_3`, put `H(a) = t^a H`, of weight
  `a delta`, for `a >= 1`.
- `H_alpha = [E_alpha, E_-alpha]` is the coroot. `(X,Y) = tr(XY)` on `h`
  satisfies `(H_alpha, H) = alpha(H)`.

**Duality.** Weight spaces are finite dimensional. So `H_2(L_p)_mu` is dual
to `H^2_mu`, the cohomology at weight `mu` of the complex of alternating
forms. A 2-cochain of weight `mu` is an alternating form `omega` that is
nonzero only on pairs of total weight `mu`. It is a cocycle iff, for every
triple `(x,y,z)` of weight `mu`,

```text
omega([x,y],z) - omega([x,z],y) + omega([y,z],x) = 0.
```

The coboundaries are `(delta phi)(x,y) = phi([x,y])` for `phi` in
`(L_p)_mu^*`.

**Two linear-algebra facts, used repeatedly.**

- (I) If `p != 3`, any two distinct roots `gamma, gamma'` with
  `gamma != -gamma'` are linearly independent functionals on `h (x) F_p`.
  Their pairing matrix with `h_1, h_2` has determinant `+-3`.
- (I') Any two non-proportional coroots span `h (x) F_p` for every `p`,
  since they form a basis of the coroot lattice.

**Root-system count.** The weights of `Lambda^2 L` have
`Q(nu)` in `{0,1,3,4}`:

- `Q = 0`: `nu = 0`;
- `Q = 1`: `nu` a root;
- `Q = 3`: `nu = gamma + gamma'` with `(gamma,gamma') = 1`;
- `Q = 4`: `nu = 2 alpha`.

For `Q = 3`, and for `nu = beta` a root, the decomposition as a sum of two
roots is unique (a direct check on the six roots). `linkage.py support`
asserts the list of `Q` values on the enumerated weights.

**Small `m`.** `Q <= 4` forces `x + y <= 4`, so `deg = 3m + x + y <= 13` when
`m <= 3`. Every such weight is in the exact integral table (Z2) of
`kms-hc1-iwahori-integral-h2-serre-plus-hc1` (degree `<= 90`, recomputed to
120 in `h2z120.out`: `check_pattern.py` reports 282 weights, 0 anomalies).
By (Z1) (UCT), `H_2(L_p)` at those weights is as stated in (A1) for every
`p >= 5`. From now on `m >= 4`.

## 1. `nu = 0`: `mu = n delta`, `n >= 4`

**Unknowns.**

- `Phi_alpha(u) = omega(e_alpha(u), e_-alpha(n-u))` for `alpha > 0` and
  `0 <= u <= n-1`.
- `G(v)(H,H') = omega(H(v), H'(n-v))` for `1 <= v <= n-1`. Antisymmetry of
  `omega` gives `G(v)(H,H') = -G(n-v)(H',H)`.

**Triples with one Cartan factor.** Take `(H(a), e_alpha(b), e_-alpha(c))`
with `a >= 1`, `b >= 0`, `c >= 1`, `a+b+c = n`. The cocycle condition is

```text
alpha(H) [Phi_alpha(a+b) - Phi_alpha(b)] + G(n-a)(H_alpha, H) = 0.
```

- Take `a = 1` and `alpha(H) != 0`. Then `Phi_alpha(b+1) - Phi_alpha(b)` is
  independent of `b`, so `Phi_alpha(u) = A_alpha + B_alpha u`.
- It follows that `G(v)(H_alpha, H) = -(n-v) alpha(H) B_alpha`.
- Additivity in the first argument, applied to
  `H_{alpha_1+alpha_2} = H_{alpha_1} + H_{alpha_2}` at `v = n-1`, gives
  `alpha_1 (B_13 - B_12) + alpha_2 (B_13 - B_23) = 0` on `h`. By (I),
  `B_12 = B_23 = B_13 = B`.
- The coroots span `h`, so `G(v)(X,Y) = -(n-v) B tr(XY)`.
- Antisymmetry then gives `-(n-v)B = vB`, i.e. `n B = 0`.

**Triples of three root vectors, pairwise non-opposite.** Take
`(e_12(a), e_23(b), e_31(c))` with `c >= 1`. It gives
`Phi_13(a+b) - Phi_23(b) - Phi_12(a) = 0`, i.e. `A_13 = A_12 + A_23`.

**Coboundaries.** `(L_p)_{n delta} = span(h_1(n), h_2(n))`, and
`delta phi` has `Phi_alpha(u) = phi(H_alpha(n))` and `G = 0`. So the
coboundaries are exactly the 2-dimensional space of offsets
`(A_12, A_23, A_12 + A_23)`, with `B = 0`.

**Result.** `dim H^2_{n delta} <= [p | n]`. Equality holds by (K): for
`n = mp`, the Kassel cocycle is `Phi(u) = u`.

## 2. `Q = 4`: `mu = 2 alpha + m delta`

**Unknowns.** The only pairs are `e_alpha(u) ^ e_alpha(m-u)`. Since
`2 alpha + m delta` is not a root, there are no coboundaries. Put
`w(u) = omega(e_alpha(u), e_alpha(m-u))` for `u` in
`[eps, m - eps]`, `eps = eps(alpha)`.

**Cartan triples.** The triple `(H(c), e_alpha(a), e_alpha(b))` gives
`alpha(H) [w(a+c) + w(a)] = 0`. So `w(u') = -w(u)` for all `u < u'` in the
range.

**Result.** For `m >= 4` the range has at least 3 points `u < u' < u''`.
Then `w(u) = -w(u') = w(u'') = -w(u)`, so `2w = 0` and `w = 0`, since `p` is
odd. Hence `H^2 = 0`.

## 3. `Q = 3`: `mu = gamma + gamma' + m delta`

**Unknowns.** The decomposition `nu = gamma + gamma'` is unique, so the pairs
are `e_gamma(a) ^ e_gamma'(m-a)`. Put
`V(a) = omega(e_gamma(a), e_gamma'(m-a))`. Since `nu` is not a root,
`[E_gamma, E_gamma'] = 0` and there are no coboundaries.

**Cartan triples.** The triple `(H(c), e_gamma(a), e_gamma'(b))` gives
`gamma(H) V(a+c) + gamma'(H) V(a) = 0` for all `H`. By (I),
`V(a) = V(a+c) = 0`. For `m >= 3` every index is some `a` or some `a+c`.

**Result.** `H^2 = 0`. At `p = 3`, (I) fails. This is the `(Z/3)^6` family
at `n delta + alpha_i - alpha_j` (`i != j` in `{0,1,2}`), which are exactly
the `Q = 3` weights.

## 4. `nu = beta` a root: `mu = beta + m delta`

**Unknowns.** Write `beta = gamma + gamma'` (unique, `(gamma,gamma') = -1`)
and `eps = eps(beta)`. The pairs are of two kinds:

- `e_beta(u) ^ H(m-u)` for `eps <= u <= m-1`, with unknown
  `P(u) = omega(e_beta(u), (.)(m-u))` in `h^*`;
- `e_gamma(a) ^ e_gamma'(m-a)`, with unknown `R(a)`.

The coboundaries form a 1-dimensional space: `phi = s e_beta(m)^*` gives
`P(u) = -s beta` for all `u`, and `R = s N_{gamma,gamma'}`.

**(Ta)** The triple `(H(c), H'(c'), e_beta(u))`, with `c, c' >= 1`, gives
`beta(H) P(u+c)(H') = beta(H') P(u+c')(H)`.

- Taking `H'` in `ker beta` gives `P(v)(ker beta) = 0` on the interior
  `eps+1 <= v <= m-1`.
- Taking `H = H'` with `beta(H) != 0`, and `v' = m-1`, gives
  `P(v) = P(m-1)` on the interior. So `P` equals a fixed multiple of `beta`
  there.
- Subtract the coboundary with that multiple. Now `P = 0` on the interior.
  Only the boundary value `P(eps)` remains, and `P(eps)` does not occur in
  (Ta).

**(Tb)** The triple `(H(c), e_gamma(a), e_gamma'(b))` gives
`gamma(H) R(a+c) + gamma'(H) R(a) + N P(a+b)(H) = 0`.

- When `a+b` is interior, (I) gives `R(a+c) = R(a) = 0`.
- For `m >= 4` every index of `R` occurs in this way. Indices
  `u <= m-1-eps(gamma')` occur as `a` with
  `b = max(eps(gamma'), eps+1-u)`. The top index occurs as `a+c` with
  `b = eps(gamma')`. So `R = 0`.

**(Tc)** The triple `(e_beta(eps), e_beta(b), e_-beta(c))`, with `b`
interior, gives `P(b)(H_beta) - P(eps)(H_beta) = 0`, so
`P(eps)(H_beta) = 0`.

**(Tc')** Take the triple `(e_beta(eps), e_alpha(b), e_-alpha(c))` with
`alpha != +-beta`. Its terms other than `P(eps)(H_alpha)` are brackets
`e_{beta +- alpha} ^ e_{-+alpha}`. Such a pair has finite parts summing to
`beta`, so it is an `R` pair (0), or the bracket vanishes. Hence
`P(eps)(H_alpha) = 0`.

**Result.** By (I'), `P(eps) = 0`. So `omega` is a coboundary and `H^2 = 0`.

## 5. Machine confirmation of the elimination

`cocycle_check.py MAXDEG p...` builds, for every weight with `m >= 4`, only
the cocycle rows of the triple shapes used above:

| type | triples used |
| --- | --- |
| `nu = 0` | Cartan triples, and root triples with no opposite pair |
| `nu` a root | Cartan triples, and root triples with an opposite pair |
| `Q = 3, 4` | Cartan triples only |

It computes `#pairs - rank(selected rows) - rank(d_2)` over `F_p`. This is an
upper bound for `dim H^2`, and the proof predicts it equals `[nu=0][p|m]`.
`cocycle90.out` records `cocycle_check.py 90 5 7 11 13 17 19`: 3042
(weight, p) pairs, 0 differ, in 40 s. This checks every case division and
index-range claim of sections 1--4 in the range, independently of the full
Chevalley--Eilenberg computation.

## 6. (A1)

- Sections 1--4 give `H^2_mu = [nu=0][p|m]` for `m >= 4`.
- Section 0 gives the weights with `m <= 3`, including the six Serre weights
  (rank 1 each by (Z2)).
- Dualize. By (Z1), `H_2(L_p)_mu = (H^2_mu)^*`.

Summing by degree, `D_p = {3} + 3pN` with dimensions 6 and 1.

## 7. (A4) The Laplacian

This section is used only in (A2).

**The form.** `B(u,v) = -(u, omega_Ch v)`, where `omega_Ch` is the Chevalley
involution. It is contravariant, `B([u,v],w) = -B(v,[omega_Ch u, w])`, and
positive definite on `n^+ = L_Q`. On the basis:

- `B(t^a E_ij, t^b E_kl) = [a=b][(i,j)=(k,l)]`;
- `B(t^a h_r, t^b h_s) = [a=b] A_rs`.

**The identity.** Kostant (Ann. of Math. 74 (1961)), in the Kac--Moody form
of Garland--Lepowsky (Invent. Math. 34 (1976)), gives

```text
d d* + d* d = (1/2)((rho,rho) - (rho-mu,rho-mu)) = (rho,mu) - (mu,mu)/2 = c(mu)
```

on `Lambda^*(n^+)_mu`.

**Integrality.** The Gram matrices are block diagonal, with 1-blocks and
exterior powers of `A`, whose determinant is 3. So `d*` has entries in
`Z[1/3]`, and `d*` is a chain homotopy from `c(mu) Id` to 0 on
`Lambda^*(L_Z)_mu (x) Z[1/3]`. Reducing mod `p != 3`, `d*/c(mu)` contracts
the complex when `p !| c(mu)`.

**Checks.**

- `lap.py 36` compares `d d* + d* d` with `c(mu) Id` exactly (FLINT
  rationals) for `j = 1,2`: 300 blocks, 0 bad. This fixes the normalization
  by computation.
- `linkage.py check h2z120.out`: 282 weights, 0 violations.
- `linkage.py support` lists the candidate degrees. It confirms that `Q` is
  in `{0,1,3,4}` and that no weight of degree `> 3` has `c = 0`.

## 8. (A2)

Fix `p >= 5`. By (A1) and (Z1), `Tors H_2(L_Z)` has exactly one invariant
factor divisible by `p` at each `n delta` with `p | n`, and none elsewhere.
So the `p`-part `T_p` of `H_2(L_Z)_{n delta}` is cyclic.

**Surjection onto `Z/n`.**

- The form `omega_n(t^a X, t^b Y) = a tr(XY) [a+b=n]` is antisymmetric mod
  `n`, since `b = n - a`.
- Its cyclic sum is `2n tr([X,Y]Z) = 0` mod `n`, so it is a `Z/n`-valued
  2-cocycle on `L_Z`.
- The coboundaries at `n delta` are constant in `u` on the pairs
  `e_alpha(u) ^ e_-alpha(n-u)`, while `k omega_n` takes the value `k u`. So
  the class has order exactly `n`.
- `H_1(L_Z)_{n delta} = 0`, so UCT gives
  `H^2(L_Z; Z/n)_{n delta} = Hom(H_2(L_Z)_{n delta}, Z/n)`. So
  `H_2(L_Z)_{n delta}` maps onto `Z/n`, and `T_p` maps onto
  `Z/p^{v_p(n)}`.

**Exponent.** By (A4), `T_p` is killed by `3n`, i.e. by `p^{v_p(n)}`.

**Result.** `T_p = Z/p^{v_p(n)}`. For the free part: at every weight other
than the six Serre weights, some `p >= 5` has `p !| n` (or `nu != 0`), so
`H_2(L_p) = 0` there and the rank is 0. This proves the display of (A2).

## 9. (A3) and (A5)

**(A3).** By (Z5), the towers agree through class 3. The least element of
`D_p` above 3 is `3p`, by (A1). So by (B), `gr_k(Gamma^) = gr_k(I_1)` for
`k <= 3p-1`, i.e. `|Gamma/P_k| = |I_1/P_k|` for `k <= 3p`. The factorization
of p-class `<= 3p-1` images through `I_1` is as in (Z5).

**(A5).** Suppose the towers agree through class `3mp - 1`. Then (B) and
(A1) bound the excess at `3mp` by 1. If the excess is 0, (B) again gives
agreement through `3(m+1)p - 1`. So the towers agree in all classes, which is
`phi^` iso by the criterion claim, iff the excess vanishes at every `3mp`.
That is Open statement 2.
