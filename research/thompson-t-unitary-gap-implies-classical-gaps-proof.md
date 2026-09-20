---
rg: 2
id: thompson-t-unitary-gap-implies-classical-gaps-proof
kind: route
title: Perturb a dense orthogonal or symplectic pair inside its SU conjugacy classes; the non-dense pairs nearby lie in the image of a map whose target has codimension H^1(Z/4 * Z/3; p) >= 1
target: thompson-t-unitary-gap-implies-orthogonal-and-symplectic-gaps
requires: []
artifacts:
  - experiments/thompson-t-classical-gap-collapse-2026-09-17/h1_census.py
---

Numbering follows the claim.

**Notation.**
- `G = SU(n)`, and `Gamma0 = Z/4 * Z/3 = <a, b>`.
- `K0` is `SO(k)` inside `SU(k)` with `n = k`, `k >= 3`, `k != 4`. Or `K0` is `Sp(m)` inside
  `SU(2m)` with `n = 2m`, `m >= 2`.
- `h = Lie K0`, and `p` is the orthogonal complement of `h` in `su(n)` for the trace form.
- `N = N_G(K0)` is the normalizer.
- For `x` in `G`, `C_x` is the `G`-conjugacy class of `x`, and `C^N_x` is the `N`-conjugacy class of
  `x` when `x` is in `N`.
- All dimensions are real dimensions. They equal the complex dimensions of complexifications, and the
  multiplicity counts below are done over `C`.

## Step 0. Representation theory of `su(n) = h (+) p`

The complexifications are:
- for `SO(k)`: `h_C = Lambda^2 C^k` and `p_C = Sym^2_0 C^k`;
- for `Sp(m)`: `h_C = Sym^2 C^(2m)` and `p_C = Lambda^2_0 C^(2m)`.

Here `Sym^2_0` and `Lambda^2_0` are the complements of the line spanned by the invariant bilinear
form.

For `k >= 3` with `k != 4`, and for `m >= 2`, the following hold.

- **Irreducibility.** `h` is simple, so `h_C` is irreducible. `p_C` is irreducible: it is the
  representation of highest weight `2 eps_1` for `SO(k)`, and `eps_1 + eps_2` for `Sp(m)`.
- **Non-isomorphism.** `h` and `p` are not isomorphic, because their dimensions differ:
  - `k(k-1)/2` against `k(k+1)/2 - 1`;
  - `m(2m+1)` against `m(2m-1) - 1`.
- **Invariant subspaces.** So the only `K0`-invariant subspaces of `su(n)` are `0`, `h`, `p` and
  `su(n)`.
- **`p` is not a subalgebra.** We have `[p, p] ⊆ h` and `[p, p] != 0`. For instance, two
  non-commuting real symmetric matrices `S_1, S_2` give `[i S_1, i S_2] != 0`, and similarly for `Sp`.
- **`K0` is irreducible on `C^n`.**
- **The normalizer.** The centralizer of `K0` in `G` consists of scalars, which form a finite group,
  and `Out(h)` is finite. So `N^0 = K0` and `dim N = dim h`.

## Step 1. Reduction of items 1 and 2 to items 3–5

**Lifting.** Let `tau : Gamma0 -> Inn(h)` have dense image. `Inn(h)` is `K0 / Z` with `Z` central
and of order at most 2. Lift `tau(a)` and `tau(b)` to `A, B` in `K0`. Then `A^4` and `B^3` are in
`Z = {1}` or `{+-1}`.

If `B^3 = -1`, then `-1` is in `K0`, and we replace `B` by `-B`. This does not change `tau`, and now
`B^3 = 1`.

**Density of the lift.** Let `K` be the closure of `<A, B>`. Its image in `K0/Z` is dense and
compact, hence all of `K0/Z`. So `K Z = K0`, and `K` has finite index in the connected group `K0`.
Hence `K = K0`.

**Perturbation.** By item 3, take `(A', B')` in `C_A x C_B` within distance `eta` of `(A, B)`, with
`<A', B'>` dense in `SU(n)`. Since `A'^4` is conjugate to the central element `A^4`, we get
`A'^4 = A^4`. Likewise `B'^3 = 1`. So `tau'(a) = Ad A'` and `tau'(b) = Ad B'` define a homomorphism
`tau' : Gamma0 -> PSU(n)`, and it has dense image.

**Norm comparison.** For each relator `r`, `r(A, B)` lies in `K0`. So

```text
||Ad_su r(A',B') - 1||  <=  ||Ad_su r(A,B) - 1|| + o_eta(1)
                        <=  c ||Ad_h r(A,B) - 1|| + o_eta(1)  =  c ||tau(r) - 1|| + o_eta(1),
```

with `c = 2` for `SO` and `c = 1` for `Sp`, by item 5. Here `o_eta(1)` tends to 0 as `eta -> 0`,
because a word map is continuous.

**Conclusion.** `Gap_T(SU)` gives `eps_SU <= D_su(tau') <= c D_h(tau) + o_eta(1)`. Letting
`eta -> 0` gives `D_h(tau) >= eps_SU / c`.

**Small cases.**
- `so(3) = su(2)` and `sp(1) = su(2)`, with the same adjoint groups and the same adjoint norms. So
  these cases are `Gap_T(SU)` for `k = 2`.
- `so(4)` is not simple and is excluded from `Gap_T(SO)`.

This proves items 1 and 2.

## Step 2. Item 3: the non-dense pairs near `(A, B)`

Let `(A, B)` be as in item 3. Put `X = C_A x C_B`. This is a compact real-analytic manifold, and

```text
dim X = 2 dim su(n) - dim su(n)^A - dim su(n)^B .
```

Call a pair in `X` **good** if it generates a dense subgroup of `G`, and **bad** otherwise.

Define

```text
Phi : G x C^N_A x C^N_B -> X,      Phi(g, x, y) = (g x g^-1, g y g^-1).
```

`C^N_A` and `C^N_B` are compact, since they are orbits of the compact group `N`.

### 2a. The image of `Phi` is a closed null set

**Closed.** The domain is compact, so the image is compact.

**Rank bound.** `Phi` is constant on the orbits of the free action
`n . (g, x, y) = (g n^-1, n x n^-1, n y n^-1)`. So its differential has rank at most

```text
dim G + dim C^N_A + dim C^N_B - dim N .
```

**Dimension of the `N`-classes.** `N^0 = K0` and `A` is in `K0`, so
`dim C^N_A = dim N - dim Z_N(A) = dim h - dim h^A`, and likewise for `B`.

**Codimension.** `A` and `B` preserve the decomposition `su(n) = h (+) p`, so
`su(n)^A = h^A (+) p^A`. Substituting,

```text
dim X - rank(Phi)  >=  (2 dim su - dim su^A - dim su^B) - (dim su + dim h - dim h^A - dim h^B)
                    =  dim p - dim p^A - dim p^B .
```

By Step 3 this is at least 1. So every point of the domain is critical. By Sard's theorem the image
of `Phi` has measure zero in `X`.

### 2b. There is a neighbourhood `U` of `(A, B)` in `X` with `U ∩ bad ⊆ Im Phi`

Suppose not. Then there are bad pairs `(A_j, B_j)` tending to `(A, B)` and lying outside `Im Phi`.
Let `H_j` be the closure of `<A_j, B_j>`. It is a proper closed subgroup of `G`, hence a compact Lie
group. After passing to a subsequence, one of two cases holds.

**Case 1: every `H_j` is finite.**
- By Jordan's theorem there is `J(n)` such that every finite subgroup of `U(n)` has an abelian normal
  subgroup of index at most `J(n)`.
- Put `M = J(n)!`. The quotient by that abelian subgroup has order at most `J(n)`, so `u^M` lies in
  the abelian subgroup for every `u` in `H_j`. Hence `[u^M, v^M] = 1` for all `u, v` in `H_j`.
- Apply this to `u = w_1(A_j, B_j)` and `v = w_2(A_j, B_j)` for arbitrary words `w_1, w_2`, and let
  `j -> infinity`. This gives `[w_1(A,B)^M, w_2(A,B)^M] = 1`.
- By density and continuity, `[x^M, y^M] = 1` for all `x, y` in `K0`.
- On a compact connected Lie group the power map `x -> x^M` is surjective, since every element lies
  in a maximal torus. So `K0` would be abelian, which it is not.

So this case cannot occur.

**Case 2: every `H_j` is infinite.**

*Setup.* Then `h_j = Lie H_j` is not 0. It is not `su(n)` either, since otherwise `H_j ⊇ G^0 = G`.
Pass to a subsequence with `dim h_j = d` constant and `h_j -> h_inf` in the Grassmannian `Gr(d, su(n))`.

*Identifying `h_inf`.* The conditions "is a subalgebra" and "is `Ad(x)`-invariant" are closed in `x`
and in the subspace. So `h_inf` is a subalgebra, invariant under `Ad A` and `Ad B`, hence under
`Ad K0`. By Step 0, and because `0 < d < dim su(n)` and `p` is not a subalgebra, `h_inf = h`.

*Conjugating `h_j` to `h`.* `h` is semisimple, so `H^1(h; su(n)/h) = 0` by Whitehead's first lemma.
By Richardson's rigidity theorem (R. W. Richardson, *A rigidity theorem for subalgebras of Lie and
associative algebras*, Illinois J. Math. 11 (1967) 92-110), every subalgebra close enough to `h` is
conjugate to `h`. So for large `j` we have `h_j = Ad(g_j) h` with `g_j` in `G`.

*Arranging `g_j -> 1`.* Pass to a subsequence with `g_j -> g_inf`. Then
`Ad(g_inf) h = lim h_j = h`, so `g_inf` is in `N_G(h) = N`. Replace `g_j` by `g_j g_inf^-1`. Now
`g_j -> 1`.

*Landing in `N`.*
- `H_j^0` is the connected subgroup with Lie algebra `h_j`, namely `g_j K0 g_j^-1`.
- `H_j` normalizes `H_j^0`, so `H_j ⊆ g_j N g_j^-1`.
- Put `x_j = g_j^-1 A_j g_j` and `y_j = g_j^-1 B_j g_j`. These lie in `N ∩ C_A` and `N ∩ C_B`, and
  they tend to `A` and `B`.

*Slice claim.* There is a neighbourhood `V` of `A` in `G` with `N ∩ C_A ∩ V ⊆ C^N_A`, and likewise
for `B`.

- `N`-components are open in `N`, so near `A` the set `N` coincides with the component `A K0`.
- Consider the conjugation action of `K0` on `A K0`. Since `Ad A` is orthogonal,
  `h = (1 - Ad A) h (+) h^A`.
- So, by the slice theorem, every `x` in `A K0` near `A` is `K0`-conjugate to `A exp(s)`, with `s`
  in `h^A` small.
- `s` commutes with `A`. Diagonalize `A` and `s` together. The eigenvalues of `A exp(s)` near an
  eigenvalue `lambda` of `A` are then the numbers `lambda e^(i sigma)`, where `sigma` runs over the
  eigenvalues of `s` on the `lambda`-eigenspace.
- If `x` is in `C_A`, these must all equal `lambda`. This uses that the spectrum of `A` is finite
  and that `s` is small.
- `s` is skew-Hermitian, so `s = 0`. Hence `x` is `K0`-conjugate to `A`.

*Contradiction.* For large `j`, `(x_j, y_j)` lies in `C^N_A x C^N_B`. So
`(A_j, B_j) = Phi(g_j, x_j, y_j)` lies in `Im Phi`, contrary to the choice of `(A_j, B_j)`.

### 2c. Conclusion of item 3

`U ∩ bad` lies in the closed null set `Im Phi`. So good pairs are dense in `U`.

- Take `(A', B')` good. It lies in `C_A x C_B`.
- A dense subgroup of `SU(n)` stays dense when read in `PSU(n)`.

This proves item 3, given Step 3.

## Step 3. Item 4: `H^1(Gamma0; p) >= 1`

### 3a. The identity and the reduction

**Mayer–Vietoris.** Apply Mayer–Vietoris to the Bass–Serre tree of `Z/4 * Z/3`. Finite groups have
no higher real cohomology. So for a finite-dimensional real module `W`,

```text
dim W^Gamma0 - dim H^1(Gamma0; W) = dim W^A + dim W^B - dim W .
```

**Fixed spaces vanish.** `A, B` generate a dense subgroup of `K0`, so
`p^Gamma0 = p^K0 = 0` and `h^Gamma0 = 0`. Hence `H^1(Gamma0; p) = dim p - dim p^A - dim p^B`, which
is the codimension found in 2a.

**Two consequences of density.**
- **(V)** `K0` is irreducible on `C^n`, and a common eigenvector of `A` and `B` would span an
  invariant line. Hence `m_lambda(A) + m_mu(B) <= n` for all eigenvalues `lambda` of `A` and `mu` of
  `B`. Here `m` denotes multiplicity.
- **(F)** `H^1(Gamma0; W) >= 0` for `W = h, p`, since the fixed spaces vanish. Moreover, if
  `dim p^A + dim p^B > dim p`, then `p^A ∩ p^B != 0`, which contradicts `p^Gamma0 = 0`.

**Multiplicity notation.**
- `M_A` is the largest multiplicity of an eigenvalue of `A` on `C^n`.
- `Q_A = sum_lambda m_lambda(A)^2`.
- `R_A = sum_lambda m_lambda(A) (M_A - m_lambda(A))`.
- `M_B`, `Q_B`, `R_B` are defined in the same way for `B`.

Then `Q_A = n M_A - R_A`.

Put `W = n^2 - Q_A - Q_B`. Since `dim su(n)^A = Q_A - 1`,

```text
H^1(Gamma0; su(n)) = W + 1,         W = n (n - M_A - M_B) + R_A + R_B  >=  0   by (V).
```

`H^1` is additive over `su = h (+) p`. So

```text
2 H^1(p) = W + 1 + (H^1(p) - H^1(h)),
```

and it suffices to compute the difference `H^1(p) - H^1(h)`.

**Diagonal counts.** For `g` in `K0` with eigenvalues `lambda_1, ..., lambda_n`, the fixed spaces on
`Sym^2 C^n` and `Lambda^2 C^n` count the pairs `i <= j`, respectively `i < j`, with
`lambda_i lambda_j = 1`. Their difference is `delta(g) = #{ i : lambda_i^2 = 1 }`. The invariant
form spans a fixed line in `Sym^2` for `SO`, and in `Lambda^2` for `Sp`.

### 3b. Orthogonal case, `n = k`

**Eigenvalues of `A`.**
- If `A^4 = 1`, the eigenvalues are `1`, `-1`, `i`, `-i`, with multiplicities `a`, `b`, `c`, `c`.
  Then `delta(A) = a + b = k - 2c`.
- If `A^4 = -1` (`k` even), the eigenvalues are the primitive 8th roots of unity, with multiplicities
  `c1, c1, c2, c2`. Then `delta(A) = 0`.

**Eigenvalues of `B`.** `B^3 = 1`. The eigenvalues are `1`, `omega`, `omega-bar`, with multiplicities
`d`, `e`, `e`. Then `delta(B) = d`.

**The difference.** From `dim p - dim h = k - 1`,

```text
H^1(p) - H^1(h) = (k - 1) + 2 - delta(A) - delta(B) = k + 1 - delta(A) - d .
```

This equals `2c + 1 - d` if `A^4 = 1`, and `2e + 1` if `A^4 = -1`.

- **`A^4 = -1`.** Then `2 H^1(p) = W + 2 + 2e >= 2`, and we are done.
- **`A^4 = 1`.** Then `2 H^1(p) = W + 2 + 2c - d`, so it suffices that `W >= d - 2c`.
  - If `d <= 2c`, this holds because `W >= 0`.
  - If `d > 2c`, it suffices to show `W >= d`. The cases are:
    - `e = 0`. Then `B = 1` and `M_B = k`, which contradicts (V).
    - `d > e >= 1`. Then `M_B = d >= 2`, and `R_B = 2 e (d - e) >= 2 (d - 1) >= d`.
    - `e > d`. Then `M_B = e`, and `R_B = d (e - d) >= d`.
    - `d = e`, so `k = 3d` and `M_B = d`.
      - If `M_A <= 2d - 1`, then `W >= k (k - M_A - M_B) >= k >= d`.
      - Otherwise `M_A = 2d` by (V). This cannot be `c`, since `2c <= k < 4d`. So one of `a, b`
        equals `2d`, and the remaining multiplicities sum to `d`, each at most `d`. Then
        `R_A >= d * d >= d`.

### 3c. Symplectic case, `n = 2m`, `m >= 2`

**Eigenvalues of `A`.**
- If `A^4 = 1`, the multiplicities are `2a, 2b, c, c` on `1, -1, i, -i`, with `a + b + c = m`.
  Then `delta(A) = 2a + 2b`.
- If `A^4 = -1`, the multiplicities are `c1, c1, c2, c2` on the primitive 8th roots, with
  `c1 + c2 = m`. Then `delta(A) = 0`.

**Eigenvalues of `B`.** The multiplicities are `d = 2 delta_0`, `e`, `e` on `1`, `omega`,
`omega-bar`, with `delta_0 + e = m`. Then `delta(B) = d`.

**The difference.** From `dim p - dim h = -2m - 1`,

```text
H^1(p) - H^1(h) = -2m - 1 + 2 + delta(A) + delta(B) .
```

This equals `1 - 2c + d` if `A^4 = 1`, and `1 - 2e` if `A^4 = -1`. So it suffices that `W >= 2c - d`,
respectively `W >= 2e`.

**Case `A^4 = 1`.** Assume `2c > d`.

- **`M_A` is `2a` or `2b`, and `M_A > c`.** The two `c`-blocks give `R_A >= 2 c (M_A - c) >= 2c`.
- **`M_A = c`, and `M_B = e > d`.**
  - Here `n - M_A - M_B = a + b + d/2`.
  - If this is at least 1, then `W >= n = 2a + 2b + 2c >= 2c`.
  - Otherwise `a = b = d = 0`. So `A^2 = -1`, `B` has no eigenvalue 1, and all blocks are equal,
    which gives `W = 0`. Then `2 H^1(p) = 2 - 2m < 0`, which contradicts (F).
- **`M_A = c`, and `M_B = d >= e`.**
  - If `n - c - d >= 1`, then `W >= n >= 2c`.
  - Otherwise `d = 2a + 2b + c` and `e = c/2`. So `c` is even, and
    `W >= R_B = 2 e (d - e) = c (2a + 2b + c/2)`.
  - This is at least `c - 2a - 2b = 2c - d`, because `c^2/2 >= c` for even `c >= 2`, and both sides
    vanish for `c = 0`.

**Case `A^4 = -1`.** Let `x = max(c1, c2)` and `y = min(c1, c2)`. Then `M_A = x`, and
`n = x + y + delta_0 + e`.

- **`M_B = e`.**
  - Here `n - M_A - M_B = y + delta_0`.
  - If this is at least 1, then `W >= n >= 2e`.
  - Otherwise `y = delta_0 = 0` and `W = 0`. Then `2 H^1(p) = 2 - 2m < 0`, which contradicts (F).
- **`M_B = d > e`.** Then `R_B = 2 e (d - e) >= 2e`.

This proves item 4.

**Census.** The artifact `h1_census.py` enumerates every multiplicity pattern satisfying (V) and
`H^1(h) >= 0`, for `3 <= k <= 200` with `k != 4`, and for `2 <= m <= 100`. It reports no pattern with
`H^1(p) = 0`.

The same enumeration with (V) alone, run as a scratch check, finds only two kinds of failures. Both
have `H^1(p) < 0` and are the two excluded families above:
- `A^2 = -1` with `B` having no eigenvalue 1;
- `A^4 = -1` with `c1 c2 = 0` and `B` having no eigenvalue 1.

## Step 4. Item 5: norm comparison

`Ad` of a unitary is unitary, so `||Ad(g) - 1||` is the largest distance from 1 to an eigenvalue of
`Ad(g)`.

**Orthogonal case.** Let `g` be in `SO(k)` with eigenvalues `e^(i theta_1), ..., e^(i theta_k)`.
These are closed under inversion. Choose an involution `sigma` of the index set with
`theta_sigma(j) = -theta_j`.

- On `so(k)_C = Lambda^2`, the eigenvalues are `e^(i(theta_i + theta_j))` for `i < j`.
- On `sl(k)`, the eigenvalues are `e^(i(theta_i - theta_j)) = e^(i(theta_i + theta_sigma(j)))`.
- **When `i != sigma(j)`.** This is a `Lambda^2` eigenvalue.
- **When `i = sigma(j)`.** The eigenvalue is `e^(2 i theta_i)`. Pick `l` outside `{i, sigma(i)}`,
  which is possible because `k >= 3`. Then

  ```text
  e^(2 i theta_i) = e^(i(theta_i + theta_l)) * e^(i(theta_i + theta_sigma(l))),
  ```

  and both factors are `Lambda^2` eigenvalues.
- For unit complex numbers, `|xy - 1| <= |x - 1| + |y - 1|`.
- Hence `||Ad_su(g) - 1|| <= 2 ||Ad_so(g) - 1||`.

**Symplectic case.** On `sp(m)_C = Sym^2`, the eigenvalues are `e^(i(theta_i + theta_j))` for
`i <= j`. Every `sl(2m)` eigenvalue `e^(i(theta_i + theta_sigma(j)))` is of this form, including
`i = sigma(j)`. So `||Ad_su(g) - 1|| <= ||Ad_sp(g) - 1||`.

This proves item 5 and completes the proof.
