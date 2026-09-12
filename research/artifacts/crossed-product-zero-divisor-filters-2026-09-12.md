# Zero-divisor filters for Cohn-family witnesses in the odd-measure crossed product

Lane `w4-cohn-gram`, 2026-09-12. Supports `mixed-depth-leavitt-lift-is-a-left-zero-divisor` (Section 1).
Later sections support the filters named there. Targets they bear on:
`ternary-anti-central-summand-has-cohn-family` and
`odd-measure-crossed-product-unit-below-cylinder-idempotent`.

## 0. Setup

Notation follows `research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md` and
`research/artifacts/ternary-cohn-mixed-depth-lifts-2026-09-12.md`.
- `G = L_(F_3)(1,2)^x`, `S_- = eps_- F_3[G]`, `H = E x| V`, and
  `B = F_3[H] eps_- ~= C(M_-, F_3) x|_alg V ⊆ S_-`.
- `U_C = { mu in M_- : mu(C) = 1 }`, `P_C = 1_(U_C)`, and `g U_C = U_(gC)`.
- Conventions: `[g] f [g]^-1 = g.f` with `(g.f)(mu) = f(g^-1 mu)`. So `[g] 1_U = 1_(gU) [g]` and
  `1_U [g] = [g] 1_(g^-1 U)`.
- The linear map `* : [g] -> [g^-1]` is an anti-automorphism of `F_3[G]`. It fixes `eps_-` and every
  function in `C(M_-, F_3)`, and on `B` reads `([g] f)* = f [g^-1]`.
- Every `x in B` has a unique form `x = sum_(g in F) [g] b_g` with `F ⊆ V` finite and
  `b_g in C(M_-, F_3)`.

A ring element `x` is a *left zero divisor* if `x y = 0` for some `y != 0`. It is then not left
invertible in any ring containing both: `z x = 1` would give `y = z x y = 0`.

## 1. The mixed-depth lift is a left zero divisor

Take the data of Lemma 2.1 of the mixed-depth artifact: Thompson units `g_0, g_1` with
`g_0(0x) = 00x` and `g_1(1x) = 01x`, and

```text
sigma = [g_0] P_0 + [g_1] P_1,        tau = [g_0^-1] P_00 + [g_1^-1] P_01,
A = g_1^-1(00),   B' = g_0^-1(01),   h = g_0^-1 g_1,
W_1 = U_A ∩ U_1,   W_2 = U_0 ∩ U_(B'),   F = 1_(W_1) + 1_(W_2),   D = [h]1_(W_1) + [h^-1]1_(W_2),
e' = 2(F - D).
```

**Proposition 1.1.** For every choice of `g_0, g_1`:
1. `sigma F = sigma D = [g_1] 1_(W_1) + [g_0] 1_(W_2)`, so `sigma e' = 0`.
2. `tau = sigma*`, `D* = D` and `e'* = e'`, so `e' tau = 0`.
3. `e' != 0`. Hence `e'` is not in `S_- sigma`, `sigma` is not left invertible in any ring containing
   `B`, and `tau` is not right invertible in any such ring.
4. No `2 x 2` Gram matrix `[tau_i sigma_j]` over any ring containing `B` is invertible when some
   `sigma_j = sigma` or some `tau_i = tau`, whatever the other three entries are.

*Proof.* The set computations below use `mu(X) = 1` and additivity mod 2. From the definitions,
`h(A) = 0`, `h(1) = B'`, `h(0) = 0 ∪ (1 \ B')`, `h^-1(0) = A` and `h^-1(1) = 1 ∪ (0 \ A)`
(Lemma 2.1, item 2, of the mixed-depth artifact).

*Item 1, `sigma F`.* `W_2 ⊆ U_0`, `W_1 ⊆ U_1` and `U_0 ∩ U_1 = ∅`. So
`[g_0] P_0 F = [g_0] 1_(W_2)` and `[g_1] P_1 F = [g_1] 1_(W_1)`.

*Item 1, `sigma D`, four terms.*
- `[g_0] P_0 [h] 1_(W_1) = [g_0 h] 1_(U_(h^-1(0)) ∩ W_1) = [g_1] 1_(U_A ∩ W_1) = [g_1] 1_(W_1)`.
- `[g_0] P_0 [h^-1] 1_(W_2) = [g_0 h^-1] 1_(U_(h(0)) ∩ W_2)`. For `mu in W_2`: `mu(0) = 1` and
  `mu(B') = 1`, so `mu(1) = 0`, `mu(1 \ B') = 1` and `mu(0 ∪ (1 \ B')) = 0`. The set is empty.
- `[g_1] P_1 [h] 1_(W_1) = [g_1 h] 1_(U_(h^-1(1)) ∩ W_1)`. For `mu in W_1`: `mu(A) = mu(1) = 1`, so
  `mu(0) = 0`, `mu(0 \ A) = 1` and `mu(1 ∪ (0 \ A)) = 0`. The set is empty.
- `[g_1] P_1 [h^-1] 1_(W_2) = [g_1 h^-1] 1_(U_(h(1)) ∩ W_2) = [g_0] 1_(U_(B') ∩ W_2) = [g_0] 1_(W_2)`,
  since `g_1 h^-1 = g_0`.

So `sigma D = [g_1] 1_(W_1) + [g_0] 1_(W_2) = sigma F`, and `sigma e' = 2 sigma (F - D) = 0`.

*Item 2.* `sigma* = P_0 [g_0^-1] + P_1 [g_1^-1] = [g_0^-1] 1_(U_(g_0(0))) + [g_1^-1] 1_(U_(g_1(1)))
= [g_0^-1] P_00 + [g_1^-1] P_01 = tau`. Next `([h] 1_(W_1))* = 1_(W_1) [h^-1] = [h^-1] 1_(h W_1)
= [h^-1] 1_(W_2)`, and symmetrically `([h^-1] 1_(W_2))* = [h] 1_(W_1)`, because `h W_1 = W_2`. So
`D* = D` and `e'* = e'`. Applying `*` to `sigma e' = 0` gives `e' tau = 0`.

*Item 3.* The identity grade of `e'` is `2F`, a nonzero function, because `W_1` and `W_2` are nonempty
(Lemma 2.1, item 1). If `z sigma = eps_-` then `e' = z sigma e' = 0`. The right-hand statement for
`tau` is the image of this under `*`.

*Item 4.* Put `Sigma = (sigma_1, sigma_2)` and `T = (tau_1, tau_2)^t`, so the Gram matrix is `T Sigma`.
If `T Sigma` has an inverse `N`, then `(N T) Sigma = I_2`, so `Sigma` is left invertible as a map on
column vectors. But `Sigma` kills the column with `e'` in slot `j` and `0` in the other slot. Dually
`T (Sigma N) = I_2`, and the row with `e'` in slot `i` kills `T`. QED

**Remarks.**
- The same computation with first letters exchanged (`g_0(0x) = 10x`, `g_1(1x) = 11x`) shows the
  natural lift of `s_1` is a left zero divisor too. Section 3 derives both from a general dichotomy.
- `tau sigma = 1 + D` and `(1 + D) e' = e' + D e' = e' - e' = 0`, which is consistent with item 1.
- On a generic orbit, `sigma` sends the two points `mu in W_2` and `h^-1 mu in W_1` to the single point
  `g_0 mu` of `U_00 ∩ U_01`. The vector `delta_mu - delta_(h^-1 mu)` is killed, and `e'` is the ring-level
  form of that kernel vector.
- The correction `tau''` of Lemma 2.1 cannot be completed to a left inverse: the defect `e'` is not
  removable, it is annihilated.

## 2. Fibre operators detect zero divisors

For `mu in M_-` define `rho_mu : B -> End(F_3[V])` on the basis `delta_k` (`k in V`) by
`rho_mu([g]) delta_k = delta_(gk)` and `rho_mu(f) delta_k = f(k mu) delta_k`.
- *Covariance.* `rho_mu([g] f [g]^-1) delta_k = f(g^-1 k mu) delta_k = rho_mu(g.f) delta_k`. So `rho_mu`
  is a representation of the crossed product, and `rho_mu(eps_-) = 1`.
- *Fibre operators.* For `x = sum_g [g] b_g`, write `x_mu = rho_mu(x)`:
  `x_mu delta_k = sum_g b_g(k mu) delta_(gk)`. This is a finite-radius linear operator on `F_3[V]` whose
  coefficients read the orbit of `mu`.
- *Orbit modules.* `delta_k -> delta_(k mu)` intertwines `rho_mu` with the orbit module `l_fin(V mu)`,
  where `[g]` moves points and functions act by evaluation. It is an isomorphism when `mu` has trivial
  stabilizer, which holds for `lambda`-a.e. `mu` (`thompson-action-on-odd-measures-is-essentially-free`).

**Theorem 2.1.** For `x in B` the following are equivalent.
1. `x` is a left zero divisor in `B`.
2. `x_mu` is not injective for some `mu in M_-`.
3. `x_mu` is not injective for some `mu` in a given dense subset of `M_-`, for instance the sums of an
   odd number of Dirac measures.

*Proof.*
- *1 ⇒ 2.* Let `xy = 0` with `y = sum_k [k] d_k != 0`, and pick `mu` with some `d_k(mu) != 0`. Then
  `xi = rho_mu(y) delta_1 = sum_k d_k(mu) delta_k` is nonzero, and `x_mu xi = rho_mu(xy) delta_1 = 0`.
- *2 ⇒ 1.* Let `x_mu xi = 0` with `xi = sum_k xi_k delta_k != 0`, and let `F` be the support of `x`.
  - The finitely many functions `eta -> b_g(k eta)`, for `g in F` and `k in supp xi`, are locally
    constant. So some clopen `W ∋ mu` has `b_g(k eta) = b_g(k mu)` for all of them and all `eta in W`.
  - Put `y = sum_k xi_k [k] 1_W`, which is nonzero.
  - By `[g] f [k] f' = [gk] (k^-1 . f) f'` and `(k^-1 . b_g)(eta) = b_g(k eta)`,

    ```text
    x y = sum_m [m] 1_W ( sum_(gk = m) xi_k b_g(k mu) ) = sum_m [m] 1_W (x_mu xi)_m = 0.
    ```
- *2 ⇔ 3.* For fixed `xi`, `{mu : x_mu xi = 0}` is clopen, because it is cut out by finitely many
  locally constant functions. So the non-injectivity set is open, and it is nonempty iff it meets a dense
  set. Odd Dirac sums are dense: a basic clopen of `M_-` prescribes an odd vector on a finite partition,
  and choosing one point in each atom where the vector is `1` realizes it. QED

**Corollary 2.2.** `x` is a right zero divisor in `B` iff `(x*)_mu` is not injective for some `mu`.

**Lemma 2.3 (what a witness entry cannot be).** Let `sigma_1, sigma_2, tau_1, tau_2 in S_-` with
`tau_i sigma_j = delta_ij eps_-`, or `b', c' in S_-` with `c' q_[0] b' = eps_-`.
1. No `sigma_j` and no `q_[0] b'` is a left zero divisor in `S_-`. No `tau_i` and no `c' q_[0]` is a right
   zero divisor.
2. If `x` is a left zero divisor and `u, v` are units of `S_-`, then `u x v` is a left zero divisor. So
   no `sigma_j` has the form `u x v` with `x` a left zero divisor, and dually for the `tau_i`.
3. Every `sigma_j` or `q_[0] b'` lying in `B` has injective fibre operators at every `mu`. Every `tau_i`
   or `c' q_[0]` lying in `B` has an adjoint with injective fibre operators at every `mu`.

*Proof.*
- *1.* `tau_j sigma_j = eps_-` and `c' (q_[0] b') = eps_-` are left inverses, and a left invertible element
  is not a left zero divisor (Section 0). Dually for `tau_i` and `c' q_[0]`.
- *2.* `x y = 0` gives `(u x v)(v^-1 y) = 0`.
- *3.* A zero divisor in `B` is one in `S_-`. Apply Theorem 2.1 and Corollary 2.2. QED

## 3. Monomial and cancellation-free elements

For `x = sum_(g in F) [g] b_g in B` put

```text
c_x(mu) = #{ g : b_g(mu) != 0 }            (column weight)
n_x(nu) = #{ g : b_g(g^-1 nu) != 0 }       (image multiplicity)
```

- *What they count.* In the orbit module `x delta_mu = sum_g b_g(mu) delta_(g mu)`. So `c_x(mu)` counts
  the terms of the column at `mu`, and `n_x(nu)` counts the terms landing on `nu`.
- *Equal integrals.* Both are locally constant. By `V`-invariance of `lambda`,
  `∫ c_x = sum_g lambda(supp b_g) = sum_g lambda(g supp b_g) = ∫ n_x`.
- *Adjoints.* `x* = sum_g b_g [g^-1] = sum_g [g^-1] (g . b_g)`, with `(g . b_g)(mu) = b_g(g^-1 mu)`. So
  `c_(x*) = n_x` and `n_(x*) = c_x`.
- *Full support.* `lambda` charges every nonempty clopen
  (`odd-measure-space-has-no-honest-thompson-compression`). So a locally constant function that is
  `>= 0` with integral `0` vanishes everywhere.

**Examples.**
- *`c_x <= 1` everywhere* means the coefficient functions of distinct group elements have disjoint
  supports.
  - Two-piece honest lifts `[g_0] P_C + [g_1] P_(X \ C)` qualify, because `U_C ⊔ U_(X \ C) = M_-`.
  - So do lifts through the orthogonal character idempotents `1_([v])` of a finite partition.
- *`n_x <= 1` everywhere* means the translated supports `g supp b_g` are disjoint. The natural lift
  `tau = [g_0^-1] P_00 + [g_1^-1] P_01` qualifies, with images `U_0` and `U_1`, although `c_tau = 2` on
  `U_00 ∩ U_01`.
- *Not covered:* honest partial isometries `sum_i [g_i] P_(C_i)` over partitions with three or more
  atoms. A measure can charge three atoms, so `c_x` takes the value `3`.

**Theorem 3.1.** Let `x in B` with `c_x <= 1` everywhere or `n_x <= 1` everywhere. Then `x` is a unit
of `B`, or `x` is both a left and a right zero divisor in `B`.

*Proof.* **Claim.** Under either hypothesis, `x` is a unit or a left zero divisor.
- *(a) A zero column.* If `c_x(mu) = 0` for some `mu`, the clopen `W = {c_x = 0}` is nonempty and
  `x 1_W = sum_g [g] b_g 1_W = 0`.
- *(b) Cancellation-free.* Suppose `c_x >= 1` everywhere and `n_x <= 1` everywhere. Then
  `1 <= ∫ c_x = ∫ n_x <= 1`, so `c_x = n_x = 1` everywhere. This is case (d).
- *(c) A collision.*
  - *Setup.* Suppose `c_x = 1` everywhere and `n_x(nu) >= 2`. Take `g != g'` with
    `mu = g^-1 nu in supp b_g` and `mu' = g'^-1 nu in supp b_(g')`. Then `mu != mu'`, since `c_x(mu) = 1`.
  - *The translate.* Put `k = g'^-1 g`, so `k != 1` and `k mu = mu'`. Choose a clopen `W ∋ mu` with
    `W ⊆ supp b_g` and `kW ⊆ supp b_(g')`, on which `b_g = epsilon` on `W` and `b_(g') = epsilon'` on `kW`,
    with `epsilon, epsilon' in {1, -1}`.
  - *The annihilator.* Since `c_x = 1`, only `g` contributes on `W` and only `g'` on `kW`:

    ```text
    x 1_W = epsilon [g] 1_W,
    x [k] 1_W = sum_(g'') [g'' k] (k^-1 . b_(g'')) 1_W = epsilon' [g' k] 1_W = epsilon' [g] 1_W.
    ```

    So `y = epsilon' 1_W - epsilon [k] 1_W` is nonzero and `x y = 0`.
- *(d) A signed permutation.*
  - *Partitions.* If `c_x = n_x = 1` everywhere, the sets `A_g = supp b_g` partition `M_-`, the sets
    `g A_g` partition `M_-`, and `b_g^2 = 1_(A_g)`.
  - *`x* x`.* It equals `sum_(g,g') [g^-1 g'] ((g'^-1 g) . b_g) b_(g')`. A term is nonzero at `mu` only if
    `g' mu in g' A_(g') ∩ g A_g`, which forces `g = g'`. So `x* x = sum_g 1_(A_g) = eps_-`.
  - *`x x*`.* It equals `sum_g [g] 1_(A_g) [g^-1] = sum_g 1_(g A_g) = eps_-`. So `x` is a unit.
- *Case split.*
  - Under `c_x <= 1`: either (a), or `c_x = 1` everywhere. In the second case either `n_x <= 1`, where
    `∫ n_x = ∫ c_x = 1` forces `n_x = 1` and hence (d), or (c).
  - Under `n_x <= 1`: either (a) or (b).

**Right side.** The hypothesis is symmetric under `*`, because `c_(x*) = n_x` and `n_(x*) = c_x`. The
Claim for `x*` says `x*` is a unit or a left zero divisor, so `x` is a unit or a right zero divisor. If
`x` is not a unit, both conclusions hold. QED

**Corollary 3.2 (Cohn entries).** In a Cohn family `tau_i sigma_j = delta_ij eps_-` in `S_-`, no entry lying
in `B` has `c <= 1` everywhere or `n <= 1` everywhere. No entry has the form `u x v` with `x in B` such a
non-unit and `u, v` units of `S_-`.

*Proof.* A unit `sigma_1` would force `tau_2 = tau_2 sigma_1 sigma_1^-1 = 0`, contradicting
`tau_2 sigma_2 = eps_-`, and the other entries are symmetric. A non-unit is a two-sided zero divisor, which
Lemma 2.3 excludes, also after multiplication by units. QED

**Corollary 3.3 (corner witnesses).** Suppose `c' q_[0] b' = eps_-` with `b' in B` and `c'` anywhere in
`S_-`. Then `x = q_[0] b'` has `c_x >= 2` on a nonempty clopen and `n_x >= 2` on a nonempty clopen. The same
holds for `c' q_[0]` when `c' in B` and `b'` is arbitrary.

*Proof.* `x` is left invertible, so it is not a left zero divisor. It is not a unit, since `q_[0] x = x`
would give `q_[0] = eps_-`. Apply Theorem 3.1. QED

**Reading.**
- *Extends the star-design weight theorem.* `star-compression-designs-need-weight-four-colliding-columns`
  excludes cancellation-free star designs (`c' = b'*`). Corollary 3.3 excludes cancellation-free and
  column-monomial witnesses for every partner `c'`, including partners outside `B`, which the square
  counting of that theorem cannot see.
- *Extends honest compression.* `odd-measure-space-has-no-honest-thompson-compression` excludes honest
  partial isometries with `x* x = eps_-`. Theorem 3.1 turns every covered non-unit into a two-sided zero
  divisor, with an explicit annihilator.
- *Units do not help multiplicatively.* Multiplying a covered lift by the Hadamard unit, by
  `1 + s_alpha t_beta`, or by any element of `G` leaves it dead. Units outside `E x| V` can enter only
  through sums.
- *What survives.* An entry in `B` needs genuine collisions with mod-3 cancellation, both among its columns
  and among its images, and injective fibre operators at every `mu`.
