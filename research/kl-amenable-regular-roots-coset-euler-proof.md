---
rg: 2
id: kl-amenable-regular-roots-coset-euler-proof
kind: route
title: Push the Fox fundamental formula to the coset module Z[Gamma/F], count dimensions on the coset graph, and pass to von Neumann dimension and dimension-flatness for infinite and amenable roots
target: kl-amenable-regular-roots-lie-in-the-coefficient-group
requires:
  - kl-regular-roots-lift-through-locally-indicable-kernels
artifacts:
  - experiments/kl-regular-roots-2026-09-17/cosetbound.py
  - experiments/kl-regular-roots-2026-09-17/cosetbound.out
  - experiments/kl-regular-roots-2026-09-17/driver6.py
  - experiments/kl-regular-roots-2026-09-17/driver6.out
---

Notation of the target. Write `w- = s_1 ... s_k` with `s_j in F ∪ {t, t^(-1)}`,
`pi_j` the image of `s_1 ... s_j` under `t -> tau`, `pi_0 = 1`, `pi_k = 1`.
Then `D = sum_(s_j = t) pi_(j-1) - sum_(s_j = t^(-1)) pi_(j-1) tau^(-1)`.

Imports, all from W. Lück, *L2-Invariants: Theory and Applications to Geometry
and K-Theory*, Springer 2002 (cited from memory, not pinned):
- [L6.7] `dim_(N(Gamma))` is defined on all `N(Gamma)`-modules and is additive
  on short exact sequences.
- [L6.54(8)] `dim_(N(Gamma)) N(Gamma) ⊗_(C Gamma) C = 1/|Gamma|`, read as `0`
  when `Gamma` is infinite.
- [L6.37] If `Gamma` is amenable, `dim_(N(Gamma)) Tor_p^(C Gamma)(N(Gamma), M) = 0`
  for every `C Gamma`-module `M` and every `p >= 1`.

Also standard: `dim_(N(Gamma)) N(Gamma) = 1`, and `dim N(Gamma) e = tr(e)` for
a projection `e`.

## 0. Reduction to `Gamma = <F, tau>`

Let `Gamma_0 = <F, tau> <= Gamma`, so `D in Z[Gamma_0]`, and choose left coset
representatives `x_i` with `Gamma = ⊔ x_i Gamma_0`. Any `mu in R[Gamma]`
is uniquely `sum x_i mu_i` with `mu_i in R[Gamma_0]`, and
`mu D = sum x_i (mu_i D)` with `mu_i D in R[Gamma_0]`. So `mu D = 0` iff every
`mu_i D = 0`. Regularity in `Gamma` is regularity in `Gamma_0`. From now on
`Gamma = <F, tau>`.

## 1. The coset complex (item 1)

**Fox fundamental formula at a root.** Telescoping,
`0 = w-(tau) - 1 = sum_j (pi_j - pi_(j-1))`. The `j`-th summand is
`pi_(j-1)(g_j - 1)` if `s_j = g_j in F`, `pi_(j-1)(tau - 1)` if `s_j = t`, and
`pi_(j-1)(tau^(-1) - 1) = -pi_(j-1) tau^(-1) (tau - 1)` if `s_j = t^(-1)`. Hence

    D (tau - 1)  =  - sum_(s_j = g_j in F) pi_(j-1) (g_j - 1)      in Z[Gamma].   (*)

**The complex.** Let `C_0 = Z[Gamma/F]`, the permutation module on left cosets,
and `d_1 : Z[Gamma] -> C_0`, `x -> x (tau - 1) · F`, so
`d_1(gamma) = gamma tau F - gamma F`. It is a left module map. For `g in F`,
`(g - 1)·F = gF - F = 0`, so by `(*)`, `d_1(mu D) = mu D (tau - 1) F = 0`.
Thus `r_D : mu -> mu D` has image in `ker d_1`.

**Image of `d_1`.** The image lies in the augmentation ideal `I` of `C_0`, and
it contains `gamma tau F - gamma F` for every `gamma`. Build the graph on
`Gamma/F` with an edge from `gamma F` to `gamma tau F` for every `gamma`. Since
`Gamma = <F, tau>`, every `gamma` is a product `y u` with `y` shorter in the
letters `F ∪ {tau, tau^(-1)}` and `u` a letter. By induction `yF` is joined to
`F`. If `u in F`, then `uF = F`, so `gamma F = yF`. If `u = tau`, the edge at
`y` joins `yF` to `gamma F`. If `u = tau^(-1)`, the edge at `gamma` joins
`gamma F` to `gamma tau F = yF`. So the graph is connected. For a connected graph
the edge differences span `I`. Hence `im d_1 = I`, of `Z`-rank `[Gamma:F] - 1`
when the index is finite, and `coker d_1 = C_0 / I = Z`, the trivial module.
The same holds after `⊗ k` for a field `k`.

## 2. Finite roots (item 2)

Let `Gamma` be finite, `k` a field. Then `dim_k k[Gamma] = |Gamma|`,
`dim_k (k ⊗ C_0) = [Gamma:F]`, `dim_k im(d_1) = [Gamma:F] - 1`, and
`dim_k ker(d_1) = |Gamma| - [Gamma:F] + 1`. Since `im r_D ⊆ ker d_1`,
`rank r_D <= |Gamma| - [Gamma:F] + 1`, which is `< |Gamma|` when `Gamma != F`.
So `r_D` has a nonzero kernel: some `mu != 0` in `k[Gamma]` has `mu D = 0`.
For `k = Q`, clearing denominators gives `mu in Z[Gamma]`. For `k = F_p` this
is non-regularity over `F_p` directly.

## 3. Infinite roots (item 3)

Let `Gamma` be infinite, `N = N(Gamma)`, and apply `N ⊗_(Z Gamma) -`. We get
`N --(r_D)--> N --(N ⊗ d_1)--> N ⊗_(Z Gamma) C_0`, which is still a complex.

- `N ⊗_(Z Gamma) Z[Gamma/F] = N ⊗_(Z F) Z ≅ N e`, with
  `e = |F|^(-1) sum_(f in F) f`, a projection of trace `1/|F|`. So
  `dim N ⊗ C_0 = 1/|F|`.
- Tensor is right exact, so `coker(N ⊗ d_1) = N ⊗_(Z Gamma) coker d_1 =
  N ⊗_(Z Gamma) Z = N ⊗_(C Gamma) C`, of dimension `0` by [L6.54(8)].
- By [L6.7], `dim im(N ⊗ d_1) = 1/|F|` and `dim ker(N ⊗ d_1) = 1 - 1/|F|`.
- `im r_D ⊆ ker(N ⊗ d_1)`, so `dim im r_D <= 1 - 1/|F|`, and by [L6.7]
  `dim ker r_D = 1 - dim im r_D >= 1/|F|`.

## 4. Amenable roots (item 4)

Let `Gamma` be infinite and amenable, and suppose `r_D` is injective on
`C Gamma`. Put `M = C Gamma / C Gamma D`. Then
`0 -> C Gamma --(r_D)--> C Gamma -> M -> 0` is a free resolution of `M`. So
`Tor_1^(C Gamma)(N, M) = ker(r_D : N -> N)`, of dimension `>= 1/|F|` by §3.
That contradicts [L6.37]. So some `mu != 0` in `C Gamma` has `mu D = 0`.

**Descent.** Let `S` be the support of `mu`. The condition `nu D = 0` on `nu`
supported in `S` is a finite homogeneous linear system with integer
coefficients. It has a nonzero complex solution, so its rank over `Q` is less
than `|S|` and it has a nonzero integer solution `nu`. Divide `nu` by the gcd
of its coefficients. Then `nu mod p != 0` and `(nu mod p) D = 0` for every `p`.

## 5. Consequence (item 5)

If `Gamma = <F, tau>` is amenable and the root is regular over `Z` (or over
`F_p`), then `Gamma = F` by §2 and §4. (Non-regularity over `Z` implies it over
every `F_p` by the gcd step.) So `tau = c in F`. On the finite-dimensional
algebra `Q[F]`, `r_D` injective means `r_D` bijective, so `mu D = 1` for some
`mu`, and a one-sided inverse in a finite-dimensional algebra is two-sided: `D`
is a unit. Conversely a unit has no left annihilator, and a `Z`-annihilator is
a `Q`-annihilator. Over `F_p` the argument is the same.

Any root `(Gamma, tau)` with `Gamma = <F, tau>` receives the surjection
`Gamma_F -> Gamma`, `c -> c`, `t -> tau`. So if `Gamma_F` is amenable, every
root group is amenable. If moreover `Gamma_F != F`, the universal root is not
in `F` and is not regular. By item 3 of the lifting claim, `X` is not
aspherical.

## 6. The blind word (item 6)

`F = <c | c^6>`, `w- = c^2 t^(-1) c^5 t c^5 t^(-1) c`, `deg = -1`.

**Roots in `F`.** `w-(c^a) = c^(13 - a)`, so the unique root in `F` is `c`.
Then `pi` before the letters `t^(-1), t, t^(-1)` equals `c^2`, `c^6 = 1`,
`c^6 = 1`, so `D = -c^2 c^(-1) + 1 - c^(-1) = 1 - c - c^5`. At the character
`c -> zeta = e^(i pi/3)`, `1 - zeta - zeta^(-1) = 1 - 2 cos(pi/3) = 0`. So `D`
is not a unit of `C[C_6]`, hence not of `Q[C_6]`. Over `F_p`, the ring map
`F_p[C_6] -> F_p[x]/(x^2 - x + 1)`, `c -> x`, is
well defined (`x^3 = -1`, so `x^6 = 1`). It sends `D` to `1 - x - x^(-1) = 0`,
because `x^(-1) = 1 - x`. The target is a nonzero ring, so `D` is a unit of no
`F_p[C_6]`.

**`Gamma_F` is amenable.** Put `c' = c^(-1) t^(-1) c^3`, so
`t^(-1) = c c' c^(-3)` and `t = c^3 c'^(-1) c^(-1)`. Substituting and using
`c^6 = 1`, the relator becomes
`c^3 · c' c^(-1) c'^(-1) c^(-1) c' c · c^(-3)`, so it is equivalent to
`c' c = c c' c c'^(-1)`, i.e. `c c' c = c' c c'`. Tietze gives
`Gamma_F = <c, c' | c c' c = c' c c', c^6> = B_3 / <<sigma_1^6>>`. The image of
the central `Delta^2 = (sigma_1 sigma_2)^3` generates a central cyclic
subgroup, and the quotient is
`PSL_2(Z)/<<sigma_1^6>> = <a, b | a^2, b^3, (b^(-1) a)^6>` with
`a = sigma_1 sigma_2 sigma_1`, `b = sigma_1 sigma_2`, `sigma_1 = b^(-1) a`. That
is the Euclidean `(2,3,6)` triangle group `Z[omega] ⋊ C_6`. So `Gamma_F` is
virtually nilpotent, hence amenable, and it is infinite, so `Gamma_F != F`.
By §5 no root of `w-` in any group is regular over `Z` or any `F_p`.

**Computation.** `driver6.py` realises `c` as an order-6 rotation about `0` and
`c'` as its conjugate by translation, an order-6 rotation about `1`, in `Z[omega] ⋊ C_6`. It asserts the braid
relation, sets `tau = c^3 c'^(-1) c^(-1)`, checks `w-(tau) = 1`, and finds
`det = 0` for the `6 x 6` Laurent matrix of right multiplication by `D` over
`Z[x^(±1), y^(±1)]`, which agrees with §4 on this quotient.
