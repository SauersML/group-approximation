---
rg: 2
id: fpbs-kazhdan-twisted-certificates-vanishing-weight
kind: claim
title: Abelian-crown certificates of rank gradient in a Kazhdan group need modules of vanishing Plancherel weight
distinct_from:
  fpbs-kazhdan-cofinal-mod-p-growth-vanishes: that bounds d_p(N) for the trivial module; this transfers every nontrivial irreducible module M of Gamma_n to d_p of the kernel K_M, losing exactly the Plancherel weight w(M), and so kills twisted certificates whose weight stays bounded below.
  fpbs-kazhdan-positive-rank-gradient: that asks for linear d(Gamma_n); this shows the abelian non-central crowns can supply it only through modules with w(M_n) -> 0 (at rate C/log p), which leaves low-weight modules (reachable only through a twisted independence lemma), non-abelian crowns and the d versus profinite-rank gap.
artifacts:
  - experiments/twisted-lackenby-lift-2026-09-17/twisted_lift.py
  - experiments/twisted-lackenby-lift-2026-09-17/cases1.py
  - experiments/twisted-lackenby-lift-2026-09-17/cases2.py
  - experiments/twisted-lackenby-lift-2026-09-17/results.txt
---

**ESTABLISHED (written deduction; short, uses Gaschutz and the Hadamard bound of
`fpbs-kazhdan-cofinal-mod-p-growth-vanishes`).**

## Setting

- `Gamma` is a Kazhdan group. `pi: G -> Gamma` is a finitely presented Kazhdan
  cover `<X|R>`, and `L = max(2, max relator length)`.
- `Gamma_n` is a finite index subgroup, `N = [Gamma:Gamma_n]`.
- `M` is a nontrivial irreducible `F_p[Gamma_n]`-module. Put `k = End(M)`, a
  field of degree `e` over `F_p`. Let `K = K_M` be the kernel of the action and
  `Q = Gamma_n/K`.
- The **abelian crown count** is `mu(Gamma_n;M) = m/dim_k M`, where `m` is the
  multiplicity of `M` in the head of `X_K = K^ab (x) F_p` as `F_p[Q]`-module.
  Crown theory (Dalla Volta–Lucchini) makes `mu` the contribution of the crown
  of `M` to `d(Gamma_n)`. Directly, `d(Gamma_n) >= 1 + mu` (step 1 below).
  Up to `O(dim M)`, `h^1(Gamma_n;M) = e*m`, by inflation-restriction and
  `h^1(Q;M) < dim M` (Aschbacher–Guralnick). So an abelian-crown certificate
  of positive rank gradient is a sequence with `mu(Gamma_n;M_n) >= c N_n`.
- The **Plancherel weight** is `w(M) = (dim_{F_p} M)^2 / (e|Q|)`. It lies in
  `(0,1]`, because `F_p[Q]` maps onto `End_k(M)`, of `F_p`-dimension
  `(dim M)^2/e` (Wedderburn).
  - It can stay bounded below: an extraspecial 2-group of order `2^(2n+1)`
    acting faithfully on `F_3^(2^n)` has `w = 1/2`.
  - It tends to zero for the natural modules of `GL_n(F_q)`.

## Statements

**Theorem 1 (weight transfer).**
`mu(Gamma_n;M) / N <= (d_p(K_M)/[Gamma:K_M]) / w(M)`.

**Corollary 2 (large primes).** For every finite index `Gamma_n` and every
nontrivial irreducible `F_p[Gamma_n]`-module `M`,

`mu(Gamma_n;M) / [Gamma:Gamma_n] <= |R| log L / (w(M) log p)`.

So a certificate `mu >= cN` at prime `p` forces `w(M) <= |R| log L/(c log p)`.

**Corollary 3 (bounded weight dies at every prime on Frattini-closed kernel
families).** Suppose:
- `(Gamma_n, M_n)` is a family with `mu(Gamma_n;M_n) >= cN_n` and
  `w(M_n) >= w_0 > 0`;
- the kernels `K_n = K_(M_n)` are normal in `Gamma` and form a `p`-Frattini
  closed family (each `K_n` contains some `K_n'` inside `[K_n,K_n]K_n^p`).

Then `Gamma` is not Kazhdan. Normality of `K_n` holds, for instance, when
`Gamma_n` is normal and `M_n` is the restriction of a `Gamma`-module.

**Consequence for the target.** An abelian non-central crown certificate for
`fpbs-kazhdan-positive-rank-gradient` must use modules with
`w(M_n) <= C_Gamma/(c log p_n)`, and at bounded primes with `w` bounded below
its kernel family must fail `p`-Frattini closure. Every central-type crown
(quotients with a faithful irreducible of dimension comparable to `|Q|^(1/2)`)
is dead at every prime. The live abelian crowns are the low-weight ones, such
as natural modules of large linear groups.

## Proof

1. **`d(Gamma_n) >= 1 + mu`.** Take a generating set of size `d` and
   `F_d -> Gamma_n -> Q` with kernel `R_F`.
   - `R_F` maps onto `K`, so `X_K` is a quotient of `R_F^ab (x) F_p`.
   - By Gaschutz, `R_F^ab (x) F_p = F_p (+) F_p[Q]^(d-1)`.
   - The head multiplicity of a nontrivial `M` there is `(d-1) dim_k M`, so
     `m <= (d-1) dim_k M`.
2. **`dim X_K >= m dim M`.** `Hom_Q(X_K, M)` is a `k`-space of dimension `m`.
   - Take a `k`-basis `f_1..f_m` and `F = (f_i): X_K -> M^m`.
   - `M` is absolutely irreducible over `k`, so every submodule of
     `M^m = M (x)_k k^m` has the form `M (x)_k V`.
   - If the image of `F` is proper, some nonzero `lambda` in `(k^m)^*` kills
     `V`, and then `sum lambda_i f_i = 0`. This contradicts independence, so `F`
     is onto.
   - Hence `d_p(K) = dim X_K >= m dim M = mu (dim M)^2/e = mu w(M) |Q|`.
3. **Theorem 1.** Divide by `[Gamma:K] = N|Q|`:
   `d_p(K)/[Gamma:K] >= w(M) mu/N`.
4. **Corollary 2.** Apply the Hadamard torsion bound of Corollary B' in
   `research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md`.
   - The bound is proved for normal `N`, but its steps 1–2 use only that
     `pi^(-1)(K)` has finite index and `b_1 = 0`.
   - So `d_p(K) <= |R|[Gamma:K] log L/log p` for every finite index `K`, and
     step 3 gives the claim.
5. **Corollary 3.** By step 3, `d_p(K_n) >= c w_0 [Gamma:K_n]` for all members.
   Theorem B (general form) of the same document forbids this for a
   `p`-Frattini closed normal family in a Kazhdan group.

## Calibration

- **Free group `F_2`** (not Kazhdan). `Q = SL_2(p)` acting on `F_p^2`, along any
  chain: `mu = (d(Gamma_n)-1)` is linear, `w = 4/(p(p^2-1))`, and
  `d_p(K)/[Gamma:K] ~ 1`. Theorem 1 gives `mu/N <= p^3/4`, which is consistent.
  Only the Kazhdan inputs (Hadamard with `b_1 = 0`, Theorem B) turn it into an
  obstruction.
- **`SL_3(Z)` congruence kernels.** `X_K = sl_3(F_p)` has bounded dimension, so
  `mu` is bounded, as Theorem 1 predicts.

## Twisted Lackenby lifting: weight-free count, independence open

The scalar iteration on `K_M` loses the weight twice.
- Its Frattini deck group has relative rank only `c w`.
- The base complex `K_(K_M)` has `|R|N|Q|` 2-cells.
- So Lackenby's Theorem 5.1 needs `u >~ 2|R|/(c w)`, and no uniform `u` exists
  when `w(M_n) -> 0`.

The twisted analogue of Theorem 5.1 works over the smaller complex
`K_(Gamma_n)`, which has `r = |R|N` 2-cells.
- **Construction.** Take `u` scalar classes `U` and `h ~ cN dim M` derivations
  into `M`. Pass to the cover `ker(Gamma_n -> M^h x| Q)`, which is a quotient
  of the Frattini cover of `K_M`. Use the `M`-valued cochains
  `Y_ij(e) = c_i(e) xi_j(i(e))`.
- **Twisted Lemma 5.7.** Deck translates of a 2-cell give `Q`-translates of one
  `M`-valued evaluation. So the cocycle subspace has codimension at most
  `r dim M`, and the lifted cocycle subspace has dimension at least
  `uh - r dim M >= N dim M (cu - |R|)`.
  This is **weight-free**: `u = 2|R|/c` suffices.

Numerical check (`experiments/twisted-lackenby-lift-2026-09-17/`).
- **Codimension.** The cocycle subspace has dimension `z >= uh - r dim M` in
  every case: free groups, and the genus-2 surface with `S_3` on `F_2^2` and
  `h = 1, 2, 3`.
- **Independence** (the twisted Lemma 5.6) is where the route can fail.
  - In `F_2`, the class inflated from `Q` (the sign character) lifts to zero
    classes (`cls = 0`), while a non-inflated class gives `cls = 4`.
  - On the genus-2 surface the inflated class survives (`cls = 2`).

**Reduction (both directions not claimed).** Take a twisted independence
lemma: the lifted cocycles span at least
`(uh - r dim M - O(t h))/dim M` classes, where `t = u - rank(U restricted to K_M)`
counts the classes of `U` inflated from `Q`. Suppose it holds, and the descent step (Theorem B, Step 2.4) can be
chosen so the pulled-back `U` is not inflated from the next `Q`. Then Corollary
3 extends to **all** weights on `p`-Frattini closed kernel families.

The obstruction is structural. Descending to a deep member tends to put `K_M`
inside `ker U`, and then every class of `U` is inflated.

## What survives, sharply

1. **Low-weight abelian crowns.** `mu(Gamma_n;M_n) >= cN_n` with
   `w(M_n) -> 0`. Equivalently, `d_p(K_(M_n))` grows linearly in `N_n` times
   `(dim M_n)^2/e` while staying `o([Gamma:K_(M_n)])`: a linear isotypic
   multiplicity of a small-Plancherel-weight irreducible in the mod-`p` relation
   module of a deep kernel. The scalar support iteration on `K_M` cannot reach
   this, since the gradient of `K_M` is `o(1)`. The weight-free twisted lift
   above could, if the twisted independence lemma holds.
2. **Non-abelian crowns** `S^k` with `log k >= cN log|S|`.
3. **The gap** `d(Gamma_n) > d(Gamma_n-hat)`.
