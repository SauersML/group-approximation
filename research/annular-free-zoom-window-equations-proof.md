---
rg: 2
id: annular-free-zoom-window-equations-proof
kind: route
title: Split points into shallow ones and deep cylinders, read deep actions as germ words evaluated at a depth, and perturb one deep annulus by conjugation
target: annular-hosts-with-free-zoom-germs-are-not-finitely-presented
requires:
  - annular-free-product-germ-hosts-are-not-finitely-presented
---

Conventions: `τ^(-δ) ĝ τ^δ` acts on `A_n`, for `n` large, by `ρ_(n+δ)(g)`. For a word
`u = ∏_i t^(-δ_i) h_i t^(δ_i)` with `h_i ∈ {ĝ_j^(±1)}`, put
`ev_n(u; ρ) = ∏_i ρ_(n+δ_i)(h_i) ∈ V`.

**Item 1 (window lemma).**
1. *Constants.*
   - `c` bounds the prefix lengths in the tables of `S_V^(±1)`.
   - `ℓ_m` bounds those of `ρ_m(g_j)^(±1)`.
   - `M_0 = 0` and `M_(j+1) = M_j + max(c, ℓ_0, ..., ℓ_(M_j))`.
   - `B = M_R + max_(m <= M_R) ℓ_m + c`.
2. *Shallow and deep points.* Call `x` *deep* if it has a zero-run of length at least
   `B + 2` starting in its first `B + 1` places, and write `x = P 0^k 1 z`, with that
   run maximal, `|P| <= B` and `k >= B + 2`. Otherwise `x` is *shallow*.
3. *Invariant form.* Let `w` have length at most `R`, and let `x` be deep. Every point of
   the trajectory then has the form `P_j 0^(k_j) 1 z_j`, with `|P_j| <= B` and
   `k_j >= k - B`. The reasons, one letter at a time:
   - A `V`-letter rewrites at most `c` leading symbols.
   - A `Ĝ`-letter at a depth `m < |P_j|` rewrites at most `ℓ_m` symbols inside
     `P_j 0^(k_j)`.
   - A `Ĝ`-letter at a point `0^m 1 z_j`, with `P_j` all zeros, keeps `0^m 1` and applies
     `ρ_m(g)` to `z_j`. This is a *tail step*, at depth `m = k + δ` with `|δ| <= B`.
4. *Translation invariance.* The evolution of `(P_j, k_j - k)` and the tail offsets `δ` do
   not depend on `z`, on `k >= B + 2`, or on any `ρ_m` with `m > M_R`. So on the cylinder
   `P 0^k 1 C`, `w` acts by `P 0^k 1 z ↦ P' 0^(k + e) 1 ev_k(u_(w,P); ρ)(z)`. Here
   `(P', e)` and the window word `u_(w,P)`, the product of the tail steps, depend only on
   `w` and `P`.
5. *Shallow points.* If some `Ĝ`-letter of a shallow point's trajectory were applied at
   depth `m >= 2B + 2`, running step 3 backwards from that moment would make `x` deep.
   So shallow points only see `ρ_m` with `m <= 2B + 1`.
6. *Conclusion.*
   - Let `r` be a relation of `Γ_ρ` of length at most `R`. Then `P' = P`, `e = 0`, and
     `ev_k(u_(r,P); ρ) = 1` for all `k >= B + 2`, and `r` acts trivially on shallow points.
   - For `ρ'` agreeing with `ρ` up to depth `2B + 1`, the shallow action and `(P', e)` are
     unchanged. So `r` holds for `ρ'` exactly when `ev_k(u_(r,P); ρ') = 1` for all
     `k >= B + 2` and all `P`.
   - Each `u_(r,P)`, realized as `∏ τ^(-δ_i) ĥ_i τ^(δ_i)`, acts trivially on all deep
     annuli, so it is trivial in `(Γ_ρ)_p`.

**Item 2.** Suppose `Γ_ρ` is finitely presented, with relators of length at most `R_0`,
and apply item 1 with `R = R_0`.
1. *Presentation of the germs.* Let `U` be the set of words `v` in the `ĝ_j` with
   `(v)_p = 1`, that is, `ρ_m(v) = 1` for all large `m`. Since `(Γ_ρ)_p = (Ĝ)_p * <t>`, the
   kernel of `F(ĝ, t) -> (Γ_ρ)_p` is the normal closure of `{t^(-δ) v t^δ : v ∈ U, δ ∈ Z}`.
2. *Window words are single-depth consequences.* Let `K` be the kernel of the
   `t`-exponent, the free product of the shifted copies of `F(ĝ)`. Each window word from
   item 1 with `R = R_0` lies in `K` and in that normal closure. So it is a product of
   `K`-conjugates of finitely many `t^(-δ) v t^δ` with `v ∈ U`. Fix these expressions for
   all the finitely many window words. Let `Δ` bound the offsets in them, and `N_0` bound
   the depths beyond which the `v` used satisfy `ρ_m(v) = 1`.
3. *Perturbation.* Take `L >= max(2B + 2, N_0 + Δ + B + 1)` with `ρ_L(g_i) != 1` for some
   `i`, and `κ ∈ V` not commuting with `ρ_L(g_i)`, which exists because `V` has trivial
   centre. Put `ρ'_L = κ ρ_L κ^(-1)` and `ρ'_m = ρ_m` for `m != L`.
   Then `ρ'_m(v) = 1` whenever `ρ_m(v) = 1`.
4. *All short relations survive.*
   - For `k` whose window `[k - B, k + B]` misses `L`, `ev_k(u; ρ') = ev_k(u; ρ) = 1`.
   - Otherwise `k >= L - B >= N_0 + Δ + 1`. `ev_k(·; ρ')` is a homomorphism on the finitely
     generated part of `K` involved, and it kills each `t^(-δ) v t^δ` used, since
     `k + δ >= N_0`. So `ev_k(u; ρ') = 1`.
   - By item 1, every relation of length at most `R_0` holds for `ρ'`.
5. *Contradiction.* The relators then hold for `ĝ'_i`, and the local rigidity lemma (item 1 of
   `annular-free-product-germ-hosts-are-not-finitely-presented`) would give
   `ĝ'_i = ĝ_i`. But `ρ'_L(g_i) != ρ_L(g_i)`.
