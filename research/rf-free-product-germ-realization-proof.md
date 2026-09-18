---
rg: 2
id: rf-free-product-germ-realization-proof
kind: route
title: Put the finite quotients of G in ping-pong position inside V and read the germs on deep annuli
target: rf-groups-have-free-product-germs-over-v
---

Notation as on the claim.

1. **Ping-pong position.** Put `X_j = 1^j 0 C` for `j >= 0`, which are disjoint nonempty
   clopen sets, and `D_j = C ∖ X_j`, so `X_i ⊆ D_j` for `i != j`, and `x_0 = 1^∞` lies in
   every `D_j`. Let `Q_j = G/N_j`. Split `X_j` into `|Q_j| - 1` nonempty clopen sets
   `E_(j,q)`, `q ∈ Q_j ∖ {1}`, and put `E_(j,1) = D_j`. Fix homeomorphisms
   `h_(j,q): C -> E_(j,q)` that are locally prefix replacements. Any two nonempty clopen
   subsets of `C` are joined by such a map. Let `q ∈ Q_j` act by
   `h_(j,q')(w) ↦ h_(j,qq')(w)`. This is an action by elements of `V`, and
   `q(D_j) = E_(j,q) ⊆ X_j` for `q != 1`. Let `ρ_j: G -> Q_j -> V`.
2. **Freeness.** Let `u = q_1 ... q_r`, `r >= 1`, with `q_i ∈ Q_(j_i) ∖ {1}` and
   `j_i != j_(i+1)`. Then `q_r(x_0) ∈ X_(j_r)`, and `q_i(X_(j_(i+1))) ⊆ q_i(D_(j_i)) ⊆ X_(j_i)`.
   By induction `u(x_0) ∈ X_(j_1)`, which does not contain `x_0`, so `u != 1`. Hence
   `<Q_j : j >= 0> = *_j Q_j` in `V`.
3. **Item 1.** `ĝ` preserves every `A_n` and every `0^n C`, so it is continuous at `p`. On
   `A_n` it is `α_n ρ_n(g) α_n^(-1)`, an element of `V` restricted to a cone. `g ↦ ĝ` is a
   homomorphism, and it is injective because `g != 1` lies outside `N_n` for all large `n`.
4. **Item 2.** Conditions 1--3 of a finite germ extension hold for the full closure exactly
   as in `prefix-replacement-actions-recode-into-germ-extensions-of-v` (fullness of `V`,
   and localization by patching with a `V`-map off a clopen neighbourhood). A germ of the
   groupoid fails to be a `V`-germ only along trajectories through `p`, so
   `sing(Γ) ⊆ V·p`. Equality holds by item 3.
5. **Generation of `(Γ)_p`.** Follow `p` along a word in the generating germs. `Ĝ`-letters
   at points other than `p` contribute `V`-germs, and `V`-germs from `p` to `p` lie in
   `(V)_p = <t>`: a `V`-element fixing `0^∞` is `0^k w ↦ 0^(k') w` near `p`. So
   `(Γ)_p = <(Ĝ)_p, t>`.
6. **Freeness of germs.** `τ α_n = α_(n+1)` for `n >= 1`, so `τ^k ĝ τ^(-k)` acts on `A_n`,
   `n >= k+1`, by `ρ_(n-k)(g)`. Take `w = (∏_i s^(k_i) g_i s^(-k_i)) s^m` in `G * <s>`,
   reduced: `g_i != 1` and `k_i != k_(i+1)`.
   - Its image `w'` in `<Ĝ, τ>` maps `A_n` onto `A_(n+m)` for large `n`. A homeomorphism
     with trivial germ at `p` is the identity near `p`, so trivial germ forces `m = 0`.
   - If `m = 0` and the product is nonempty, then for large `n`, `w'` acts on `A_n` by
     `∏_i ρ_(n-k_i)(g_i)`. Every factor is nontrivial, because `g_i ∉ N_(n-k_i)`.
     Consecutive indices `n - k_i` differ, so this is a reduced word in `*_j Q_j`, which is
     nontrivial by step 2.

   So `G * <s> -> (Γ)_p`, `s ↦ t`, is injective, and onto by step 5. It factors through
   `<Ĝ, τ>`, so that group is also `G * Z`.
7. **Item 4.** A free product of two finitely presented groups is finitely presented.
