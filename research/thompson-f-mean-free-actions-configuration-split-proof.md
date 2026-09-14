---
rg: 2
id: thompson-f-mean-free-actions-configuration-split-proof
kind: route
title: Canonical finite fixed sets of confined stabilizers push mean-free means to dense configurations, disjoint intervals kill bounded types, pushing inside an interval gives the profile, and grids over Følner sets give (I) under amenability
target: thompson-f-mean-free-actions-dense-configurations-or-unconfined
requires:
  - thompson-f-confined-subgroups-fix-finite-sets
  - thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived
  - mean-free-amenable-actions-residually-amenable-and-sofic
  - elek-szabo-essentially-free-amenable-actions
---

Notation as in the claim.
- `F[a,b]` is the group of elements of `F` supported in `[a,b]`. For dyadic `a < b` it is conjugate to
  `F` by the dyadic PL map `[0,1] → [a,b]`, so it contains the conjugate `x_0^[a,b]` of `x_0`. That
  conjugate has no fixed point in `(a,b)` and pushes every point toward `a`.
- Composition is right to left, and `[p,s] = p s p⁻¹ s⁻¹ ∈ F'`.

**Import (item 6 only).** Every nontrivial normal subgroup of `F` contains `F'`. It is pinned verbatim in
`thompson-f-is-lea-only-if-amenable-proof` (Burillo–Lodha–Reeves, arXiv:1509.04586, citing
Cannon–Floyd–Parry).

**0. Small commutators.** Let `J ⊆ (0,1)` be open, `x ∈ J`, and dyadic `a < b` with `x ∈ (a,b)` and
`[a,b] ⊂ J`.
- Pick dyadic `a' < b'` with `x ∈ (a',b')` and `[a',b'] ⊂ (a,b)`, and put `p = x_0^[a',b']`, so
  `p(x) ≠ x`.
- A power of `x_0^[a,b]` carries `[a',b']` to an interval `s[a',b'] ⊂ (a,b)` disjoint from `[a',b']`.
- Then `q = [p,s] = p · (s p⁻¹ s⁻¹)` lies in `F'`. It agrees with `p` on `[a',b']`, so `q(x) ≠ x`, and
  `supp(q) ⊆ [a',b'] ∪ s[a',b'] ⊂ J`.

**1. Item 1.** Let `ω ∈ Ω_conf` and `H = Stab(ω)`. By `thompson-f-confined-subgroups-fix-finite-sets`
there is a finite `S ⊂ [0,1]` with `St⁰_(F')(S) ≤ H ≤ St_F(S)`.
- **`S ∩ (0,1) ⊆ S(ω)`.** An order-preserving homeomorphism that preserves a finite set fixes it
  pointwise.
- **`S(ω) ⊆ S`.** Let `x ∈ (0,1) \ S`, and let `J` be the component of `(0,1) \ S` containing `x`.
  - Step 0 gives `q ∈ F'` with `q(x) ≠ x` and `supp(q)` a compact subset of `J`.
  - `q` is trivial near `S`, including near `0` and `1` if they lie in `S`. So
    `q ∈ St⁰_(F')(S) ≤ H`, and `x ∉ S(ω)`.
- **Equivariance.** `Stab(gω) = g H g⁻¹`, and the fixed points of a conjugate are translates.
- **Fixed by small commutators.** If `q ∈ F'` has `supp(q) ⊆ (0,1) \ S(ω)`, then `q` is trivial on a
  neighbourhood of `S`: `supp(q)` is compact, avoids `S(ω)`, and lies in `(0,1)`. So `q ∈ H`.

**2. Item 2.**
- **(⇒), non-confined part charged.** Let `(Ω, m)` be mean-free. If `m(Ω_free) > 0`, then
  `m(f·1_(Ω_free))/m(Ω_free)` is invariant and mean-free on `Ω_free`. That is (II).
- **(⇒), otherwise.** `m(Ω_conf) = 1`. Define `m'(φ) = m(ω ↦ 1_(Ω_conf)(ω) φ(S(ω)))` for
  `φ ∈ ℓ∞(Conf)`.
  - `m'` is a mean, and it is invariant: `φ(g·S(ω)) = φ(S(gω))`, `Ω_conf` is invariant, and `m` is
    invariant.
  - For open `J ≠ ∅`, step 0 gives `q ∈ F' \ {e}` with `supp(q) ⊂ J`.
  - By step 1, `{ω ∈ Ω_conf : S(ω) ∩ J = ∅} ⊆ Fix(q)`. So `m'({S ∩ J = ∅}) ≤ m(Fix(q)) = 0`.
- **(⇐).** (II) is a mean-free amenable action. Let `m` be as in (I) and `g ≠ e`.
  - Choose an open `J ≠ ∅` on which `g` moves every point.
  - If `g(S) = S`, then `g` fixes `S` pointwise, so `S ∩ J = ∅`.
  - Hence `m(Fix(g)) ≤ m({S ∩ J = ∅}) = 0`.

**3. Item 3.** Put `Y = {ω ∈ Ω_conf : |S(ω)| ≤ k}`. It is invariant by step 1. Suppose
`m(Moved(c) ∩ Y) > 0`.
- The normalized restriction of `m` to `Y` is an invariant mean on the `F`-set `Y` with `t > 0`.
- The witness corollary of `thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived` (normalize on
  `X = Moved(c)`, items 2–3) gives a mean-free invariant mean `m_X` on `Y`.
- Choose `k+1` pairwise disjoint open intervals `J_0, ..., J_k` and, by step 0, `q_i ∈ F' \ {e}` with
  `supp(q_i) ⊂ J_i`.
- Every `ω ∈ Y` has `S(ω) ∩ J_i = ∅` for some `i`, so `Y ⊆ ⋃_i Fix(q_i)` by step 1.
- Then `1 = m_X(Y) ≤ Σ_i m_X(Fix(q_i)) = 0`, a contradiction.

**4. Item 4.** Let `f(S) = n_I(S)/n_(I')(S)`.
- **An interval preserved.** Choose dyadic `a < b` with `I ⊂ (a,b)` and `[a,b] ⊆ I'`, and put
  `h = x_0^[a,b]`.
  - `h` preserves `I'` and pushes compact subsets of `(a,b)` toward `a`.
  - So some `N` has `h^N(max I) < min I`, and the intervals `h^(Ni)(I)`, `i ≥ 0`, are pairwise disjoint
    subsets of `I'`.
- **Translates.** `n_I(h^(-p) S) = n_(h^p I)(S)` and `n_(I')(h^(-p) S) = n_(I')(S)`.
- **Summing.** For `L ≥ 1`, `Σ_(i<L) f(h^(-Ni) S) ≤ 1` pointwise, while `m(f∘h^(-Ni)) = m(f)` by
  invariance. So `m(f) ≤ 1/L` for every `L`.

**5. Item 5.**
- **(II) under amenability.** If `F` is amenable, the left regular action carries an invariant mean with
  `Fix(g) = ∅` for `g ≠ e`. The trivial subgroup is not confined (take `P = {g}`). That is (II).
- **(I) under amenability.** Take Følner sets `A_n` with `|s A_n Δ A_n| ≤ |A_n|/n` for
  `s ∈ {x_0^±1, x_1^±1}`, and enumerate the open dyadic intervals `J_1, J_2, ...`.
  - **A fine grid.** Since `A_n` is finite, pick `L_n` with `2^(1-L_n) < length(g⁻¹ J_k)` for all
    `g ∈ A_n` and `k ≤ n`. Let `G_n = {j 2^(-L_n) : 0 < j < 2^(L_n)}`, so `g G_n ∩ J_k ≠ ∅` for those
    `g, k`.
  - **Almost invariant measures.** `µ_n = |A_n|⁻¹ Σ_(g∈A_n) δ_(g G_n)` has `‖s µ_n - µ_n‖₁ ≤ 1/n`, and
    `µ_n({S ∩ J_k = ∅}) = 0` for `k ≤ n`.
  - **The limit.** A nonprincipal ultralimit is an invariant mean on `Conf`. Every open interval contains
    some `J_k`, so the mean meets every interval: (I).
- **Soficity.** (I) and (II) are mean-free amenable actions (item 2), so `F` is sofic by item 3 of
  `mean-free-amenable-actions-residually-amenable-and-sofic`.

**6. Item 6.**
- **`N_F` is `1` or `F'`.** `N_F` is normal (Elek–Szabó §5), so by the import it is `1` or contains
  `F'`. The regular action of the abelian group `F/F'` has an invariant mean, and every `g ∉ F'` acts on
  it without fixed points. So `N_F ⊆ F'`, and `N_F ∈ {1, F'}`.
- **`N_F = 1`.** Proposition 5.1(2) gives a mean-free amenable action, hence (I) or (II) by item 2.
- **`N_F = F'`.** By the definition of `N_F`, every invariant mean on every `F`-set gives `Fix(g)` mass
  `1` for all `g ∈ F'`.
