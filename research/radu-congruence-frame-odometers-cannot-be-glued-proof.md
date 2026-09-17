---
rg: 2
id: radu-congruence-frame-odometers-cannot-be-glued-proof
kind: route
title: Ball fixators are strictly decreasing on every branch because the vertex group is infinite, so no two second-prime levels coincide on the edge group, and Lemma G with the congruence gap charges every gluing
target: radu-congruence-frame-odometers-cannot-be-glued
requires:
  - expanding-matchings-need-a-shared-stabilizer
  - radu-horizontal-quotient-is-arithmetic-lattice
  - homogeneous-quotient-soficity-gives-vertex-soficity
---

Notation of the claim. `d` is the path metric of `T'`, `B(q,M)` is a closed ball and `S(q,M)` a sphere.
Write `p' = xp`, `N'_M = xN_Mx = Fix_Q(B(p',M))`, and `C_1 = xC_0x = Fix_Q(p')`.

**Step 0: structure.**
* *Faithfulness.* `ρ'` is injective on `Q ≤ PB^×(F)`, since the global group embeds in its completion.
  So `Q` acts faithfully on `T'`.
* *Transitivity.* By item 1 of `radu-horizontal-quotient-is-arithmetic-lattice`, `Q` is transitive on
  `V(T')`, `<xz, xyx> ≤ C_0` acts as `S_3` on the three edges at `p`, and `x` inverts an edge at `p`.
  Call that edge `e' = [p, p']`.
* *The vertex group.* `C_0` acts on the finite ball `B(p,M)`, so `N_M` is normal of finite index in `C_0`.
  `C_0 ⊇ C_χ ≅ C_2^(*4)` is infinite. For `M ≥ 1`, `N_M ⊆ B`. `N_0 = C_0`.
* *Amalgam.* `x^2 = 1`, and `x` normalizes `B` because it swaps `p` and `p'`. The graph of groups of
  `Q ↷ T'` has one vertex and one half-edge, so `Q = <C_0, x>` with relations `xsx = φ(s)`, `s ∈ B`.
* *Levels.* `Fix_L(B(p,M))` is the kernel of `PGL_2(Z_2) → PGL_2(Z/2^M)` acting on
  `S(p,M) ≅ P^1(Z/2^M)`. So `N_M` is the principal `𝔮'`-adic congruence subgroup of level `𝔮'^M`.

**Step 1: strict decrease.** *If `N_k = N_(k+1)` for some `k ≥ 0`, then `N_k = 1`.*
* *All vertices.* By vertex transitivity, `Fix_Q(B(q,k)) = Fix_Q(B(q,k+1))` for every vertex `q`.
* *Induction.* Let `g ∈ N_k = N_(k+1)`, and suppose `g` fixes `B(q,k+1)` for all `q` with `d(p,q) ≤ n`.
  Let `q'` be a neighbour of such a `q`. Then `B(q',k) ⊆ B(q,k+1)`, so `g ∈ Fix_Q(B(q',k)) = Fix_Q(B(q',k+1))`.
  Hence `g` fixes `B(q,k+1)` for all `q` with `d(p,q) ≤ n+1`.
* *Conclusion.* So `g` fixes `T'`, and `g = 1` by faithfulness.

`N_k` has finite index in the infinite group `C_0`, so `N_k ≠ 1`. Hence **`N_k ⊋ N_(k+1)` for every `k ≥ 0`**.

**Step 2: every branch.** *For `M ≥ 1` and each neighbour `u` of `p`, `N_M` moves some vertex of
`S_u := {w ∈ S(p,M+1) : the geodesic [p,w] passes through u}`.*
* *Nontriviality on the sphere.* By Step 1, `N_M` acts nontrivially on `S(p,M+1)`.
* *Branches are preserved.* `N_M` fixes the three neighbours of `p`, so it preserves each `S_u`.
* *Transport.* If `N_M` is trivial on `S_u`, then for `g ∈ C_0` the group `gN_Mg^(−1) = N_M` is trivial on
  `S_(gu)`. `C_0` is transitive on the neighbours of `p`, so `N_M` would be trivial on all of
  `S(p,M+1)`, a contradiction. ∎

**Step 3: noncoincidence (item 1).** Let `(M, M') ≠ (0,0)`. The conjugation by `x` swaps `(N_M, N'_(M'))`
with `(N'_M, N_(M'))` and fixes `B`, so we may assume `M ≥ M'` and `M ≥ 1`.
* *A witness.* By Step 2 applied at `u = p'`, some `g ∈ N_M` moves a vertex `w` with `d(p,w) = M+1`
  and `p' ∈ [p,w]`. Then `xgx ∈ N'_M` moves `xw`.
* *Where `xw` lies.* `d(p, xw) = d(xp', xw) = d(p', w) = M`, so `xw ∈ B(p,M)` and `xgx ∉ N_M`.
* *Membership.* `N'_M ⊆ N'_(M')` because `M ≥ M'`. `N'_M ⊆ Fix_Q(p) ∩ Fix_Q(p') = B` because
  `p ∈ B(p',1) ⊆ B(p',M)`.

So `xgx ∈ (B ∩ N'_(M')) \ (B ∩ N_M)`. ∎

**Step 4: uniform expansion of diagonal orbits.** Fix `S_B` and a transversal `r_1, r_2, r_3` of `B` in
`C_0`. For `c ∈ S_C` write `c^(−1) r_j = r_(i(c,j)) b_(c,j)`, where `b_(c,j)` lies in a fixed finite set
`W ⊆ B` of `S_B`-word length at most `ℓ`.

*(a) Gap for `B`.* Let `k ≥ 1` and `f ∈ ℓ^2(B/N_k)` with mean zero. Since `N_k ⊆ B`, we have
`C_0/N_k = ⊔_i r_i·(B/N_k)`. Define `F(r_i u) = f(u)`. Then `F` has mean zero and `||F||^2 = 3||f||^2`.
For `c ∈ S_C`,

```text
(cF)(r_j u) = F(c^(-1) r_j u) = f(b_(c,j) u),    so   ||cF − F||^2 = Σ_j ||b_(c,j)^(-1) f − f||^2  ≤  3 ℓ^2 max_(s∈S_B) ||sf − f||^2.
```

By `(τ_𝔮')`, `max_(s∈S_B)||sf − f|| ≥ (κ/ℓ)||f||` for all `k ≥ 1`.

*(b) Diagonal orbits.* Let `v ∈ C_0/N_M` and `v' ∈ C_1/N'_(M')`, with `k = max(M,M')+1`. Then
`B(p',M') ⊆ B(p, M'+1) ⊆ B(p,k)`, so the stabilizer `B ∩ N_M ∩ N'_(M')` contains `N_k`. `N_k` is normal in
`B`, so the diagonal orbit `O` is a quotient `B`-set of `B/N_k`, with fibres of constant size.
* *Lifting.* A set `U ⊆ O` with `|U| ≤ |O|/2` lifts to `Ũ ⊆ B/N_k` with the same proportion, and
  `|∂_s Ũ| = (fibre)·|∂_s U|`.
* *Cheeger.* Take `f = 1_Ũ − |Ũ|/|B/N_k|`. Then `||f||^2 ≥ |Ũ|/2` and `||sf − f||^2 = 2|∂_s Ũ|`, so
  `Σ_s |∂_s U| ≥ h|U|` with `h = κ^2/(4ℓ^2)`.

**Step 5: the defect `(R1)`.**
* *Two `B`-sets.* `V_0 = V` with `B` acting by `ρ`. `V_1 = V` with `C_1` acting by `c·v = ρ(xcx)v`. Its
  orbits are `C_1/N'_M`, where `M` is the level of `v` for `ρ`, and its `B`-action is `s·v = ρ(φ(s))v`.
* *The bijection.* Let `τ = X : V_0 → V_1`. Then `τ(sv) ≠ sτ(v)` iff `Xρ(s)v ≠ ρ(φ(s))Xv`, so the left
  side of `(R1)` is the left side of `(G1)` in Lemma G of `expanding-matchings-need-a-shared-stabilizer`.
* *Stabilizers.* The `B`-stabilizer of `v ∈ V_0` is `B ∩ N_(M(v))`, since `N_M` is normal in `C_0`. That
  of `Xv ∈ V_1` is `B ∩ N'_(M(Xv))`.
* *Coincidence.* By Step 3 the orbit through `(v, Xv)` is coincident only if `M(v) = M(Xv) = 0`.
* *Expansion.* By Step 4 every noncoincident orbit is an `h`-expander.

Lemma G gives `(R1)`. ∎

**Step 6: robust form (item 3).**
* *Words.* Write each `s ∈ S_B` and `φ(s)` as words of length at most `ℓ'` in `S_C`, and put all prefixes
  into `F`.
* *Near-agreement.* `σ(s)` and `ρ(s)` differ on at most `ℓ'(δ + ε)|V|` points. The same holds for `φ(s)`.
* *The relation.* `σ(x)σ(s) ≈ σ(xs) = σ(φ(s)x) ≈ σ(φ(s))σ(x)`, off `2ε|V|` points.
* *Comparison.* With `X = σ(x)`, the left side of `(R1)` is at most `|S_B|(2ℓ'(δ+ε) + 2ε)|V|`. ∎

**Step 7: microstates (item 4).**
* *Displacement.* Fix `c_0 ∈ C_0 \ {1}`. Since `Λ` is torsion-free and `K_p` is compact, `c_0` has no fixed
  point on `L/Λ`: `c_0 gΛ = gΛ` would put `c_0 ∈ gΛg^(−1) ∩ K_p = {1}`. By compactness
  `δ_0 = min_ξ d(c_0ξ, ξ) > 0`.
* *Level-0 points are bad.* Take `ε < δ_0`. If `v` lies in a level-0 orbit of `ρ`, then `ρ(c_0)v = v`.
  Either `σ(c_0)v ≠ ρ(c_0)v`, which happens on at most `O(δ + ε)|V|` points, or
  `d(y(v), c_0y(v)) < ε < δ_0` fails `(HV1)`, which happens on at most `ε|V|` points.
* *Conclusion.* So `|{level ≥ 1}| ≥ (1 − O(δ+ε))|V|`. Step 6 gives `h(1 − O(δ+ε)) ≤ O(δ+ε)`, which is false
  once `δ, ε ≤ δ_*` for a `δ_*` depending only on `h` and the word constants.
* *Frame sets.* The depth-`M` frame sets `K_p(M)\L/Λ` are unions of `C_0/N_M`. The stabilizer of
  `K_p(M)gΛ` in `C_0` is `C_0 ∩ K_p(M)·gΛg^(−1)`. A product `kλ ∈ K_p` has `λ ∈ gΛg^(−1) ∩ K_p = {1}`, so
  that stabilizer is `N_M`. ∎

**Status of inputs.** Steps 0–3 and 5–7 are complete, given item 1 of
`radu-horizontal-quotient-is-arithmetic-lattice`. Step 4 uses `(τ_𝔮')`, which is cited and not re-derived
here. The chain it rests on is:
* `C_0` is `{𝔮}`-arithmetic in the totally definite quaternion algebra over `Q(√17)`, split at `𝔮`;
* strong approximation away from `𝔮` identifies `ℓ^2(C_0/N_M)` with automorphic forms of level `𝔮'^M`;
* Jacquet–Langlands transfers them to Hilbert modular forms;
* the Ramanujan bound at `𝔮` (Blasius, or any Gelbart–Jacquet-type exponent `< 1/2`) gives the gap;
* one-dimensional representations only contribute eigenvalue `−3`, and eigenvalue `+3` means constant on
  the connected graph `N_M\T_h`;
* the Švarc–Milnor comparison, with the uniform constants of the cocompact action `C_0 ↷ T_h`, converts the
  graph gap into the generator gap on `C_0/N_M`.
