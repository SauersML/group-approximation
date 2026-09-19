---
rg: 2
id: level-subpair-line-sections-are-bounded-or-cofinite-proof
kind: route
title: Close the line section at the place t = 0; an open unbounded subgroup of SL_3(F_q((t))) is everything, density pulls finite index back to the Laurent group, and a bounded section fixes a vertex that the level pins within 2n of the base lattice
target: level-subpair-line-sections-are-bounded-or-cofinite
requires:
  - normalised-level-subpairs-cannot-certify-rank-three-cone
---

Proof of [[level-subpair-line-sections-are-bounded-or-cofinite]].  Notation as there.  Write
`O = F_q[[t]]`, `k_0 = F_q((t))`, `G_0 = SL_3(k_0)`, `K = SL_3(O)`, `Λ = SL_3(F_q[t, t^-1])`, and
`L_0 = O^3`.  Embed `F_q[t, t^-1] ⊆ k_0`, so `Λ ≤ G_0`.  A subset of `G_0` is bounded when the pole orders
of its entries are bounded; for `SL_3` this is the same as relative compactness, since the entries of `g^-1`
are cofactors of `g`.

## Step 0: three standard facts

- **(F1)** `F_q[t, t^-1] ∩ O = F_q[t]`, so `Λ ∩ K = SL_3(F_q[t])`.
- **(F2)** `K = E_3(O)`, since `O` is local.  `F_q[t]` is dense in `O`, so the closure of `E_3(F_q[t])` contains
  every `e_ab(O)`, and the closure of `SL_3(F_q[t])` is `K`.
- **(F3)** *An open, non-compact subgroup `H` of `G_0` equals `G_0`.*  This is Tits' theorem; Prasad (1982)
  gives an elementary proof.  Here is the Howe-Moore route.  `G_0 / H` is discrete.  Let `δ ∈ ℓ^2(G_0 / H)` be
  the indicator of the coset `H`.  Then `⟨h δ, δ⟩ = 1` for every `h ∈ H`, and `H` is unbounded.  So this
  coefficient does not vanish at infinity.  By Howe-Moore for `SL_3` over the local field `k_0`, the
  representation `ℓ^2(G_0 / H)` has a nonzero `G_0`-invariant vector, so `G_0 / H` is finite.  Let `N` be the
  normal core of `H`, of finite index.  `PSL_3(k_0)` is simple and infinite, so `N` maps onto it, and
  `G_0 = N Z` with `Z` the finite centre.  `G_0` is perfect, so `G_0 = [N Z, N Z] ⊆ N ⊆ H`.

## Step 1: the closure of `Δ` is open

Let `Γ_0` have finite index in `SL_3(F_q[t])`, with coset representatives `γ_1, .., γ_r`.  The closure of
`SL_3(F_q[t])` is `K` by (F2), so `K = ⋃_i γ_i · closure(Γ_0)`.  So `K_1 = closure(Γ_0)` is a closed subgroup of
finite index in `K`.  Its complement is a finite union of closed cosets, so `K_1` is open.  Since `Γ_0 ≤ Δ`,
the closure of `Δ` contains `K_1` and is open.  Also `K_1 ⊇ e_ab(t^n O)` for all `a ≠ b`, since `Γ_0` contains
the dense subgroup `e_ab(t^n F_q[t])` of `e_ab(t^n O)`.

## Step 2: the unbounded case

Suppose `Δ` is unbounded.  Then its closure is open and non-compact, so it equals `G_0` by (F3).  Thus `Δ` is
dense.  For `λ ∈ Λ`, the set `λ K_1^-1` is open, so it meets `Δ`: `λ = δ κ` with `δ ∈ Δ`, `κ ∈ K_1`.  Then
`κ = δ^-1 λ ∈ Λ ∩ K_1`.  So

```text
Λ = Δ · (Λ ∩ K_1),        [Λ : Δ] ≤ [Λ ∩ K_1 : Δ ∩ K_1].
```

By (F1), `Γ_0 ≤ Δ ∩ K_1 ≤ Λ ∩ K_1 ≤ SL_3(F_q[t])`, and `Γ_0` has finite index in `SL_3(F_q[t])`.  So
`[Λ : Δ] < ∞`: case 1.

## Step 3: the bounded case

Suppose `Δ` is bounded.  Its closure `Δ̄` is compact.  By the Bruhat-Tits fixed-point theorem, `Δ̄` fixes a
point of the building `X` of `G_0`.  `G_0` acts on `X` without inverting types, so `Δ̄` fixes every vertex of
the closed cell containing that point, in particular a vertex `[L]`.  Scale `L` so that `L ⊆ L_0` and
`L ⊄ t L_0`.  An element `g ∈ Δ̄` with `g L = t^j L` has `1 = det g ∈ t^(3j) O^×`, so `j = 0`: every element of
`Δ̄` fixes `L` itself.  Also `Δ̄ ⊇ K_1 ⊇ e_ab(t^n O)` for all `a ≠ b`.

Pick `v ∈ L \ t L_0`.  Some coordinate `v_a` is a unit of `O`.  For `b ≠ a` and `c ∈ O`,

```text
e_ba(t^n c) v - v = t^n c v_a e_b ∈ L,     so  t^n O e_b ⊆ L  for all b ≠ a.
```

Fix `b ≠ a`.  Apply `e_ab(t^n c)` to `t^n e_b ∈ L`: the difference is `t^(2n) c e_a`, so `t^(2n) O e_a ⊆ L`.
Hence `t^(2n) L_0 ⊆ L ⊆ L_0`.

Let `g ∈ Δ`.  Then `g L = L`, so `g L_0 ⊆ g t^(-2n) L = t^(-2n) L ⊆ t^(-2n) L_0`.  The columns of `g` are
`g e_b ∈ t^(-2n) L_0`, so every entry lies in `t^(-2n) O`: pole order at most `2n`.

*Commensurability.*  Let `P = Stab_(G_0)(L) = h K h^-1`, with `h ∈ GL_3(k_0)` and `h L_0 = L`.  `P` and `K` are
compact open, so `P ∩ K` has finite index in `P`.  Hence `Λ ∩ P ∩ K` has finite index in `Λ ∩ P`, and
`Γ_0 ≤ Δ ≤ Λ ∩ P`.  Also `Λ ∩ P ∩ K ≤ SL_3(F_q[t])` by (F1), and it contains `Γ_0`, so it is commensurable with
`SL_3(F_q[t])`.  So `Δ` is commensurable with `SL_3(F_q[t])`: case 2.

*Exclusivity.*  `Λ` is unbounded (it contains `e_12(t^-j)` for all `j`), and a subgroup of finite index in an
unbounded group is unbounded, since finitely many translates cover it.  So case 1 excludes the pole bound of
case 2.  This proves (L1).  ∎

## Step 4: (L2) and (L3)

Let `B ⊇ U_k`, `m ∈ N^d \ {0}`, `t = x^m`.  The monomials `x^m` are algebraically independent over `F_q`
as long as `m ≠ 0`, so `A_m = F_q[t, t^-1]` is a Laurent ring in `t`.  For `j ≥ n` we have `|j m| ≥ k`, so
`e_ab(t^j) ∈ U_k`.  `e_ab` is additive, so `e_ab(t^n F_q[t]) ⊆ U_k ∩ SL_3(A_m) ⊆ Δ_m` for all `a ≠ b`.

`Γ_0 = E_3(t^n F_q[t])` has finite index in `SL_3(F_q[t])`.  Indeed `E(3, F_q[t], t^(2n)) ≤ Γ_0`, by the
standard inclusion `E(3, A, I^2) ≤ E_3(I)` used in [[normalised-level-subpairs-cannot-certify-rank-three-cone]],
and `SL_3(F_q[t], t^(2n)) = E(3, F_q[t], t^(2n))` by Bass-Milnor-Serre.  The quotient
`SL_3(F_q[t]) / SL_3(F_q[t], t^(2n))` is finite.  So (L1) applies to `Γ_0 ≤ Δ_m ≤ SL_3(A_m)`.

*Case 1.*  `F_q[t, t^-1]` is Euclidean for the norm `deg - ord_0`, so `SL_3(A_m) = E_3(A_m)`, and
`Δ_m ∩ E_3(A_m) = Δ_m` has finite index in `E_3(A_m)`.  `A_m` contains the monomial unit `t = x^m`, with
`t^-1 ∈ A_m`.  So (Z3) of [[normalised-level-subpairs-cannot-certify-rank-three-cone]] applies with `A' = A_m`
and gives `e_ab(1) ∈ E_B` for all `a ≠ b`.  Then `SL_3(F_p) = E_3(F_p) ≤ E_B ∩ Gamma = C`.  (Z4) there shows
that the image of `SL_3(F_p)` in `F = PSL_3(F_q)` has trivial centraliser, so `C_F(psi(C)) = 1`.  So `B` is
not a certificate.

*Case 2* is the pole bound and the commensurability of (L1).  This proves (L2).

(L3) is (L2) for `m = c e_l`, where `|m| = c`, `n = ⌈k / c⌉` and `t = s`.  If `Δ_l` has infinite index,
case 1 fails, so case 2 holds: `Δ_l` is bounded at `s = 0`, with the pole bound, and commensurable with
`SL_3(F_q[s])`.  ∎

## Calibration of the method

- *Known finite case.*  `B = G` gives `Δ_m = Λ`, unbounded, case 1, and the proof then recovers
  `e_ab(1) ∈ G`, which is correct.
- *Known bounded case.*  For `B = U_k`, `E_B = U_k ⊆ 1 + M_3(𝔪^k)` with `𝔪^k ⊆ R_+` spanned by the monomials of
  degree `≥ k`.  So `Δ_m ≤ SL_3(F_q[t])`, `[L_0]` is a fixed vertex as in Step 3, and the method does not claim
  `e_ab(1) ∈ B`.  That is correct, since `e_ab(1) ∉ 1 + M_3(𝔪^k)`.
- *Where the method stops.*  Step 2 uses that `k_0` is locally compact.  Over `K((t))` with `K` an infinite
  field (for example `K = F_q(x_2, .., x_d)`, to treat a whole coordinate hyperplane at once), (F3) and Step 1
  fail.  That is why the theorem is stated only for one monomial line at a time.  The group `E_w` of the claim
  shows that the naive multi-variable analogue (bounded on every line implies bounded) is false: all its line
  sections are bounded, yet it has Laurent elements.
