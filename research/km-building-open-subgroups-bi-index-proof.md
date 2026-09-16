---
rg: 2
id: km-building-open-subgroups-bi-index-proof
kind: route
title: Pass to the closure in the completion, apply the Caprace--Marquis classification of open subgroups, then count Bruhat double cosets through a nested chain of Coxeter roots
target: km-building-open-subgroups-have-infinite-bi-index
requires: []
artifacts:
  - research/artifacts/km-building-open-subgroups-bi-index-2026-09-16.md
---

The full proof, with verbatim pins and line numbers, is §0--§3 of the artifact. This node lists
every step and every import.

## Imports

- **[CM] Caprace--Marquis, arXiv:1108.4934v2, TeX `OpenKM_rev.tex`, read 2026-09-16.**
  - l.822--826: `Λ = 𝒢(F_q)` embeds densely in `G`, which is locally compact, totally
    disconnected and acts on `Δ_+`. `(B,N)` is a BN-pair of type `(W,S)` for `G`, `B` is compact
    open, `H = B ∩ N`, and `P_J = BW_JB` is open.
  - l.844: `P_J = Stab_G(R_J(C_0))`.
  - No irreducibility is assumed in this setup (l.819--826).
  - Theorem `thm complet` (l.907--916): for an open subgroup `O ≤ G` there are `K ⊆ S` and
    `g ∈ G` with `gOg^{-1}` of finite index in `P_K`.
  - Lemma `lemme racine essentielle` (l.782--784): for essential `L ⊆ S` and `α ∈ Φ_L` there is
    `w ∈ W_L` with `wα ⊊ α`. Its proof cites Hée, Prop. 8.1, which was not read. The statement
    is imported as stated.
- **[CR] Caprace--Rémy, arXiv:math/0607664v2, TeX `SimplSuperrigid.tex`.**
  - Proposition `prop:TopoCompletions` (ii)--(iii): the action of `G` extends that of `Λ`.
  - l.511--512: the kernel of `Λ ↷ Δ_+` is `Z_Λ(Λ^†)`.
- **Standard Coxeter and BN-pair facts** (Bourbaki *Lie IV--VI* Ch. IV §1; Abramenko--Brown
  GTM 248 Ch. 2--3, 6; chapter level, not re-read):
  - the sign character;
  - the exchange and deletion conditions;
  - axiom (BN3), `sBw ⊆ BwB ∪ BswB`;
  - that the half-spaces of a wall of `Σ(W,S)`, as chamber sets, are the components of the
    chamber graph after deleting the edges through that wall (used only in (C7)).

## Proof

**Step 1: transfer (artifact §3.1).** Let `Λ ∩ V ⊆ M` with `V` open, and `O = closure_G(M)`.
1. `V ⊆ closure(Λ ∩ V) ⊆ O`, because `Λ` is dense and `V` open. So `O` is open.
2. `MV` is a union of left `V`-cosets whose complement is too, so it is clopen. Hence
   `O ⊆ MV`, and `Λ ∩ MV = M` because `Λ ∩ V ⊆ M`. So `Λ ∩ O = M`.
3. `ΛO = G` by density, so `λM ↦ λO` is a `Λ`-equivariant bijection `Λ/M → G/O`.
4. For each `gO`, the stabilizer `O ∩ gOg^{-1}` is open in `O`, and `M` is dense in `O`. So the
   `M`-orbits and `O`-orbits on `G/O` coincide.

Hence `[Λ:M] = [G:O]` and `|M\Λ/M| = |O\G/O|`.

**Step 2: classification (§3.2).** By `thm complet`, `O' = gOg^{-1}` has finite index in some
`P_K`.
- **If `K = S`.** `P_S = Stab_G(Δ) = G`, so `[Λ:M] < ∞`.
- **If `K ⊊ S`.** `|O\G/O| = |O'\G/O'| ≥ |P_K\G/P_K|`.

**Step 3: Bruhat (§3.3).**
- **(B1)** `BwB = Bw'B ⇒ w = w'`, by induction on `min(ℓ(w), ℓ(w'))` using (BN3) and `B ∩ N = H`.
- **(B2)** `P_K n_w P_K ⊆ ⋃_{x,y∈W_K} BxwyB`, by iterating (BN3) and its inverse.
- **(B3)** Consequently `W_Kw W_K ↦ P_K n_w P_K` is injective, and `|P_K\G/P_K| ≥ |W_K\W/W_K|`.

**Step 4: Coxeter lemma (§3.4).** Let `(W,S)` be irreducible with `W` infinite, and `K ⊊ S`.
Put `α_s = {x : ℓ(sx) > ℓ(x)}` and `Φ^c = {vα_s}`.
- **(C0)--(C1)** `W_K ∩ S = K`, and `W_K ⊆ α_s` for `s ∈ S∖K` (exchange condition).
- **(C2)--(C5)** Folding: `x ∈ α_s`, `xu ∉ α_s ⇒ sx = xu`. Hence:
  - `α_s` and its complement `sα_s` are connected;
  - the edges cut by `vα_s` are exactly those with `xux^{-1} = vsv^{-1}`;
  - each edge `{y, yu}` is cut, from `y` towards `yu`, by at most one root.
- **(C6)** `#{β ∈ Φ^c : 1 ∈ β, w ∉ β} ≤ ℓ(w)`: assign to each such `β` the first edge of a
  geodesic from `1` to `w` that it cuts.
- **(C7)** Removing the edges through the wall of `vsv^{-1}` leaves exactly the components
  `vα_s` and `vsα_s`. So [CM]'s roots are `Φ^c`, and [CM]'s `α_s` is this `α_s`.
- **(C8)** Fix `s ∈ S∖K`.
  1. `S` is essential and `sα_s ∈ Φ_S`. The nesting lemma gives `h` with `h(sα_s) ⊊ sα_s`, that
     is `hα_s ⊋ α_s`.
  2. The roots `α_i = h^iα_s` form a strict chain containing `W_K`, and `h^n sW_K ⊆ W∖α_n`.
  3. For `w' = u h^n s u'` with `u, u' ∈ W_K`, the `n+1` roots `uα_0, …, uα_n` contain `1` and
     miss `w'`. By (C6), `ℓ(w') ≥ n+1`.
  4. So the minimal length in `W_K h^n s W_K` is unbounded in `n`, and `|W_K\W/W_K| = ∞`.

With Steps 1--3 this proves (A).

**(A') (§3.5).** Suppose every `W_K` with `K ⊊ S` is finite, which forces `(W,S)` to be
irreducible, and let `K ⊊ S` be given by Step 2.
1. `P_K` is a finite union of the compact sets `BxB`, so `O'`, being closed in `P_K`, is compact.
2. The cosets `n_wB`, `w ∈ W`, are pairwise distinct by (B1), so `[G:B] = ∞` and `G` is not
   compact.
3. Finitely many compact double cosets `OgO` cannot cover `G`, so `|O\G/O| = ∞`.

This uses neither (C7) nor the nesting lemma.

**(A'').** For `N ⊆ Z_Λ(Λ^†)` normal, the preimage in `Λ` of a subgroup of `Λ/N` containing the
image of `Λ ∩ V` contains `Λ ∩ V`. It has the same index and the same number of double cosets.
∎
