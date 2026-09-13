---
rg: 2
id: thompson-f-two-transitive-stabilizers-minimal-not-confined-proof
kind: route
title: Invariant closed sets and the commutator lemma both put a rigid stabilizer group inside a point stabilizer
target: thompson-f-two-transitive-stabilizers-minimal-not-confined
requires:
  - thompson-f-two-transitive-actions-are-faithful
  - thompson-f-two-transitive-rigid-stabilizers-fix-no-point
  - confined-subgroup-commutator-lemma
---

Notation: `F_W^c` = elements with compact support in an open interval `W`. For
dyadic `c < d`, `F_{(c,d)}^c` is the derived subgroup of the copy of `F`
supported on `[c,d]`, so it is simple, infinite and perfect. For any open `W`,
`F_W^c` is a directed union of such groups. Hence it is perfect and has no
proper finite-index subgroup: a finite-index subgroup meets each simple
infinite piece in a finite-index subgroup, hence contains it.

1. A 2-transitive action is primitive, so `H` is maximal. `HF' ⊋ H` since
   `F' ⊄ H` by faithfulness, so `HF' = F`. If `H ∩ F' = 1` then
   `H ≅ HF'/F' = F/F'` is abelian. An abelian group transitive on `Ω \ {ω}`
   acts regularly there, so the action would be sharply 2-transitive. Then an
   element `s` swapping two points has `s^2` fixing both, so `s^2 = 1`, but `F`
   is torsion-free. Contradiction. The same swap argument gives item 4.
2. Suppose `H` preserves a closed `K ⊂ (0,1)` with `∅ ≠ K ≠ (0,1)`. `F`-orbits
   in `(0,1)` are dense, so `Stab_F(K) ≠ F`, and maximality gives
   `H = Stab_F(K)`. `(0,1) \ K` contains an open interval `U`, and `F_U^c` acts
   trivially on `K`, so `F_U^c ≤ H`. This contradicts
   `thompson-f-two-transitive-rigid-stabilizers-fix-no-point`.
3. Suppose `H` is confined by `F ≤ Sym((0,1))`, with confining set `P`,
   `r = |P|`. `F` is torsion-free, so `σ^2 ≠ 1` for `σ ∈ P`, and
   `confined-subgroup-commutator-lemma` gives an open displacement
   configuration `{Ω_σ}`. Check its hypotheses:
   - `R_F(Ω_σ) ⊇ F_W^c ≠ 1` for any open interval `W ⊆ Ω_σ`.
   - Nontrivial conjugacy classes of `R := R_F(Ω_σ)` are infinite. If
     `n ∈ R \ {1}` had a finite class, its centralizer would have finite index
     and so contain every `F_W^c` with `W ⊆ Ω_σ`. But `n` moves some `t`, and a
     small interval `W_1 ∋ t` inside `Ω_σ` with `nW_1 ∩ W_1 = ∅` carries
     `f ∈ F_{W_1}^c \ {1}`, and `nfn^{-1}` is supported in `nW_1`, so it is not
     `f`.
   So there are `ρ` and `1 ≠ N ≤ H ∩ R_F(Ω_ρ)` whose normalizer `K` has index
   `≤ r` in `R_F(Ω_ρ)`. Then `K ⊇ F_W^c` for every open interval
   `W ⊆ Ω_ρ`. Pick `n ∈ N \ {1}`, a point `t` with `n(t) ≠ t` (so
   `t ∈ Ω_ρ`), and an open interval `W_1 ∋ t`, `W_1 ⊆ Ω_ρ`, with
   `nW_1 ∩ W_1 = ∅`. For `f_1, f_2 ∈ F_{W_1}^c ⊆ K`:
   - `[n,f_1] = n·(f_1 n^{-1} f_1^{-1}) ∈ N`, and it equals `u·f_1^{-1}` with
     `u = n f_1 n^{-1}` supported in `nW_1`;
   - `u` commutes with `F_{W_1}^c`, so `[[n,f_1],f_2] = [f_1^{-1}, f_2]`;
   - this commutator lies in `N`, since `f_2` normalizes `N`.
   Hence `N ⊇ [F_{W_1}^c, F_{W_1}^c] = F_{W_1}^c`, so `F_{W_1}^c ≤ H`,
   contradicting `thompson-f-two-transitive-rigid-stabilizers-fix-no-point`.
   Finally, `H` confined means some finite `P` meets every conjugate
   `F_{gω}`, i.e. every point is fixed by some `p ∈ P`. So "not confined" is
   item 3 as stated.
