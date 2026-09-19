---
rg: 2
id: ascending-completions-give-only-virtually-cyclic-quotients-proof
kind: route
title: "Proof: the closure of rho(F) is compact-open-normal-by-P; in an ascending completion a letter of positive degree conjugates a fixed compact open subgroup into itself and eventually pulls every degree-zero element into it, so the degree-zero part of P is a finite subgroup normalized by that letter, hence P is finite-by-cyclic"
target: ascending-completions-give-only-virtually-cyclic-quotients
requires:
  - f-cores-reduce-benign-witnesses-to-normalized-ones
  - commensurated-witnesses-survive-browder-but-die-when-linear
---

Verification tier: proposed-established. Elementary point-set topology of
totally disconnected locally compact (tdlc) groups. The only facts used are
these:
- a compact subset of a discrete group is finite;
- an open subgroup is closed;
- for a compact open `K` and an element `g`, `gKg^{-1}` is compact open;
- the Schlichting completion `ρ : Γ -> G` of a commensurated pair `(Γ, Σ)`
  has dense image, `K = closure ρ(Σ)` is compact open, and
  `ρ^{-1}(K) = Σ`.

## Step 1: the closure is compact-open-normal-by-P

Let `ρ : F -> G`, `K` compact open, `N = ρ^{-1}(K)`, `R = ρ(F)`,
`Ĥ = closure R`. Then `ρ(N) = R ∩ K`, and this is normal in `R` because
`N ⊴ F`. The map `F -> R/(R ∩ K)` is onto with kernel
`ρ^{-1}(R ∩ K) = N`, so `P ≅ R/(R ∩ K)`.

`K` is open, so `Ĥ ∩ K = closure(R ∩ K)`. Indeed, any `x ∈ Ĥ ∩ K` is a
limit of elements of `R` that eventually lie in `K`. Call this `M`. It is
compact (closed in `K`) and open in `Ĥ`. Conjugation by `r ∈ R` preserves
`R ∩ K`, hence its closure `M`. By continuity, conjugation by every element
of `Ĥ = closure R` preserves `M`, so `M ⊴ Ĥ`.

`M` is open, so `Ĥ/M` is discrete and `R -> Ĥ/M` is onto (every coset
`xM` is open and meets the dense `R`). Its kernel is `R ∩ M = R ∩ K`. Hence
`Ĥ/M ≅ R/(R ∩ K) ≅ P`. Write `π : Ĥ -> P` for this map.

## Step 2: the parabolic lemma (item 1)

Let `τ ∈ Ĥ` and `x ∈ Ĥ` with `C = closure{τ^n x τ^{-n} : n ≥ 0}` compact.
- `C ⊆ Ĥ` since `Ĥ` is closed, and `π(C)` is compact in the discrete `P`,
  so it is finite.
- Hence `τ̄^a x̄ τ̄^{-a} = τ̄^b x̄ τ̄^{-b}` for some `0 ≤ a < b`.
- Conjugating by `τ̄^{-a}` gives `x̄ = τ̄^d x̄ τ̄^{-d}` with `d = b - a ≥ 1`,
  that is `x̄ ∈ C_P(τ̄^d)`.

For the second statement, let `L ≤ Ĥ` be compact open with `τLτ^{-1} ⊆ L`.
- `π(L) = LM/M` is a compact subgroup of a discrete group, so it is finite.
- `τ̄ π(L) τ̄^{-1} ⊆ π(L)`, and conjugation is injective, so equality
  holds.
- If `τ^n x τ^{-n} ∈ L` for some `n ≥ 0`, then
  `x̄ ∈ τ̄^{-n} π(L) τ̄^n = π(L)`.

## Step 3: ascending completions (item 2)

Let `G` be ascending, with `K`, `t`, `K_k = t^{-k}Kt^k` and
`G_0 = ⋃_k K_k`.
- From `tKt^{-1} ⊆ K` we get `K_k ⊆ K_{k+1}`. So `G_0` is an increasing
  union of compact open subgroups. It is an open subgroup, hence closed.
- `t G_0 t^{-1} = ⋃_k K_{k-1} = G_0`, since `K_{-1} = tKt^{-1} ⊆ K_0`. So
  `G_0 ⊴ G = G_0⟨t⟩`.
- **Every compact subset `C` of `G_0` lies in some `K_k`.** The open cover
  `{K_k}` is increasing, so a finite subcover is a single `K_k`.

Let `K'` be compact open with `N = ρ^{-1}(K')`. Apply Step 1 with `K'`:
this gives `M = Ĥ ∩ K'` and `π : Ĥ -> P`. Let `g_1, ..., g_s` be the
images of a finite generating set of `F`.

**Local ellipticity.** If `x_1, ..., x_r ∈ Ĥ ∩ G_0`, they lie in one
`K_k`, so `⟨x_1, ..., x_r⟩ ⊆ Ĥ ∩ K_k`. That set is compact, so its image in
the discrete `P` is finite. Hence `π(Ĥ ∩ G_0)` is locally finite.

**Case A: `t^e ∈ G_0` for some `e ≥ 1`.** Then `G_0 ⊴ G` has finite
index, and `Ĥ/(Ĥ ∩ G_0)` embeds in the finite group `G/G_0`.
- The preimage of `π(Ĥ ∩ G_0)` in `Ĥ` is `(Ĥ ∩ G_0)M`, which contains
  `Ĥ ∩ G_0` and so has finite index in `Ĥ`. Hence `π(Ĥ ∩ G_0)` has finite
  index in `P`.
- A finite-index subgroup of the finitely generated group `P` is finitely
  generated. Being locally finite, it is finite.

So `P` is finite.

**Case B: `t^e ∉ G_0` for all `e ≠ 0`.** Then `Δ : G -> G/G_0 ≅ Z`,
`Δ(t) = 1`, is a continuous homomorphism. `Δ(K')` is a compact subgroup of
the discrete group `Z`, so it is 0. Hence `M ⊆ K' ⊆ G_0`.
So `Δ|_Ĥ` factors through `P`, as `Δ̄ : P -> Z`. Put
`P_0 = ker Δ̄ = π(Ĥ ∩ G_0)`.

- If `Δ(Ĥ) = 0`, then `Ĥ ⊆ G_0`. The finitely many generators
  `g_1, ..., g_s ∈ G_0` of `R` lie in one `K_k`. So `R ⊆ K_k`, `Ĥ ⊆ K_k`
  is compact, and `P = π(Ĥ)` is finite.
- Otherwise `Δ(Ĥ) = mZ` with `m ≥ 1`. Pick `τ ∈ Ĥ` with `Δ(τ) = m`.
  Then `τ = g t^m` with `g ∈ G_0`, and `g ∈ K_j` for some `j ≥ 0`.

**Contraction.** For `k ≥ j + m`:

`τ K_k τ^{-1} = g t^m t^{-k} K t^k t^{-m} g^{-1} = g K_{k-m} g^{-1} = K_{k-m}`,

since `g ∈ K_j ⊆ K_{k-m}`. With `k_0 = j + m` this gives
`τ K_{k_0} τ^{-1} = K_j ⊆ K_{k_0}`. Now iterate from any `x ∈ G_0`:
- `x ∈ K_k` for some `k ≥ k_0`;
- while the level is `≥ k_0 + m`, one conjugation lowers it by `m`;
- once the level `ℓ` lies in `[k_0, k_0 + m)`, one more conjugation gives
  `K_{ℓ - m} ⊆ K_{k_0}`, because `ℓ - m ≥ j`.

So `τ^n x τ^{-n} ∈ K_{k_0}` for all large `n`.

**Conclusion.** Put `L = Ĥ ∩ K_{k_0}`. It is compact open in `Ĥ` and has
`τLτ^{-1} ⊆ L`. Every `x ∈ Ĥ ∩ G_0` satisfies `τ^n x τ^{-n} ∈ L` for
large `n`. By Step 2, `P_0 = π(Ĥ ∩ G_0) ⊆ π(L)`, which is finite. Then
`P/P_0 ≅ Δ(Ĥ) = mZ`, so `P` is finite-by-`Z`. ∎ (item 2)

## Step 4: ascending witnesses (item 3)

Assume `t ∈ Λ`, `tΣt^{-1} ⊆ Σ` of finite index, `Λ_0 = ⋃_k t^{-k}Σt^k`,
`Γ = Λ_0⟨t⟩`, and `F ⊆ Γ`.
- `t^{-k}Σt^k ⊇ Σ` with index `[Σ : t^kΣt^{-k}] < ∞`. So every
  `g ∈ Λ_0` lies in a group containing `Σ` with finite index, and
  commensurates `Σ`. Also `t` does.
- `tΛ_0t^{-1} = Λ_0`, as in Step 3. So `Λ_0 ⊴ Γ`, and `Γ` commensurates
  `Σ`.

Let `ρ : Γ -> G` be the Schlichting completion, with `K = closure ρ(Σ)`.
- `ρ(t)Kρ(t)^{-1} = closure ρ(tΣt^{-1}) ⊆ K`.
- `closure ρ(Λ_0) = ⋃_k ρ(t)^{-k} K ρ(t)^k = G_0`. The right side is an
  open subgroup, hence closed; it contains `ρ(Λ_0)` densely.
- `G_0⟨ρ(t)⟩` is an open subgroup containing the dense `ρ(Γ)`, so it
  equals `G`.

So `G` is ascending. Moreover `N = F ∩ Σ = F ∩ ρ^{-1}(K)`, since
`ρ^{-1}(K) = Σ`. Item 2 applies with `K' = K`.

For an ascending HNN extension `Λ = Σ*_φ`, the kernel of `Λ -> Z` is
`⋃_k t^{-k}Σt^k`, so `Λ = Γ` and every `F ≤ Λ` qualifies. ∎ (item 3)

## Step 5: consequences and sharpness

- `Z/2 ≀ Z`, `U`, `V`, Grigorchuk's group and `Z^2` are finitely generated
  and not virtually cyclic. Each contains either `Z^2` or infinitely many
  torsion elements. Neither is possible in a finite-by-`Z` group, whose
  torsion elements all lie in the finite kernel. So item 2 excludes them.
- **Lamps are two-sided.** Let `P = Z/2 ≀ Z`, and let `τ̄` be any element
  outside the base, for example the shift generator. A base element `b ≠ 0` has finite support, so
  `τ̄^d b τ̄^{-d} ≠ b` for every `d ≥ 1`. Hence `C_P(τ̄^d) ∩ base = 0`. By
  Step 2, applied to `τ` and to `τ^{-1}`, every lamp preimage outside `M`
  lies outside `par(τ) ∪ par(τ^{-1})`.
- **`Z[1/6] ⋊ Z^2`.** It is the ascending HNN extension of
  `BS(1,2) = Z[1/2] ⋊ ⟨2⟩` along multiplication by `3`, which is injective
  with image of index 3. So it is torsion-free of type `F`, with
  `cd = 3`.
  - `Σ = Z` is commensurated, since `2Z` and `3Z` have finite index.
  - The complement `Z^2 = ⟨(0,2), (0,3)⟩` meets `Σ` trivially.
  - For `π : F_2 -> Z^2` onto, embed `F_2 -> Λ × F_2` by `f ↦ (π(f), f)`
    and put `Σ' = Σ × F_2`. This is a type `F` witness (torsion-free)
    commensurated by the diagonal `F_2`, with
    `F_2 ∩ Σ' = π^{-1}(Z^2 ∩ Σ) = ker π`. So `P = Z^2`, and item 2 fails
    for two contracting letters. ∎
