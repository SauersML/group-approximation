---
rg: 2
id: relative-countable-eg-gives-eg-for-aleph-one-groups-proof
kind: route
title: Filter a cd-2 group of size aleph_1 by elementary submodels, show every step has pd I_{G_beta/G_alpha} at most 1, and extend 2-complexes by REG_omega with unions at limits
target: relative-countable-eg-gives-eg-for-aleph-one-groups
requires: []
artifacts: []
---

Assume REG_ω. Let `|G| ≤ ℵ_1` and `cd G ≤ 2`. If `G` is countable, apply REG_ω with `H = 1`: then `I_{G/1} = I_G` has `pd ≤ 1`, and `K` is a point. So assume `|G| = ℵ_1`.

**Step 0: a free resolution.**
- Since `cd G ≤ 2`, there is an exact sequence `0 → P → F_0 → I_G → 0` with `F_0` free on a basis `B_0` and `P` projective.
- Choose `Q` with `P ⊕ Q` free (Q exists because P is projective), and let `F` be free of infinite rank at least the rank of that free module. By the Eilenberg swindle, `P ⊕ F` is free.
- Replacing `F_0` by `F_0 ⊕ F` gives `0 → F_1 → F_0 → I_G → 0`, with `F_1, F_0` free on bases `B_1, B_0` and with differential `d` and augmentation `ε`.

**Step 1: the filtration.**
- Fix a large regular `θ`.
- Take a continuous increasing chain `(M_α)_{α<ω_1}` of countable elementary submodels of `H(θ)`. Each contains `G`, `B_0`, `B_1`, `d`, `ε` and an enumeration `ω_1 → G`, and the union contains all of `G`.
- Put `G_α = G ∩ M_α`. This is a continuous chain of countable subgroups with union `G`.
- Set `M_{-1} := ∅`, so that `G_{-1} = 1`.

Two standard facts are used throughout.
- **(E1)** A finite set that lies in `M` has all its elements in `M`, because `ω ⊆ M`.
- **(E2)** If a first-order statement with parameters in `M` has a witness in `H(θ)`, it has one in `M`.

**Step 2: restricted resolutions.** For `α < ω_1`, let `F_i^α` be the `ZG_α`-submodule of `F_i` spanned by `B_i ∩ M_α`. It is free on that set, and `F_i ∩ M_α = F_i^α`: by (E1), the support and the coefficients of an element of `M_α` lie in `M_α`.

*Claim.* `0 → F_1^α → F_0^α → I_{G_α} → 0` is exact.

- **`d` preserves the submodules.** For `b ∈ B_1 ∩ M_α` we have `d(b) ∈ F_0 ∩ M_α = F_0^α`, and `d` is `ZG`-linear.
- **`ε` lands in `I_{G_α}`.** Similarly `ε(F_0^α) ⊆ ZG_α ∩ I_G = I_{G_α}`.
- **Surjectivity.** For `g ∈ G_α`, the element `g − 1 ∈ M_α` has a preimage in `F_0`, hence by (E2) one in `F_0 ∩ M_α`. These elements generate `I_{G_α}`.
- **Exactness in the middle.** Let `x ∈ F_0^α` with `ε(x) = 0`. Then `x ∈ M_α`, so `x = d(y)` for some `y ∈ F_1`. By (E2), `y` can be chosen in `F_1 ∩ M_α = F_1^α`.
- **Injectivity.** `d` is injective.

**Step 3: the pd lemma.** For `−1 ≤ α < β < ω_1`, `pd_{ZG_β} I_{G_β/G_α} ≤ 1`.

- **Induce up.** Apply the exact functor `ZG_β ⊗_{ZG_α} −` (exact because `ZG_β` is free over `ZG_α`) to the α-sequence. It maps into the β-sequence.
- **Vertical maps on the free terms.** For `i = 0, 1`, the map is the inclusion of the free submodule on `B_i ∩ M_α` into the module free on `B_i ∩ M_β`. It is injective with free cokernel on `B_i ∩ (M_β ∖ M_α)`.
- **Vertical map on the third term.** `ZG_β ⊗ I_{G_α} → I_{G_β}` is injective by flatness, with image `ZG_β · I_{G_α}`. Its cokernel is `I_{G_β} / ZG_β I_{G_α} = ker(Z[G_β/G_α] → Z) = I_{G_β/G_α}`, since `ZG_β / ZG_β I_{G_α} = Z[G_β/G_α]`.
- **Snake lemma.** All three vertical maps are injective, so the cokernels form a short exact sequence `0 → (free) → (free) → I_{G_β/G_α} → 0`. ∎

**Step 4: the recursion.** Build 2-dimensional `K(G_α,1)`'s `K_α`, each a subcomplex of the next and inducing the inclusions of subgroups.
- **Start.** `K_0` comes from REG_ω applied to `(G_0, 1)`, using Step 3 with `α = −1`.
- **Successor.** `K_{α+1}` comes from REG_ω applied to `(G_{α+1}, G_α, K_α)`. The hypotheses hold: `cd G_{α+1} ≤ cd G ≤ 2`, and Step 3 gives the pd condition. Choose basepoints compatibly.
- **Limit `μ`.** `K_μ = ⋃_{α<μ} K_α` is 2-dimensional and aspherical with `π_1 = G_μ`. This is Lemma 3 of `continuous-free-chain-unions-have-gd-two-proof` together with continuity.

Finally `⋃_{α<ω_1} K_α` is a 2-dimensional `K(G,1)`. ∎

**Remarks.**
- **Consistency check.** Step 3 with `α = −1` also re-proves `cd G_β ≤ 2` for every `β`.
- **Converse to Step 3 (heuristic, not used and not proved here).** If `gd G = 2` with a 2-dimensional `K(G,1)` `X ∈ M_0`, one expects, via (E2) applied to null-homotopies and covering-space data, that the subcomplexes spanned by cells in `M_α` are aspherical `K(G_α,1)`'s. So on some filtration the recursion can be realized. The only missing ingredient for the unconditional statement is the ability to extend an *arbitrary* given `K_α`, which is exactly REG_ω.
