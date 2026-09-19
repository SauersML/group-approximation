---
rg: 2
id: f-cores-reduce-benign-witnesses-to-normalized-ones-proof
kind: route
title: "Proof: N is normal in F and lies in Sigma, so it lies in every F-conjugate of Sigma and hence in the F-core, which F normalizes; Browder's trivial-action bound and the finitely generated form apply to the core; an open closure of rho(F) makes the closure of rho(N) open, and its preimage is a finite-index F-normalized subgroup of Sigma inside the core"
target: f-cores-reduce-benign-witnesses-to-normalized-ones
requires:
  - type-f-weyl-groups-have-bounded-elementary-abelian-ranks
  - commensurated-witnesses-survive-browder-but-die-when-linear
  - commensurated-quotients-coarsely-embed-in-hecke-graphs
---

Verification tier: proposed-established. Items 1, 4 and 5 are elementary.
Items 2 and 3 apply two results already in the graph to a new subgroup, the
`F`-core:
- the trivial-action Browder bound, Step 2 of
  `commensurated-witnesses-browder-survives-linear-kill-proof`, which needs
  no finite generation of homology;
- the finitely generated form, the theorem of
  `type-f-weyl-groups-have-bounded-elementary-abelian-ranks`.

The only facts about locally compact groups used below are these:
- an open subgroup of a compact group has finite index;
- a closed subgroup of finite index is open.

Throughout, `F` is free, `N ⊴ F`, `P = F/N`, `Σ ≤ Λ ⊇ F` with
`Σ ∩ F = N`, and `S = ∩_{f ∈ F} fΣf^{-1}`.

## Item 1: the core is a normalized witness

- **`F` normalizes `S`.** For `g ∈ F`,
  `gSg^{-1} = ∩_f (gf)Σ(gf)^{-1} = S`.
- **`N ≤ S`.** For `f ∈ F`, `N = fNf^{-1} ≤ fΣf^{-1}`, because `N ⊴ F` and
  `N ≤ Σ`.
- **`S ∩ F = N`.** `S ∩ F ≤ Σ ∩ F = N`, and `N ≤ S ∩ F` by the previous
  point.
- **`E = FS` and `E/S ≅ P`.** `E` is a subgroup because `F` normalizes `S`.
  `E/S ≅ F/(F ∩ S) = F/N = P`.
- **Conjugates.** `fΣf^{-1} = gΣg^{-1}` iff `g^{-1}f ∈ N_F(Σ)`. Now
  `N ≤ N_F(Σ)`, because `N ≤ Σ`. So conjugates are indexed by
  `F/N_F(Σ) = P/P_Σ`.
- **Equivalence.**
  - If `(Λ, Σ)` is `F`-normalized, then `S = Σ`.
  - Conversely, if `Λ` and `S` are of type `F_m`, then `(Λ, S)` is an
    `F`-normalized `F_m`-witness for `N`. ∎

## Item 2: Browder at the core

Let `Λ` be torsion-free and `n = cd Σ < ∞`. Then `cd S ≤ n`, since `S ≤ Σ`.

- **The action.** `E` acts on `S` by conjugation. This induces an action on
  each `H_i(S; Z)`. Inner automorphisms act trivially on homology, so the
  action factors through `E/S = P`. Let `W` be the kernel of the action on
  `⊕_{i ≥ 1} H_i(S; Z)`. It is normal in `P`.
- **The bound.** Let `A ≤ W` be elementary abelian `p`, and let `E_A ≤ E` be
  its preimage. Then `E_A` is torsion-free and `[E_A : S] = |A| < ∞`, so
  `cd E_A = cd S ≤ n` (Serre). `A = E_A/S` acts trivially on `H_{≥1}(S; Z)`.
  These are exactly the hypotheses of Step 2 of
  `commensurated-witnesses-browder-survives-linear-kill-proof`, with `Σ_Q`
  replaced by `S`. That step uses only three facts:
  - `S ⊴ E_A` with finite quotient;
  - `E_A` torsion-free with `cd E_A ≤ n`;
  - trivial action on homology.

  It uses no finiteness of `H_*(S)` and not that `S` is a `Q`-core. Hence
  `rk A ≤ 2n`.
- **Images.** For elementary abelian `A ≤ P`, the group `A ∩ W` has rank
  `≤ 2n`. So the image `A/(A ∩ W) ≤ P/W` has rank `≥ rk A - 2n`.
- **Degrees.** `H_i(S; Z) = 0` for `i > n`, so
  `P/W ↪ ∏_{i=1}^{n} Aut H_i(S; Z)`. ∎

## Item 3: infinitely generated homology of the core

Assume in addition that every `H_i(S; Z)` is finitely generated. For
elementary abelian `A ≤ P`, let `E_A ≤ E` be its preimage. Then
`S ⊴ E_A`, `E_A/S ≅ A`, and `E_A` is torsion-free. Also `cd S ≤ n < ∞`, and
`H_*(S; Z)` is finitely generated. The theorem of
`type-f-weyl-groups-have-bounded-elementary-abelian-ranks` gives
`rk_p A ≤ 2·#{i : H_i(S) ≠ 0} + Σ_i rk_p Aut H_i(S; Z)`. The right side does
not depend on `A`.

- **The listed groups.** `U`, `V`, `Z/2 ≀ Z`, Grigorchuk's group and
  `⊕_∞ Z/p` contain `(Z/p)^r` for every `r`, for a fixed `p`.
- **Conclusion.** For those `P`, some `H_i(S; Z)` with `1 ≤ i ≤ n` is not
  finitely generated. A group of type `FP_∞` has finitely generated
  homology, so `S` is not of type `FP_∞`. ∎

## Item 4: witnesses whose core has finite index

Let `Σ` be of type `F`, `Λ` torsion-free, and `Σ` commensurated by `F`.
If `[Σ : S] < ∞`, then `S` is of type `F`, being of finite index in a type
`F` group. So its homology is finitely generated, and item 3 bounds every
`rk_p A`. Also `(Λ, S)` is a type `F`, `F`-normalized witness by item 1.
It remains to show that each of
(a)–(d) gives `[Σ : S] < ∞`.

- **(a) Finitely many conjugates.** If `[P : P_Σ] = k < ∞`, then by item 1
  `S = ∩_{j=1}^{k} f_jΣf_j^{-1}` for a transversal `f_1, ..., f_k`. Each
  `Σ ∩ f_jΣf_j^{-1}` has finite index in `Σ` (commensuration). A finite
  intersection of finite-index subgroups has finite index. If `P` is
  finite, then `k ≤ |P|`.
- **(b) Open closure.** Let `C`, `ρ : C -> H`, `K` and `Σ' = ρ^{-1}(K)` be
  as stated. Put `F̂ = cl ρ(F)` and `M = F̂ ∩ K`.
  - `ρ(F) ∩ K = ρ(N)`: if `ρ(f) ∈ K`, then `f ∈ Σ' ∩ F = N`; and
    `ρ(N) ≤ K` since `N ≤ Σ'`.
  - `M = cl ρ(N)`: `K` is open, so every point of `F̂ ∩ K` is a limit of
    points of `ρ(F)` that lie in `K`, i.e. of points of `ρ(N)`. Conversely
    `cl ρ(N) ≤ F̂ ∩ K`, since `K` is closed.
  - `ρ(F)` normalizes `M`, because it normalizes `ρ(N)` and conjugation is
    a homeomorphism.
  - `F̂` open in `H` means `M` is open in `K`. `K` is compact, so
    `[K : M] < ∞`.
  - Put `Σ_0 = ρ^{-1}(M) ≤ Σ'`. The map `Σ'/Σ_0 -> K/M`, `σΣ_0 ↦ ρ(σ)M`,
    is injective. So `[Σ' : Σ_0] ≤ [K : M] < ∞`, and `Σ_0` has finite index
    in `Σ`.
  - `F` normalizes `Σ_0`, since `ρ(F)` normalizes `M`.
  - An `F`-normalized subgroup of `Σ` lies in every `fΣf^{-1}`, hence in
    `S`. So `[Σ : S] ≤ [Σ : Σ_0] < ∞`.
  - Also `Σ_0 ∩ F = N` directly: `ρ(f) ∈ M ≤ K` gives `f ∈ N`, and
    `ρ(N) ≤ M`. So `(Λ, Σ_0)` is itself a finite-index normalized
    witness.
- **(c) Schlichting completion.** Take `C = ⟨F, Σ⟩`, `G` the closure of
  the image of `C` in `Sym(C/Σ)`, `ρ : C -> G`, and `K = Stab_G(Σ)`.
  - `G` is totally disconnected locally compact, and `K` is compact open
    (`commensurated-quotients-coarsely-embed-in-hecke-graphs`, item 2).
  - `ρ^{-1}(K) = {c : cΣ = Σ} = Σ`. So (b) applies with `Σ' = Σ`.
  - **The equivalence.** With `M = cl ρ(N)` as in (b), `F̂` is open iff `M`
    is open in `K`. The Hecke closure of `N` is `Σ_0 = Σ ∩ ρ^{-1}(M)`.
    - If `M` is open, then `[Σ : Σ_0] = [K : M]`, because `ρ(Σ)` is dense
      in `K`, so `ρ(Σ)M = K`.
    - If `[Σ : Σ_0] < ∞`, then `cl ρ(Σ_0) ≤ M` has finite index in
      `K = cl ρ(Σ)`. A closed subgroup of finite index is open, so `M` is
      open.
  - **Discrete `G`.** Then `K` is finite, so every subgroup of `G` is
    open.
- **(d) Lattice type.** This is (b) with `C = Λ`, `ρ = pr_2 : Λ -> G_2`
  and `Σ' = Σ = ρ^{-1}(K)`. If `pr_2(F)` is dense in an open subgroup, its
  closure is that open subgroup. ∎

## Item 5: the surviving regime

Let `C = ⟨F, Σ⟩`, `G`, `ρ` and `K` be as in (c), with `o = Σ ∈ C/Σ`.

- **The core is a stabilizer.** `Stab_C(fo) = fΣf^{-1}`. So
  `S = {c ∈ C : c fixes F·o pointwise} = ρ^{-1}(Fix_K(F·o))`. Every such
  `c` fixes `o`, so it lies in `Σ = ρ^{-1}(K)`. Here `F·o = φ(P)` is the
  orbit of `commensurated-quotients-coarsely-embed-in-hecke-graphs`.
- **The index.** `Fix_K(F·o)` is a closed subgroup of `K`.
  - If it is open, then `[Σ : S] = [K : Fix_K(F·o)] < ∞`, by density of
    `ρ(Σ)` in `K`.
  - If `[Σ : S] < ∞`, then `cl ρ(S)` is closed of finite index in `K`,
    hence open. It lies in `Fix_K(F·o)`, because fixing a point is a closed
    condition, so the fixator is open.
  - `Fix_K(F·o)` is open iff it has finite index iff `K` acts on `F·o`
    through a finite quotient.
- **The listed conditions.**
  - The coarse gate is item 1 of the Hecke claim.
  - The rigidity condition is the previous point together with items 3
    and 4.
  - The non-open closure is (b) in contrapositive. A non-open closed
    subgroup `M` of the profinite `K` has infinite index. `K/M` is then an
    infinite compact homogeneous space with no isolated point (an isolated
    coset would make `M` open), so it is uncountable.
  - The homological conditions are items 2 and 3 applied to
    `S = Σ ∩ Fix(φ(U))`. ∎

## Sharpness

Let `Λ = BS(1,2) = ⟨a, t | tat^{-1} = a^2⟩`, `Σ = ⟨a⟩` and `F = ⟨t⟩`.

- **The witness.** `Λ` is torsion-free of type `F` (a one-relator group
  that is not a proper power; its presentation complex is aspherical). `Σ`
  is infinite cyclic. `Σ ∩ F = 1` in the HNN normal form, so `N = 1`.
- **Commensurated.**
  - `tΣt^{-1} = ⟨a^2⟩`, which has index 2.
  - `t^{-1}Σt ∋ t^{-1}at`, whose square is `a`. So `t^{-1}Σt ⊇ Σ`, with
    index 2.
- **The core.** `t^kΣt^{-k} = ⟨a^{2^k}⟩` for `k ≥ 0`, and
  `t^kΣt^{-k} ⊇ Σ` for `k < 0`. So `S = ∩_{k ≥ 0} ⟨a^{2^k}⟩ = 1`, which has
  infinite index in `Σ`.
- **The completion.** It is `Q_2 ⋊ Z` with `K = Z_2`. The closure of `F`
  is the discrete subgroup `0 ⋊ Z`, which is not open.

So the regime of item 5 is non-empty. The quotient `P = Z` is torsion-free,
so this example says nothing about `Z/2 ≀ Z`.
