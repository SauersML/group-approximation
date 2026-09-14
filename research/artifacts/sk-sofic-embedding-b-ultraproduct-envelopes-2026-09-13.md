# sk-sofic-embedding-b: ultraproduct envelopes for sofic groups (2026-09-13)

Lane brief: `ROSTER-D.md`, start (b). The target is that every finitely generated sofic group embeds
in an infinite simple Kazhdan sofic group, built from rings acting on permutation modules inside
metric ultraproducts.

**CORRECTION (2026-09-13, after sk-verify-4 FAIL).** The first version of this artifact
(5deaad2389) claimed that `ι(γ) = (γ, γ^(-1))` embeds every group `Γ` in the derived subgroup of
`Δ = (Γ × Γ) ⋊ C_2`. That is false for nonabelian `Γ`:
- `ι(γ)ι(δ) = (γδ, γ^(-1)δ^(-1))`, while `ι(γδ) = (γδ, δ^(-1)γ^(-1))`.
- The `Γ^op` variant only produces the diagonal, whose image in `Δ^ab = Γ^ab × C_2` is `2γ̄`.

So Theorem A below is NOT established for general amenable groups. §2 records what survives.

## 1. What the route reaches, and where it stops

The envelope recipe that the note's theorem generalizes: take a finitely generated simple ring `R`
with local annihilation. Then `EL_n(R)/Z` is infinite, simple and Kazhdan for `n >= 3`, and the
group's approximation type follows the ring's. The two metrics separate:

| ring model | group conclusion | available for |
|---|---|---|
| exact finite models (LEF ring) | LEF, so sofic | residually finite acting groups, Toeplitz subshifts |
| rank ultraproduct model | linear sofic | amenable acting groups, Folner truncation |
| permutation model | sofic | not available beyond the LEF case |

The third row is empty for a reason. By `gap-sofic-approximations-are-local-embeddings` (reviewed
PASS), for `g ∈ GL_N(F_q)` acting on `F_q^N` the fixed-point ratio is `q^(-rank(g-1))`. So a rank
defect of rank `r >= 1` becomes a Hamming defect `1 - q^(-r) >= 1 - 1/q`. An approximate ring model,
composed with any of the standard algebraic actions, is a sofic approximation only when exactly
multiplicative, and then it witnesses LEF. Route (b) therefore stops at linear soficity; the
Hamming metric needs non-algebraic models.

## 2. Embedding step: what survives

**Correct embedding lemma** (sk-sofic-embedding-a, `perfect-groups-embed-in-crossed-product-elementary-groups`).
For `R = LC(X,k) ⋊ Δ`:
- `γ ↦ diag(u_γ,1,1)` is an injective homomorphism `Δ -> GL_3(R)`;
- it lands in `EL_3(R)` on `[Δ,Δ]`, through
  `diag(u_[α,β],1,1) = diag(u_α,u_α^(-1),1) diag(u_β,u_β^(-1),1) diag((u_β u_α)^(-1),u_β u_α,1)`;
- the class of `u_γ` in `K_1(R)` is the exact obstruction.

**Theorem A, perfect case** (established, sk-sofic-embedding-a,
`amenable-perfect-groups-embed-in-kazhdan-linear-sofic`). Every finitely generated perfect amenable
group embeds in an infinite simple Kazhdan `F_2`-linear sofic group. The steps are:
- a free minimal subshift over `Γ` itself;
- the Folner rank model (`amenable-minimal-crossed-products-have-faithful-rank-models`, reviewed PASS);
- `rank-modelled-simple-rings-give-linear-sofic-projective-el`.

This covers `[[T]]'` of minimal `Z`-subshifts, which are not residually finite.

**Theorem A for non-perfect amenable groups: open.** It needs a finitely generated perfect amenable
overgroup, or a class-level `Γ ⊆ [Δ,Δ]` construction preserving amenability.
- The swap double fails (above).
- Wreath products keep the abelianization of the base (`wreath-products-keep-the-abelianization-of-the-base`).
- Ore's route needs residual finiteness.

The node `amenable-groups-embed-in-simple-kazhdan-linear-sofic` is demoted by sk-verify-4.

## 3. Theorem B (the cost of the target; reviewed PASS)

**If every finitely generated sofic group embedded in an infinite simple Kazhdan sofic group, there
would be a sofic infinite simple Kazhdan group that is not LEF.** Node
`sofic-universal-envelope-forces-non-lef-simple-kazhdan`. The argument does not use the false lemma:
- LEF passes to subgroups;
- `BS(2,3)` is finitely presented, sofic and not residually finite, so it is not LEF (Vershik--Gordon).

Every sofic simple Kazhdan group on this graph is LEF. So the target is at least as hard as producing
one non-LEF example, and by §1 no algebraic model can produce it.

## 4. Theorem SR (sofic acting groups, conditional)

Let `Δ` be sofic and act freely and minimally on a Cantor space `X`, with an invariant probability
measure `μ`. Suppose there are maps `σ_k : Δ -> Sym(V_k)` and labellings `φ_k : V_k -> X` with
`φ_k(σ_k(δ)v) = δ φ_k(v)` off a vanishing fraction of `v`, and `(φ_k)_*(uniform) -> μ`. Put

    Φ_k(f) = diag(f(φ_k(v)))_v,   Φ_k(u_δ) = P_(σ_k(δ)).

**Multiplicativity.** `Φ_k` is multiplicative up to rank `o(|V_k|)`, because
`u_δ f u_δ^(-1) = f ∘ δ^(-1)` holds at every `v` where the labelling is equivariant.

**Faithfulness.**
- Take `r = Σ_(δ∈F) f_δ u_δ ≠ 0` and `δ_0` with `f_(δ_0) ≠ 0`.
- Choose a nonempty clopen `U` on which `f_(δ_0)` is a nonzero constant and `U ∩ δU = ∅` for
  `δ ∈ F^(-1)F \ {1}`.
- The columns `v` with `φ_k(v) ∈ U` give `rank Φ_k(r) >= μ(U)|V_k| - o(|V_k|)`.
- `μ(U) > 0` because an invariant measure of a minimal action has full support.

This replaces the Folner truncation for non-amenable `Δ`. With the correct embedding lemma of §2, it
would embed finitely generated perfect sofic groups `Δ` in simple Kazhdan linear sofic groups,
provided the measured system exists. That input is `sofic-groups-have-measured-free-minimal-subshifts`
(open). This lane did not verify the Elek--Lippner statement at source, so SR keeps the labelling
property as an explicit hypothesis.

## 5. Status and limits
- **FAIL, demoted by sk-verify-4:** `double-swap-embeds-group-in-derived-subgroup`, and through it
  the route of `amenable-groups-embed-in-simple-kazhdan-linear-sofic`.
- **PASS:** `sofic-universal-envelope-forces-non-lef-simple-kazhdan`.
- **Open, with attempts:**
  - the target `sofic-groups-embed-in-simple-kazhdan-sofic-groups`;
  - `sofic-groups-have-measured-free-minimal-subshifts`.
- **Not verified at source by this lane:** Gao--Jackson--Seward (abstract level, arXiv:1201.0513),
  Elek--Lippner.
