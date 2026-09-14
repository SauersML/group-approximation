# sk-sofic-embedding-b: ultraproduct envelopes for sofic groups (2026-09-13)

Lane brief: `ROSTER-D.md`, start (b). Target: every finitely generated sofic group embeds in an
infinite simple Kazhdan sofic group, built from rings acting on permutation modules inside metric
ultraproducts. Everything here is unreviewed; review is queued with sk-verify-4.

## 1. What the route reaches, and where it stops

The envelope recipe that the note's theorem generalizes is: a finitely generated simple ring `R` with
local annihilation gives `EL_n(R)/Z` infinite, simple and Kazhdan for `n >= 3`, and the approximation
type of the group follows the approximation type of the ring. The two metrics separate here:

| ring model | group conclusion | available for |
|---|---|---|
| exact finite models (LEF ring) | LEF, so sofic | residually finite acting groups, Toeplitz subshifts |
| rank ultraproduct model | linear sofic | amenable acting groups, Folner truncation |
| permutation model | sofic | not available beyond the LEF case |

The third row is empty for a reason. `gap-sofic-approximations-are-local-embeddings` (reviewed PASS)
shows that for `g ∈ GL_N(F_q)` acting on `F_q^N`, the fixed-point ratio is `q^(-rank(g-1))`, so a
rank defect of rank `r >= 1` becomes a Hamming defect `1 - q^(-r) >= 1 - 1/q`. An approximate ring
model composed with any of the standard algebraic actions is a sofic approximation only if it is
exactly multiplicative, and then it witnesses LEF. So route (b) has a ceiling at linear soficity; the
Hamming metric needs models that are not algebraic.

## 2. Theorem A (amenable inputs, unconditional)

**Every finitely generated amenable group `Γ` embeds in an infinite finitely generated simple Kazhdan
`F_q`-linear sofic group.** Node `amenable-groups-embed-in-simple-kazhdan-linear-sofic`, route
`...-proof`. The four steps:

1. **Double.** `Δ = (Γ × Γ) ⋊ C_2`, and `ι(γ) = (γ, γ^(-1)) = [(γ,1), s]` embeds `Γ` in `[Δ,Δ]`.
2. **Envelope.** `X ⊆ A^Δ` a free minimal subshift (Gao--Jackson--Seward), `R = LC(X,F_q) ⋊ Δ`.
   `R` is finitely generated, and the transformation groupoid is minimal, effective, ample and
   Hausdorff, so `EL_n(R)/Z` is infinite simple Kazhdan.
3. **Linear soficity.** `Δ` amenable acting minimally gives the Folner rank model
   (`amenable-minimal-crossed-products-have-faithful-rank-models`, reviewed PASS), then
   `rank-modelled-simple-rings-give-linear-sofic-projective-el`.
4. **Embedding.** `diag(a,a^(-1),1) diag(b,b^(-1),1) diag((ab)^(-1),ab,1) = diag(1,[a^(-1),b^(-1)],1)`
   puts `diag(1, u_(ι(γ)), 1)` in `E_3(R)`, injectively and injectively modulo the centre.

The point of step 1 is that it needs no hypothesis on `Γ` at all, and it transports along any class
closed under finite direct products and index-two extensions. It replaces the Ore theorem plus
quotient-doubling used in `rf-groups-lie-in-derived-subgroups-of-rf-groups`, and it is the version
that survives for sofic, hyperlinear and LEF inputs. Node
`double-swap-embeds-group-in-derived-subgroup`.

**Firewall used throughout.** `a ↦ diag(a, a^(-1), 1)` is not a homomorphism on noncommuting units.
The displayed identity is the correct substitute and gives a single diagonal position.

## 3. Theorem B (the cost of the target)

**If every finitely generated sofic group embedded in an infinite simple Kazhdan sofic group, there
would be a sofic infinite simple Kazhdan group that is not LEF.** Node
`sofic-universal-envelope-forces-non-lef-simple-kazhdan`. LEF passes to subgroups, and `BS(2,3)` is
finitely presented, sofic and not residually finite, so not LEF by Vershik--Gordon. Since every sofic
simple Kazhdan group on this graph is LEF, the target is at least as hard as producing one non-LEF
example, and by §1 no algebraic model can produce it.

## 4. Theorem SR (sofic inputs, conditional) and the missing ingredient

Let `Δ` be sofic and act freely and minimally on a Cantor space `X` with an invariant probability
measure `μ`. Suppose the orbit relation of `Δ ↷ (X, μ)` is sofic, so that there are maps
`σ_k : Δ -> Sym(V_k)` and labellings `φ_k : V_k -> X` with `φ_k(σ_k(δ)v) = δ φ_k(v)` off a vanishing
fraction of `v`, and `(φ_k)_*(uniform) -> μ` weakly. Define

    Φ_k(f) = diag(f(φ_k(v)))_v,   Φ_k(u_δ) = P_(σ_k(δ)).

Then `Φ_k` is multiplicative up to rank `o(|V_k|)`: the relation `u_δ f u_δ^(-1) = f ∘ δ^(-1)` holds
at every `v` where the labelling is equivariant. For faithfulness, take `r = Σ_(δ ∈ F) f_δ u_δ ≠ 0`
and `δ_0` with `f_(δ_0) ≠ 0`. Freeness and compactness give a nonempty clopen `U` on which `f_(δ_0)`
is a nonzero constant with `U ∩ δ U = ∅` for `δ ∈ F^(-1)F \ {1}`. On the columns `v` with
`φ_k(v) ∈ U`, the entry of `Φ_k(r)` in row `σ_k(δ_0)v` is nonzero, and no other such column has a
nonzero entry in that row, since that would force `φ_k(v') ∈ δ^(-1)δ_0 U`, disjoint from `U`. So
`rank Φ_k(r) >= μ(U)|V_k| - o(|V_k|)`, and `μ(U) > 0` because an invariant measure of a minimal
action has full support. This is the sofic-approximation replacement for the Folner truncation.

The hypothesis that is not available is the existence of the measured system:
`sofic-groups-have-measured-free-minimal-subshifts`. For amenable `Δ` it is automatic, which is
Theorem A. This lane did not verify the Elek--Lippner statement on sofic orbit relations at source,
so Theorem SR is stated with the labelling property as an explicit hypothesis rather than derived.

## 5. Status and limits

- Established but unreviewed: the double-and-swap lemma, Theorem A, Theorem B.
- Open and landed as such: the target, and the measured free minimal subshift question.
- Not verified at source by this lane: Gao--Jackson--Seward (abstract level only, arXiv:1201.0513),
  Elek--Szabó on extensions with amenable quotient, Vershik--Gordon (used through the reviewed gap
  node), Elek--Lippner. Soficity of `BS(2,3)` is taken from the reviewed model test of
  `gap-sofic-approximations-are-local-embeddings`.
- No literature search was made for universal embedding theorems into simple Kazhdan groups; the
  novelty of Theorem A beyond Kionke--Schesler's LEF statement is therefore unchecked.
