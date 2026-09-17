---
rg: 2
id: thompson-v-finitary-structure-stabilizers-are-not-co-amenable
kind: claim
title: Stabilizers in Thompson's V of structures that V moves only at finitely many points of a mean-free V-set are not co-amenable; in particular Thompson's T is not co-amenable in V
distinct_from:
  thompson-v-amenable-actions-are-free-off-fixed-points: that kills stabilizers fixing a probability on the Cantor set, rigid covers and each confining set; T is in none of these families, and this kills T and every subgroup of it through quasi-equivariant breakpoint sets instead of fixed measures.
  thompson-v-cantor-orbits-have-no-folner-sets: that rules out Følner sets on orbits of the Cantor action itself; this transfers that halving to coset spaces whose points are only moved by finite perturbations, where no equivariant map to Cantor orbits exists.
  thompson-v-has-a-fixed-point-free-amenable-action: that open claim asks for some mean-free amenable V-set; this refutes the test candidate V/T proposed for it and removes a whole class of candidate stabilizers, but does not refute the claim.
  braided-v-kernel-elements-have-equivariant-breakpoint-sets: that uses breakpoint sets moved by conjugation through T to control centralizers in braided V; this uses the breakpoint set of a coset of T as a quasi-equivariant finite set to transfer invariant means.
artifacts:
  - research/thompson-v-finitary-structure-stabilizers-not-co-amenable-proof.md
---

**ESTABLISHED** by `thompson-v-finitary-structure-stabilizers-not-co-amenable-proof` (unreviewed).

**Setting.** `V = G_(2,1)` acts on `C = {0,1}^N`. A *mean* on a set `X` is a finitely additive probability on all
subsets of `X`. `P_f(Q)` is the set of finite subsets of `Q`.

**Theorem A (transfer).** Let a group `G` act on a set `Ω` with an invariant mean `m`, and on a set `Q` with no
invariant mean. Let `D : Ω -> P_f(Q)` be *quasi-equivariant*: for each `g ∈ G` there is `c_g` with
`|D(gω) Δ gD(ω)| <= c_g` for all `ω`. Then `m({ω : |D(ω)| <= N}) > 0` for some `N`.

**Theorem B (finitary structures).** Let `Q` be a countable `V`-set with no `V`-invariant mean. For example `Q`
is any countable `V`-invariant subset of `C`, or `Q = V/K` for any non-co-amenable `K`. Let `Σ` be a `V`-set
with a *disagreement map* `Δ : Σ × Σ -> P(Q)` that is symmetric, satisfies `Δ(σ,ρ) ⊆ Δ(σ,τ) ∪ Δ(τ,ρ)`, and
is equivariant: `Δ(gσ,gτ) = gΔ(σ,τ)`. Let `σ ∈ Σ` be *finitary with unbounded defect*: `Δ(gσ,σ)` is finite for
every `g`, and `sup_g |Δ(gσ,σ)| = ∞`. Then:
1. the orbit `Vσ ≅ V/Stab(σ)` has no invariant mean, so `Stab(σ)` and every subgroup of every conjugate of it
   is not co-amenable in `V`, and `φ_S(V/H) > 0` for all these `H`;
2. for every `V`-set `Ω` with invariant mean `m`, the set `{x : Stab(x) ≤ Stab(gσ) for some g}` is `m`-null.

The typical instance is `Σ = X^Q`, or the set of maps `Q -> Q`, with `Δ` the set of points where two maps differ.

**Corollary (Thompson's T).** Let `Q ⊆ C` be the union of the tail classes of `0^∞` and `1^∞`. Let `σ` be the
involution of `Q` that swaps `w01^∞` with `w10^∞` for every finite word `w`, and swaps `0^∞` with `1^∞`. Then
`T ≤ Stab_V(σ)`, and in fact equality holds. Hence `T` is not co-amenable in `V`, `φ_S(V/T) > 0`, and the same
holds for `F` and for every subgroup of every conjugate of `T`. For every invariant mean on a `V`-set,
the points whose stabilizer lies in a conjugate of `T` form a null set.

**Why T needed a new argument.** `T` fixes no probability on `C`, contains no `V_U` and preserves no finite
clopen partition. So items 4 and 5 of `thompson-v-amenable-actions-are-free-off-fixed-points` do not apply to it,
and this proof does not use confinement. The new object is the *breakpoint set* `D(gT)`: the finite set where
the circle structure `gσg^(-1)` differs from `σ`. It is quasi-equivariant, so an invariant mean on `V/T` would
average the uniform measures on breakpoint sets into an invariant mean on `Q`. The halving map rules that out.

**Consequence for the target.** The route "`T` co-amenable in `V` ⇒ `V` sofic ⇒ `V` surjunctive" is dead at
its first step. The chain itself is sound: a proper co-amenable subgroup gives item 1(a) of
`thompson-v-amenable-actions-are-free-off-fixed-points`, hence soficity, and Gromov–Weiss gives surjunctivity.
A witness for `thompson-v-has-a-fixed-point-free-amenable-action` must now have almost every stabilizer outside
the downward closure of the finitary-structure stabilizers. The class is closed under iteration: once `K` is
known to be non-co-amenable, finitary structures over `Q = V/K` give more null stabilizers.

**Not proved here.** No uniform lower bound on `φ_S(V/H)` over the whole class is given. Theorem B needs unbounded
defect. It says nothing when `|Δ(gσ,σ)|` is bounded on the orbit.
