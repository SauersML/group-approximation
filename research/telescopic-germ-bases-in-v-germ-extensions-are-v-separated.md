---
rg: 2
id: telescopic-germ-bases-in-v-germ-extensions-are-v-separated
kind: claim
title: Telescopes (a group acting on every annulus around a point through the orbit of one endomorphism) have germ group (P/K_∞)*σ; inside a finite germ extension of V a faithful telescopic germ base is exactly a dynamically V-separated group, and a self-simulating finite germ extension of V simulates only subgroups of V
distinct_from:
  dynamically-v-separated-groups-satisfy-boone-higman: that is the sufficiency direction (a finitely presented dynamically V-separated group gives a finitely presented host); this is the converse (every faithful telescope inside ANY finite germ extension of V has a dynamically V-separated base), the germ calculus for general seeds and non-injective data, and the self-simulation corollary.
  f-infinity-tail-ascending-hnns-satisfy-boone-higman: that realizes last-section ascending HNN extensions; here the telescope operator is defined for an arbitrary seed action, and the result is a characterization and an obstruction, not a construction.
  fw-window-zero-shells-are-self-similar-actions: that is the discrete (countable-set) shadow; a telescope is its Cantor version, in which each annulus carries a whole copy of the seed action rather than finitely many points.
  rank-one-cone-hosts-put-fw-groups-in-local-map-groups: that localizes FW subgroups of rank-one hosts into local-map groups; this shows the graded (annulus-preserving) part of any germ at one point of a finite germ extension of V is an ascending HNN extension over a dynamically V-separated base, which for simple or FW inputs forces the input into V.
---

**ESTABLISHED** by `telescopic-germ-bases-dynamically-v-separated-proof` (lane proof, elementary;
the only import is that `V` has the Haagerup property, Farley, recalled, used in item 4. Not
reviewed; no priority claimed).

**The telescope operator.** Let `C = {0,1}^ω`, `p₀ = 0^∞`, `A_n = 0^n 1 C` and `α_n(w) = 0^n 1 w`, so
`C = {p₀} ⊔ ⨆_{n≥0} A_n`. For a group `P`, an endomorphism `σ` of `P` and a *seed*
`ρ: P → Homeo(C)`, define `T(p) = T_{ρ,σ}(p)` to fix `p₀` and to act on `A_n` by
`α_n ∘ ρ(σ^n(p)) ∘ α_n^{-1}`. The zoom element `x₀ ∈ V` satisfies `x₀ α_n = α_{n+1}` for `n ≥ 1`.

**Theorem.**
1. *(Calculus.)* `T: P → Homeo(C)` is a homomorphism with `ker T = ⋂_n (σ^n)^{-1}(ker ρ)`. Near
   `p₀`, `x₀^{-1} T(p) x₀ = T(σ(p))`. The germ of `T(p)` at `p₀` is trivial exactly when `p ∈ K_∞`,
   where `K_∞ = ⋃_N ⋂_{n≥N} (σ^n)^{-1}(ker ρ)`. `σ` induces an injective endomorphism `σ̄` of
   `P̄ = P/K_∞`. If `ρ(P) ≤ V`, the germ group of `⟨V, T(P)⟩` at `p₀` is the ascending HNN
   extension `P̄ *_{σ̄}`, with stable letter the germ of `x₀`.
2. *(Singular sets.)* The `V`-singular set of `T(p)` is `⋃_n α_n(Sing ρ(σ^n p))`, together with `p₀`
   when `p ∉ K_∞`.
3. *(Necessity of dynamical separation.)* Let `H` be a finite germ extension of `V`, i.e. every
   element is locally in `V` off finitely many points. Suppose `T_{ρ,σ}(P) ≤ H` for some
   `ρ: P → Homeo(C)`. Then for every `p` there is `N` with `ρ(σ^n p) ∈ V` for all `n ≥ N`. If `P`
   is finitely generated and the germ map is faithful (`K_∞ = 1`, e.g. `σ` injective and `ρ`
   faithful), then for some `N` the triple `(P, σ, ρ∘σ^N)` is dynamically V-separated. With
   `dynamically-v-separated-groups-satisfy-boone-higman` this gives: *a finitely presented group
   with an injective endomorphism is a faithful telescopic germ base of a finitely presented
   finite germ extension of `V` if and only if it is dynamically V-separated.*
4. *(Self-simulation dissolves into V.)* Call `H ≥ V` **self-simulating** along an endomorphism `σ`
   of `H` if `T_{ι,σ}(H) ⊆ H`, where `ι` is the inclusion (the host is its own seed, at every
   scale). If `H` is a finite germ extension of `V` and self-simulating, then for each `h ∈ H`
   one has `σ^n(h) ∈ V` for all large `n`. Every finitely generated `P ≤ H` with `σ(P) ≤ P` and
   `σ|_P` injective embeds in `V`, via `σ^N`. In particular `P` is finite if it is infinite FW
   or Kazhdan, and `P` is a subgroup of `V` if it is simple.
5. *(Simple inputs never climb.)* If `P` is simple and `T_{ρ,σ}(P)` has nontrivial germ at `p₀`, then
   `ρ∘σ^n` is injective for some `n`. So a telescope never transports a simple group into a host
   whose seed does not already contain it.

**Calibrations.**
- **Grigorchuk.** With `b = (a,c)`, `c = (a,d)`, `d = (1,b)` along the spine `1^∞`, `⟨b,c,d⟩ = (Z/2)²` is
  the telescope of the seed `ρ(b) = ρ(c) = a`, `ρ(d) = 1` along the order-3 automorphism
  `σ: b ↦ c ↦ d ↦ b` (chart with the roles of 0 and 1 exchanged). Here `K_∞ = 1`, so the germ group
  of Röver's group `⟨V, b, c, d⟩` at the spine contains `(Z/2)² ⋊_σ Z`. Directed parts of bounded
  automata are telescopes with finite seeds along periodic `σ`.
- **Annular hosts.** bh-free-22's annular and dynamically-V-separated hosts are telescopes with
  seeds in `V`, and bh-free-20's last-section hosts are telescopes with seeds in `V_d S`.
- **Divisibility.** The germ base is the direct limit `lim(P̄, σ̄)`. For example `P = Z`, `σ = ×2`
  gives `Z[1/2]`. One endomorphism therefore yields `Z[1/m]`-type divisibility and never `Q`, which
  is the telescope form of prime locality.

**Lesson for general BH.** A telescope is the canonical cross-depth rule: it is the germ-level
self-similarity that makes Thompson-like hosts finitely presented. Inside finite germ extensions
of `V` it can only carry dynamically V-separated data, and self-simulation of the host collapses
into `V`. So finite germ extensions (singular sets finite per element) can never simulate
themselves nontrivially. A genuinely self-simulating host must have infinite, hierarchical
singular sets per element; see `telescope-fixed-points-are-singular-on-a-parse-shift`. Telescopes
are also a finiteness engine, not an embedding engine: they transport ascending-HNN,
direct-limit and residual structure upward, but never a simple input the seed lacks.
