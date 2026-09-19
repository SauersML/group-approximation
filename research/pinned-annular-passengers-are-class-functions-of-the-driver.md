---
rg: 2
id: pinned-annular-passengers-are-class-functions-of-the-driver
kind: claim
title: In a pinned one-point annular host over V, the passenger's depth-n data are fixed by every automorphism of V fixing the driver's depth-n data; so the pinned quotient depends only on the Aut(V)-class of the driver datum, and inner, Aut(V)-induced, cone-copy and faithful diagonal drivers pin only bounded or ascending passengers
distinct_from:
  fp-annular-germ-groups-are-hnn-recursive: that gives the HNN shape of every fp annular germ group; this constrains which drivers can pin a passenger inside that shape.
  telescopic-germ-bases-in-v-germ-extensions-are-v-separated: that characterizes the ascending (telescope) case; this shows several natural non-ascending driver designs fall back into it or into bounded quotients.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed).

**Setting** (the passenger design of `fp-rf-groups-embed-in-hnn-recursive-annular-germ-groups`).
- An fp driver `M = ⟨m_1..m_k⟩` with injective endomorphism `μ` and a homomorphism `ρ: M → V`. The
  driver datum at depth `n` is the tuple `c_n = (ρμ^n(m_1), …, ρμ^n(m_k)) ∈ V^k`; it generates
  `Γ_n := ρμ^n(M)`, and `Γ_{n+1} ⊆ Γ_n`.
- A passenger `G = ⟨g_1..g_l⟩` with depth data `x_n = (r_n(g_1), …, r_n(g_l)) ∈ V^l`, where
  `r_n: G → Q_n ≅ G/N_n` runs through a residual chain `(N_n)`.
- A finite pinning system `R(x; c) = 1` of words, with **pinning**: for every `n ≥ n_0`, `x_n` is the
  unique tuple in `V^l` with `R(x_n; c_n) = 1`.
- `Aut(V) = N_{Homeo(C)}(V)` (Rubin), acting on tuples coordinatewise.

**Theorem.**
1. **Galois confinement.** Every `α ∈ Aut(V)` with `α(c_n) = c_n` satisfies `α(x_n) = x_n`. In
   particular `Q_n ≤ C_V(C_{Aut(V)}(Γ_n))`: the passenger commutes with everything that centralizes
   the driver's depth-`n` group.
2. **Class function.** If `α(c_n) = c_{n'}` for some `α ∈ Aut(V)`, then `α(x_n) = x_{n'}`, and `α`
   is an isomorphism of marked groups `Q_n → Q_{n'}`. Hence `N_n = N_{n'}`.
3. **Growth needs an infinite driver orbit.** Depths with different `N_n` have driver data in
   different `Aut(V)`-classes. So if the chain is strictly decreasing, the `μ*`-orbit of `[ρ]` in
   `Hom(M,V)/Aut(V)` (where `μ*ρ = ρ∘μ`) is infinite from `n_0` on.
4. **Dead driver families.** A germ `ĝ = (x_n)` is faithful only if `⋂ N_n = 1`, and for an infinite `G` that needs
   infinitely many distinct `N_n`. The following drivers therefore pin only finite passengers
   (a, b) or only ascending ones, `G ≤ M̂` (c).
   - **(a) Aut(V)-induced drivers.** `ρ∘μ = ι_h∘ρ` for some `h ∈ Aut(V)`. This covers `μ` inner in
     `M`, and the machine candidate "`μ = conj(R)` with `R ∈ V`" whenever it acts on all of `M`.
     Here `c_n = h^n c_0 h^{-n}`, so all `N_n` agree by 2.
   - **(b) Cone-copy drivers.** `ρ(M) ≤ V` and `ρμ = κ∘ρ`, where `κ` copies `V` onto the cone `1C`.
     For `n ≥ 1`, a prefix replacement `h ∈ V` taking `1^nC` onto `1^{n+1}C` conjugates `c_n` to `c_{n+1}`.
   - **(c) Passenger inside a faithful driver.** Suppose `x_n ∈ Γ_n^l` for infinitely many `n`, and `ρμ^n`
     is injective there. Then `x_n = ρμ^n(y)` for one fixed `y ∈ M^l`, so `Ĝ ≤ M̂` (the ascending
     case). This applies to the faithful diagonal driver `M = V`, `ρ = id`,
     `μ = Δ: g ↦ (g on 0C, g on 1C)`: there `C_{Aut(V)}(Γ_n) ⊇ Sym` (level-`n` block permutations) and
     `C_V(Sym) = Δ^n(V) = Γ_n`, so part 1 already forces `x_n ∈ Γ_n`. Such passengers lie in `V`.

**Proof.**
1. `R(α x_n; c_n) = α(R(x_n; c_n)) = 1`, since `α` is a group automorphism fixing `c_n`. Uniqueness
   gives `α x_n = x_n`. Inner automorphisms fixing `c_n` are conjugations by `C_V(Γ_n)`.
2. `R(α x_n; c_{n'}) = α(R(x_n; c_n)) = 1`, and uniqueness at `n'` gives `α x_n = x_{n'}`. `α`
   carries the marked group `⟨x_n⟩` onto `⟨x_{n'}⟩` and generator to generator. So `r_n` and `r_{n'}`
   have the same kernel.
3. Immediate from 2.
4. (a) and (b) are immediate from 2. For the prefix-replacement claim in (b): `V` acts transitively on
   pairs of proper clopen sets. So there is `h ∈ V` that is the prefix map `1^nξ ↦ 1^{n+1}ξ` on
   `1^nC` and any `V`-element from the complement onto the complement. Then
   `h κ^n(g) h^{-1} = κ^{n+1}(g)`.
   For (c), write `x_n = ρμ^n(y_n)`. Then `ρμ^n(R(y_n; m)) = R(x_n; c_n) = 1`, and injectivity gives
   `R(y_n; m) = 1` in `M`. So for any other such depth `n'`, `ρμ^n(y_{n'})` also solves the depth-`n`
   system, and uniqueness plus injectivity give `y_{n'} = y_n =: y`.
   For the diagonal driver, let `h` commute with all level-`n` block permutations, with `2^n ≥ 3`.
   The block stabilizer `S_w` fixes exactly block `w`, so `h` preserves each block. Commuting with
   block transpositions makes `h` act identically on every block, so `h = Δ^n(g)`, and `h ∈ V`
   forces `g ∈ V`.

## Lesson for general BH

Pinning is a **definability** statement, and definable data obey Galois symmetry. A passenger pinned
by the driver can only encode information that is invariant under the driver's symmetries in
`Aut(V)`, and it can only grow if the driver's depth data run through infinitely many `Aut(V)`-types.
The natural drivers are self-similar in `Aut(V)`: conjugations, reversible machines acting as
conjugations, cone copies, and diagonal doubling. They all have bounded type, or they trap the
passenger inside themselves (the ascending case). So a non-ascending pinned host needs a driver whose
depth-`n` representations `ρ∘μ^n ∈ Hom(M,V)` are pairwise non-conjugate under `Aut(V)`, while its
depth groups `Γ_n` still have small double centralizers. Either `ρ` is non-faithful with varying
kernels, or the types grow genuinely. That is the precise sense in which the compiler has to be a
machine and not a symmetry.
