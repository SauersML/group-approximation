---
rg: 2
id: out-free-extension-pushed-into-the-boundary-full-group
kind: claim
title: Pushed into the full group of the free-group boundary shift, Aut(F_n) → Out(F_n) becomes a finitely presented extension of Out(F_n) by a centerless group; it splits over a finite-index subgroup iff that subgroup acts on ∂F_n by piecewise representatives, and in rank 2g such an action moves the surface-word periodic point with infinite orbit
requires:
  - abelian-subgroups-of-out-free-virtually-lift-to-aut
distinct_from:
  out-free-groups-virtually-embed-in-aut-free-groups: that asks for a finite-index subgroup of Out(F_n) inside some Aut(F_m); this replaces the kernel F_n by the full group M of the boundary groupoid, where a lift needs only to be piecewise a representative, and shows a virtual section is the one-piece case.
  aut-free-to-out-free-does-not-virtually-split-in-even-rank: that is the open non-splitting of Aut(F_2g) → Out(F_2g) itself; this proves a weaker, unconditional constraint that every piecewise lift (hence every virtual section) must satisfy in rank 2g, from the Euler class of the boundary capping extension.
  fox-rational-section-fails-class-two-virtually: that obstructs lifts through the nilpotent quotient F_n/γ_3; the pushout here does not factor through any nilpotent quotient, so that computation does not apply to piecewise lifts.
---

**ESTABLISHED** (lane proof, bh-outfn-2, 2026-09-18; elementary from the cited inputs;
not reviewed; no priority claimed). Inputs:
- Matui, arXiv:1210.5800 (J. reine angew. Math. 705, 2015), Theorem `finite`: the full
  group of the groupoid of a one-sided irreducible shift of finite type is of type F_∞.
  The TeX was read on MSI at line 3245.
- Grossman (J. London Math. Soc. 1974): an automorphism of a free group that sends every
  element to a conjugate is inner.
- McCool / Culler–Vogtmann: Out(F_n) is finitely presented.
- Standard surface topology (Farb–Margalit, *Primer*: the capping sequence, Dehn–Nielsen–Baer
  with boundary, and the Birman sequence for a boundary component). Recalled, not re-read.

## Setting

Let `n ≥ 2`.
- `∂F_n` is the space of infinite reduced words. It is the one-sided SFT `X_A`, where `A`
  is the `2n × 2n` matrix on the letters `x_i^{±1}` with `A(a,b) = 1` iff `b ≠ a^{-1}`.
  `A` is irreducible and not a permutation matrix.
- `𝒢_n := F_n ⋉ ∂F_n`. It is isomorphic to the SFT groupoid `G_A`, via
  `(g, η) ↦ (gη, |g| − 2j, η)`, where `j` is the number of letters cancelled in `g·η`.
  - Inverse: given `σ^k ξ = σ^l η`, put `g = ξ_1⋯ξ_k (η_1⋯η_l)^{-1}`. This element does
    not change when `(k,l) → (k+1,l+1)`.
  - Injectivity: if `gη = g'η` with equal lags, then `g^{-1}g' ∈ Stab(η)`, which is trivial
    or `⟨r⟩`, and a nonzero power of `r` has nonzero lag.
- `M := [[𝒢_n]] ≤ Homeo(∂F_n)`: the homeomorphisms that are piecewise left translations
  `ξ ↦ uξ` on a finite clopen partition.
- `Aut(F_n)` acts on `∂F_n` by boundary maps `Φ̂`, and `Φ̂(uξ) = Φ(u)Φ̂(ξ)`.
- For `q ∈ Out(F_n)`, write `q̂ M` for the coset `Φ̂M`, `Φ ∈ q`. It is well defined by
  item 1.

## Statement

1. **Intersection.** `Aut(F_n) ∩ M = Inn(F_n)`, where `c_u` acts as the global translation
   `ξ ↦ uξ`.
2. **The pushed extension.** `H := ⟨M, Aut(F_n)⟩ = M·Aut(F_n)` and `H/M ≅ Out(F_n)`. `H` is
   finitely presented. `M` has trivial center, and its centralizer in `Homeo(∂F_n)` is
   trivial.
3. **Splitting criterion.** For `Γ ≤ Out(F_n)` the following are equivalent:
   - (a) `H → Out(F_n)` splits over `Γ`;
   - (b) **(PR)** there is a homomorphism `q ↦ h_q`, `Γ → Homeo(∂F_n)`, with `h_q ∈ q̂M`
     for all `q`.

   Concretely, (b) says each `h_q` is piecewise, on a finite clopen partition, the boundary
   map of a representative of `q`, since `u·Φ̂ = (c_uΦ)^`. Any such `h` is injective.
4. **Virtual sections are the one-piece case.** A section `s` of `Aut(F_n) → Out(F_n)` over
   `Γ` gives (PR) with `h_q = s(q)^`. Every abelian subgroup of `Out(F_n)` satisfies (PR)
   virtually (by `abelian-subgroups-of-out-free-virtually-lift-to-aut`). So no test on
   commuting pairs can refute (PR).
5. **Germs.** For `h ∈ H` and `ξ ∈ ∂F_n` there is a unique `Ψ ∈ Aut(F_n)` with `h = Ψ̂` on a
   neighborhood of `ξ`. Composition of germs is composition of these automorphisms. If
   `h ∈ q̂M` then `Ψ ∈ q`.
6. **Euler constraint (rank `2g ≥ 4`).** Let `w = [x_1,x_2]⋯[x_{2g−1},x_{2g}]`. Let `h` be a
   (PR) action of a finite-index `Γ ≤ Out(F_{2g})`, and let `Γ_w = Γ ∩ Out(F_{2g})_{[w]}`
   (fixing the oriented conjugacy class). Then the `h(Γ_w)`-orbit of `w^∞` is infinite. The
   same holds for every point of the tail class `F_{2g}·w^∞`. In particular, a virtual
   section can never fix `w^∞` on a finite-index subgroup of `Γ_w`.

## Proof

**Two facts about boundary points.**
- For `a ≠ 1`, `a^∞ := lim a^k`, `Φ̂(a^∞) = Φ(a)^∞` and `u·a^∞ = (uau^{-1})^∞`.
- If `a`, `b` are not proper powers and `a^∞ = b^∞`, then `a = b`: both lie in `Stab(a^∞)`,
  a maximal cyclic `⟨r⟩`, so `a, b ∈ {r, r^{-1}}`, and the attracting ends agree.

**(G) An automorphism `Θ` with `Θ̂ = id` on an open set is trivial.**
- Take a cylinder `[v]` inside the open set. For each `i`, choose the sign `ε_i` such that
  `x_i^{ε_i}` is not the inverse of the last letter of `v`.
- Then `v·(x_i^{ε_i})^∞` is a reduced infinite word in `[v]`. It is the attracting point of
  the root-free element `v x_i^{ε_i} v^{-1}`.
- `Θ̂` fixes that point, so `Θ` fixes `v x_i^{ε_i} v^{-1}` by the two facts.
- Hence `Θ` fixes `vF_nv^{-1} = F_n`.

**Item 1.**
- `c_u` acts as `ξ ↦ uξ`, so `Inn(F_n) ⊆ M`.
- Conversely, let `Φ̂ ∈ M`, equal to `ξ ↦ u_iξ` on the pieces `U_i`, and let `w` be root-free.
  Then `w^∞ ∈ U_i` for some `i`, and `Φ(w)^∞ = Φ̂(w^∞) = u_i w^∞ = (u_iwu_i^{-1})^∞`. So
  `Φ(w) = u_iwu_i^{-1}`.
- Powers follow, so `Φ` maps every element to a conjugate, and `Φ` is inner by Grossman.

**Item 2.**
- `Φ̂ ∘ (ξ ↦ uξ on U) ∘ Φ̂^{-1} = (ξ ↦ Φ(u)ξ on Φ̂(U))`, so `Aut(F_n)` normalizes `M`. Hence
  `H = M·Aut(F_n)`, and `H/M ≅ Aut(F_n)/(Aut(F_n) ∩ M) = Out(F_n)` by item 1.
- `M` is finitely presented by Matui (through `𝒢_n ≅ G_A`) and `Out(F_n)` is finitely
  presented, so the extension `H` is finitely presented.
- Centralizer: let `z ≠ 1` in `Homeo(∂F_n)`. Choose `ξ` with `zξ ≠ ξ` and a clopen `U ∋ ξ`
  with `zU ∩ U = ∅`. `M` contains an element `g` supported in `U` and moving `ξ`. Take disjoint
  cylinders `[a] ∋ ξ` and `[b]` in `U` whose words end in the same letter. Then `ba^{-1}`
  maps `[a]` onto `[b]`, and `g` swaps them by `ba^{-1}` and `ab^{-1}`. Then
  `zgz^{-1}` is supported in `zU`, so `zgz^{-1} ≠ g`.

**Item 3.**
- The cosets of `M` in `H` are the classes `q̂M`, so a section of `H → Out(F_n)` over `Γ` is
  exactly a homomorphism with `h_q ∈ q̂M`.
- Distinct `q` give distinct cosets, so `h` is injective.

**Item 4.** Immediate. For abelian `A`, a virtual lift `s: A_0 → Aut(F_n)` gives
`h = ŝ` on `A_0`.

**Item 5.**
- Near `ξ`, `h = m·Φ̂` with `m ∈ M` and `Φ ∈ q`. Shrinking the neighborhood, `m` is a single
  translation `u`, so `h = (c_uΦ)^` there, and `c_uΦ ∈ q`.
- Uniqueness is (G) applied to the quotient of two such automorphisms.

**Item 6.**
- Suppose the orbit of `w^∞` under `h(Γ_w)` is finite, and let `L ≤ Γ_w` be its stabilizer,
  of finite index. For `q ∈ L` let `Ψ_q` be the automorphism of item 5 at `w^∞`.
  - Since `h_{q'}` fixes `w^∞`, germs compose, and `q ↦ Ψ_q` is a homomorphism.
  - `Ψ_q ∈ q`, and `Ψ_q(w)^∞ = w^∞`, so `Ψ_q(w) = w`, since `w` is root-free.
  - So `L` splits the extension `1 → ⟨c_w⟩ → Aut(F_{2g}, w) → Out(F_{2g})_{[w]} → 1`, whose
    kernel is `⟨c_w⟩` because the centralizer of `w` is `⟨w⟩`.
- By Dehn–Nielsen–Baer for one boundary component, this is the capping sequence
  `1 → ⟨T_∂⟩ → Mod(S_g^1) → Mod(S_{g,*}) → 1`.
- `L` has finite index in `Mod(S_{g,*})`, so it meets the point-pushing subgroup `π_1(S_g)`
  in `π_1(S')` for a finite cover `S' → S_g` of some degree `d`. Over `π_1(S_g)` the
  extension is `π_1(UT S_g)` (the Birman sequence for a boundary component). Over `π_1(S')`
  it is `π_1(UT S')`, with Euler number `χ(S') = d(2 − 2g) ≠ 0`.
- A central extension of a closed surface group by `Z` splits only if its Euler number is 0.
  This is a contradiction.
- For another point `u·w^∞` of the tail class, conjugate by the translation `u`, which
  lies in `M`. `∎`

**Scope.**
- `n = 2` is consistent: `Out(F_2) = GL_2(Z)` is virtually free, so (PR) holds, and `g = 1`
  gives Euler number 0.
- Odd rank: the nonorientable boundary word `x_1^2⋯x_n^2` gives the same splitting
  requirement. The rational class of its capping extension was not examined, and it may
  vanish.

## Lesson for general BH

Outer groups are bands, not subgroups. Out(F_n) appears in every natural construction as a
quotient of a stabilizer by its inner part: splitting stabilizers, point pushing, and here
the fp group `H` over the boundary full group. A host must therefore **strictify** the band
`F_n → Aut(F_n) → Out(F_n)`: make Out act honestly on a compact model of the F_n-groupoid.

- **The non-compact model is always strict.** `Aut(F_n)` acting on `∂F_n × Out(F_n)` has
  Out acting by translation on the second factor. So compactness is the entire difficulty.
- **Pushouts into a host where Aut(F_n) acts by inner automorphisms are empty**
  (`M ⋊_{F_n} Aut(F_n) ≅ M × Out(F_n)`). The host must see Aut acting by outer
  automorphisms on a centerless kernel. Then the splitting is unique if it exists.
- **The Euler class says how.** A strict compact model cannot virtually fix the cusp `w^∞`
  of a surface word. The input has to move through the parabolic point with infinite
  orbits: it must scale at the emitter, not sit there. This is the SYNTHESIS v5 dichotomy,
  now forced by a characteristic class.
