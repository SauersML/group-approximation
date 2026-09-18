---
rg: 2
id: simple-subgroups-act-trivially-on-equicontinuous-factors
kind: claim
title: A minimally almost periodic subgroup, e.g. an infinite f.g. simple group, acts trivially on the maximal equicontinuous factor of every minimal action; so free minimal actions of groups containing one are never almost automorphic, and functional couplings of almost-automorphic transverse layers kill it
distinct_from:
  injective-plane-lift-codings-force-finite-type: that kills M1 designs whose points are determined by the Y-coordinate plus a Λ_0-invariant factor; this kills designs whose Λ_0-planes are coupled by equivariant functions of an almost-automorphic transverse system, and constrains every free minimal system, SFT or not.
  binary-leavitt-unit-group-is-minimally-almost-periodic: that proves one group is minimally almost periodic; this uses the property for an arbitrary subgroup to constrain every minimal action of any overgroup.
  labbe-shift-is-a-toral-rotation-coding: that records Labbé's shift as an almost 1-1 extension of a toral rotation; this uses it as an instance of part 3.
---

**ESTABLISHED (lane proof, elementary, unreviewed; no priority claimed).** The proof is
below. It is standard topological dynamics; the only recalled inputs are Arzelà–Ascoli,
the universal property of the maximal equicontinuous factor (MEF), Peter–Weyl and
Malcev's theorem.

**Definitions.**
- A group `G` is *minimally almost periodic* (m.a.p.) if every homomorphism from `G` to a
  compact Hausdorff group is trivial.
- A minimal system is *almost automorphic* if some fiber of its MEF map is a singleton.

**Lemma 0.** Every infinite finitely generated simple group is m.a.p.

**Theorem.** Let `Λ` be a countable group acting minimally on a compact metrizable `X`,
let `π : X -> M` be the MEF, and let `G ≤ Λ` be m.a.p.
1. `G` acts trivially on `M`. Hence so does its normal closure in `Λ`.
2. If `Λ` acts freely and `G ≠ 1`, every fiber `π^{-1}(m)` is `G`-invariant, `G` acts
   freely on it, and it is infinite. In particular `X` is not almost automorphic.
3. **(Couplings.)** Let `H` be countable and `T` a minimal, almost automorphic
   `H`-system. Then every action of an m.a.p. group on `T` by homeomorphisms commuting
   with `H` is trivial. So for a homomorphism `α : Λ_0 -> Aut(T,H)`:
   - the `Λ_0 x H`-system `T`, with `Λ_0` acting through `α`, is not free as soon as
     `Λ_0` contains a nontrivial m.a.p. subgroup;
   - the same holds for the functionally coupled subshift
     `X_α = {x : x(λ,·) ∈ T, x(λs,·) = α(s)(x(λ,·))}`, with each `α(s)` a sliding block
     code. It is conjugate to `T` through `x ↦ x(1,·)`.

Instances of `T`: Labbé's Wang shift, whose MEF map has fiber cardinalities `{1,2,8}`
(`labbe-shift-is-a-toral-rotation-coding`); Sturmian and cut-and-project codings; Toeplitz
subshifts. Whether the Durand–Romashchenko fixed-point tilings are almost automorphic is
not checked here.

## Proof

**Lemma 0.** Let `ψ : G -> C` be a nontrivial homomorphism to a compact group.
- By Peter–Weyl, some finite-dimensional unitary representation `ρ` of `C` is
  nontrivial on `ψ(G)`.
- The kernel of `ρ∘ψ` is a proper normal subgroup of `G`, hence trivial. So `G` embeds
  in `U(n)`, and a f.g. linear group is residually finite (Malcev).
- An infinite residually finite group has a proper nontrivial normal subgroup of finite
  index, which contradicts simplicity.

**Part 1.**
- `M` is minimal and equicontinuous. By Arzelà–Ascoli, the uniform closure `K` of the
  maps `m ↦ λm` in `C(M,M)` is a compact topological group of homeomorphisms.
- `λ ↦ (m ↦ λm)` is a homomorphism `Λ -> K`. Its restriction to `G` is trivial because
  `G` is m.a.p.
- So every `g ∈ G` fixes `M` pointwise, and the kernel of `Λ -> K` is normal.

**Part 2.**
- `π(gx) = gπ(x) = π(x)`, so each fiber is `G`-invariant, and the action on it is free
  because the whole action is.
- A nontrivial m.a.p. group is infinite, since a finite nontrivial group embeds in the
  compact group formed by itself. So each fiber contains an infinite free `G`-orbit.
- A singleton fiber `{x}` would give `gx = x` for all `g ∈ G`.

**Part 3.**
- Let `π_T : T -> M_T` be the MEF of the `H`-action, and `φ` a homeomorphism of `T`
  commuting with `H`.
  - `π_T∘φ` is an `H`-factor map onto the equicontinuous `M_T`. By the universal
    property of the MEF there is a unique continuous `ψ_φ` with `π_T∘φ = ψ_φ∘π_T`.
  - Uniqueness makes `φ ↦ ψ_φ` a homomorphism into the group `Aut(M_T,H)` of
    `H`-equivariant homeomorphisms of `M_T`.
- `Aut(M_T,H)` is compact.
  - Write `M_T = K/L`, with `K` the compact group of part 1 for the `H`-action; the
    image of `H` in `K` is dense.
  - An `H`-equivariant homeomorphism `ψ` commutes with a dense subgroup of `K`, hence
    with `K`. So `ψ(kL) = kψ(L)`, and `ψ(L) = nL` with `n ∈ N_K(L)`.
  - Hence `Aut(M_T,H) ≅ N_K(L)/L`, a compact group.
- For an m.a.p. group `G` acting as above, `g ↦ ψ_g` is therefore trivial, and every
  `g` maps each `π_T`-fiber into itself.
- The set `S` of points with a singleton fiber is nonempty (almost automorphic) and
  `H`-invariant, hence dense by minimality. Each `g` fixes `S` pointwise, so `g = id`.
- **`X_α`.** `x ↦ x(1,·)` is a conjugacy onto `T`, because the rule
  `x(λs,·) = α(s)(x(λ,·))` and the homomorphism property determine every plane from the
  plane at `1`.
  - Under it, `Λ_0` acts through `α` (or through `α∘inv`, depending on the shift
    convention).
  - Any nontrivial m.a.p. subgroup therefore acts trivially, so `X_α` is not free.

## Lesson for general BH

**The input is invisible to every equicontinuous factor.** Boone–Higman reduces to
infinite simple Kazhdan inputs (`boone-higman-iff-simple-kazhdan-decidable-inputs`), and
these are m.a.p.
- For the master route's object (a free minimal SFT over an envelope `Λ` of such a `G`),
  `G` acts trivially on the maximal equicontinuous factor and lives entirely inside its
  fibers.
- So any rigidity or parsing argument that reads the structure off an equicontinuous
  factor (an odometer or toral rotation, as for hierarchical and cut-and-project tilings)
  controls only the part of `Λ` modulo the normal closure of `G`. The `G`-direction needs
  a rigidity that no equicontinuous factor sees.

**For coupled simulation (gate G1(g)).** Coupling the `Λ_0`-planes by equivariant
functions of an almost-automorphic transverse layer cannot make a simple input act freely.
`injective-plane-lift-codings-force-finite-type` closes the other deterministic option.
So every M1-type solution must couple planes by a genuine relation, a joining that is not
a graph, and must carry relational floating data.
