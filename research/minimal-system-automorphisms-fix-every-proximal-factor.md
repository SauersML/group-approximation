---
rg: 2
id: minimal-system-automorphisms-fix-every-proximal-factor
kind: claim
title: Automorphisms of a minimal system fix every factor map onto a proximal system and are determined by one point, so proximal systems have trivial commutant, finite extensions of proximal systems have finite commutant, and a minimally almost periodic group of automorphisms is trivial on every system that is a proximal or principal compact extension of its equicontinuous and proximal skeleton
requires:
  - simple-subgroups-act-trivially-on-equicontinuous-factors
  - deterministic-time-lifts-inherit-quantum-rigidity
  - free-group-boundary-shifts-are-quantum-rigid
  - labbe-shift-is-a-toral-rotation-coding
distinct_from:
  simple-subgroups-act-trivially-on-equicontinuous-factors: that shows a minimally almost periodic group acts trivially on the maximal equicontinuous factor, and on almost automorphic systems by automorphisms; this adds the proximal half (maps into proximal systems are unique, commutants act fibrewise over every proximal factor and injectively on each fibre) and the principal compact extension step, and applies both to the compression-rigid SFTs of master route v5.
  deterministic-time-lifts-inherit-quantum-rigidity: that shows time lifts inherit rigidity from the row SFT; this shows that over every rigid row SFT recorded on main, a minimally almost periodic time group acts trivially.
  time-lift-actors-carry-no-complexity-beyond-row-language: that bounds the complexity of automorphism groups by the row language; this bounds their dynamics by the row system's proximal and equicontinuous structure.
---

**ESTABLISHED** (lane bh-invent-16, 2026-09-18; lane proof, elementary, not reviewed). Items 1–4 are
standard topological dynamics (Auslander's book treats automorphisms of minimal flows); no priority is
claimed for them. The point here is items 5–7 and the consequence for the symbolic-dynamics (automorphism
group) route to Boone–Higman.

## Setting

`Λ` is a countable group acting by homeomorphisms on compact metric spaces. `Aut(Z, Λ)` is the group
of homeomorphisms of `Z` commuting with `Λ`; for a subshift these are the invertible cellular automata
(Curtis–Hedlund–Lyndon). A pair `z, z'` is **proximal** if `inf_λ d(λz, λz') = 0`. A system is proximal
if every pair is proximal. A factor map `π: Z → Y` is a **proximal extension** if every pair in one fibre
is proximal. A group is **m.a.p.** (minimally almost periodic) if every homomorphism to a compact group is
trivial; infinite finitely generated simple groups are m.a.p. (Lemma 0 of the first required node).

## Statement

Let `Z` be minimal.

1. **Uniqueness of maps to proximal systems.** If `B` is proximal (not necessarily minimal), there is at
   most one `Λ`-equivariant continuous map `Z → B`.
2. **Commutants act fibrewise over proximal factors.** For every factor map `π: Z → B` onto a proximal
   system and every `φ ∈ Aut(Z, Λ)`, `π ∘ φ = π`. No invariance of `π` under `Aut` has to be assumed.
3. **One point decides.** If `φ, ψ ∈ Aut(Z, Λ)` agree at one point, then `φ = ψ`. If `(z, φz)` is a
   proximal pair for one `z`, then `φ = id`.
4. **Counting.** Let `π: Z → B` with `B` proximal. For every `z`, `φ ↦ φ(z)` injects `Aut(Z, Λ)` into
   the fibre `π^-1(π z)`. Hence:
   - (a) if `Z` is proximal, `Aut(Z, Λ) = 1`;
   - (b) `|Aut(Z, Λ)|` is at most the smallest fibre cardinality of `π`; it is finite when `π` has a finite
     fibre and trivial when `π` has a singleton fibre.
5. **m.a.p. groups: the skeleton.** Let `G ≤ Aut(Z, Λ)` be m.a.p. Let `π_eq: Z → Z_eq` be the maximal
   equicontinuous factor, let `π_B: Z → B` be any factor map onto a proximal system, and let
   `ρ = (π_eq, π_B): Z → Z_eq × B`. Then `G` acts trivially on `Z_eq` and on `B`, so `ρ ∘ g = ρ` for
   `g ∈ G`, and `g ↦ g(z)` injects `G` into `ρ^-1(ρ z)` for every `z`. Consequently:
   - (a) if `ρ` is a proximal extension, `G = 1`. This holds in particular when `Z` is almost automorphic
     (`π_eq` has a singleton fibre), and when `Z` is proximal;
   - (b) if `ρ` has a finite fibre, `G` is finite, hence `G = 1` (a nontrivial m.a.p. group is infinite).
6. **m.a.p. groups: one compact step.** Suppose `G ≤ Aut(Z, Λ)` is m.a.p. and acts trivially on a factor
   `Y = Z/K`, where `K` is a compact group acting continuously and freely on `Z` on the right, commuting
   with `Λ` (a principal compact group extension). Then `G = 1`.
7. **Time lifts.** In the setting of `deterministic-time-lifts-inherit-quantum-rigidity`
   (`Φ: Λ_1 → Aut(Y)` over a row SFT `Y` over `Λ_2`), assume `Y` is `Λ_2`-minimal and of one of the
   types in 4(a), 4(b), 5(a), 5(b) or 6. Then every m.a.p. subgroup of `Λ_1` lies in `ker Φ`. So the
   lift is not faithful on it, and the joint `Λ_1 × Λ_2` action is not topologically free as soon as
   `Λ_1` contains a nontrivial m.a.p. subgroup.

## Proof

1. Let `π_1, π_2: Z → B` be equivariant and fix `z`. The pair `(π_1 z, π_2 z)` is proximal, so a net
   `λ_i` has `d(λ_i π_1 z, λ_i π_2 z) → 0`. Pass to a subnet with `λ_i z → z'` and `λ_i π_1 z → b`. Then
   `λ_i π_2 z → b` too. By continuity and equivariance `π_1 z' = lim π_1(λ_i z) = b` and likewise
   `π_2 z' = b`. So `E = {z : π_1 z = π_2 z}` is nonempty. It is closed and `Λ`-invariant, so `E = Z`.
2. Apply 1 to `π` and `π ∘ φ`, which is equivariant because `φ` commutes with `Λ`.
3. `ψ^-1 φ` fixes a point, and its fixed set is closed, nonempty and `Λ`-invariant, hence all of `Z`. For
   the second claim, take `λ_i` with `d(λ_i z, λ_i φ z) → 0` and a subnet `λ_i z → z'`. Then
   `φ(λ_i z) = λ_i φ z → z'` and `φ(λ_i z) → φ(z')`, so `φ` fixes `z'`; conclude as before.
4. By 2, `φ(z) ∈ π^-1(π z)`. By 3, `φ` is determined by `φ(z)`. For (a) take `B = Z` and `π = id`.
5. For `φ ∈ Aut(Z, Λ)`, `π_eq ∘ φ` is a factor map onto an equicontinuous system, so it factors uniquely
   as `ψ_φ ∘ π_eq`. Uniqueness makes `φ ↦ ψ_φ` a homomorphism into `Aut(Z_eq, Λ)`, and that group is
   compact (`simple-subgroups-act-trivially-on-equicontinuous-factors`, proof of part 3:
   `Aut(M, H) ≅ N_K(L)/L`). So `G` acts trivially on `Z_eq`. It acts trivially on `B` by 2. The injection
   is 3. For (a), `(z, gz)` lies in one `ρ`-fibre, so it is proximal, and `g = id` by 3. An almost 1-1
   extension of minimal systems is proximal: if `π_eq^-1(y_0)` is a singleton and `π_eq z = π_eq z'`,
   take `λ_i` with `λ_i π_eq z → y_0` (minimality of `Z_eq`); every limit point of `(λ_i z, λ_i z')` lies
   over `y_0`, hence on the diagonal. For (b), `G` embeds in a finite group, which is compact.
6. If `g` induces the identity on `Y`, then `g(z) = z · k(z)` for a unique `k(z) ∈ K`. The map
   `Z × K → Z ×_Y Z`, `(z, k) ↦ (z, zk)`, is a continuous bijection from a compact space onto a Hausdorff
   one, so `k` is continuous. Equivariance gives `λ z · k(λz) = λ(z · k(z)) = λz · k(z)`, so `k` is
   `Λ`-invariant, hence constant by minimality. So `g` is right translation by an element `k_g ∈ K`, and
   `g ↦ k_g^-1` is an injective homomorphism `G → K`. `K` is compact and `G` is m.a.p., so `G = 1`.
7. `Φ` restricted to an m.a.p. subgroup of `Λ_1` has m.a.p. image in `Aut(Y, Λ_2)`, which is trivial by
   the item that applies. A nontrivial element acting trivially on `Y` fixes every point of the lift
   (the lift is conjugate to `Y` with the joint action). ∎

## Instances on main

- **Proximal, so `Aut = 1` (4(a)).** The end shift `X_∂ ≅ ∂T` of a free group
  (`free-group-boundary-shifts-are-quantum-rigid`): a non-elementary tree action is minimal and strongly
  proximal on the ends. The same holds for its products over products of free groups, since the product
  group acts coordinatewise. These are the compression-rigid SFTs of master route v5.
- **Finite over proximal, so `Aut` finite (4(b)).** The Ã₂ skew shift `P → Ω` of
  `a2-lattice-boundary-skew-shifts-are-quantum-rigid` is a finite-to-one factor map onto the chambers at
  infinity. This applies *if* `Γ ↷ Ω` is proximal, as it is for lattices acting on the chamber boundary of
  a Bruhat–Tits building; for exotic Ã₂ buildings this is not checked here.
- **Almost automorphic, so no m.a.p. automorphisms (5(a)).** Labbé's shift
  (`labbe-shift-is-a-toral-rotation-coding`, which has a singleton fibre over its rotation), Sturmian and
  cut-and-project codings, and Toeplitz shifts. Whether the Durand–Romashchenko fixed-point tile sets are
  almost automorphic is not checked.

## What it changes

**The commutant–compression dichotomy.** Master route v5 gets rigidity cheaply from compression, which
means boundary-type, proximal dynamics, and from hierarchy, which means almost automorphic dynamics. Both
kill commutants.
- A proximal system has no automorphisms at all.
- An almost automorphic one has no m.a.p. automorphisms.
- Anything finite, proximal or principal-compact over the skeleton `Z_eq × B` has only finite or trivial
  m.a.p. automorphisms.

So the natural symbolic-dynamics host for a Kazhdan simple input fails over every rigid row SFT recorded
on main. That host lets the input act by cellular automata on a rigid SFT over a fixed scaffold, which is
a time lift, a group of automorphisms, or a group of reversible cellular automata. It fails whether the
scaffold is `Z^2`, a free group, a product of free groups or an Ã₂ lattice. This extends the v5
retirement of time lifts ("no odometer parse") from equicontinuous rows to the non-amenable, compression
rigid rows that v5 relies on.

**What an automorphism host would need.** Here `G` is m.a.p.; items 5 and 6 then force the following.
- In a minimal row system, `G` moves points only inside the infinite fibres of the skeleton map `ρ`.
- On every `G`-orbit the points are pairwise distal.
- No principal compact extension above the skeleton helps.

So `G` must act in the part of `Z` that is neither proximal nor a compact extension. By the
Furstenberg–Veech structure theory that is the relatively weakly mixing part. Weak mixing is the
independence that breaks quantum rigidity over `Z^d` (positive entropy, walls). The live object would be
new: a quantum-rigid minimal SFT over a non-amenable group that is relatively weakly mixing over its
skeleton, with a large commutant. The other escape is a non-minimal row system, on which `G` permutes
the `Λ_2`-minimal subsets. Items 1–6 then apply to each minimal subset and its stabilizer. As a design
remark, not proved: `G` then acts through the space of `Λ_2`-orbit closures, where `Λ_2` is trivial, so
the input's dynamics is again a `Λ_1`-system that must be built directly. That is (★′) for `Λ_1` alone.

## Lesson for general BH

**Cheap rigidity and commutation are mutually exclusive.** An automorphism of a minimal system must fix
every map to a proximal system and cannot move a point to a proximal partner. So the compression
mechanism that makes v5's rigidity cheap is exactly what forbids hosting an input by automorphisms. With
the equicontinuous half (m.a.p. inputs are invisible there), the result is this.

A Kazhdan simple input can act on a rigid system only through the acting group, never through the
system's commutant. The commutant route (reversible cellular automata, `Aut(σ)`, time lifts, space–time
codings) is therefore not a shortcut past (★′). It needs a rigidity source for relatively weakly mixing
dynamics, and none is known.
