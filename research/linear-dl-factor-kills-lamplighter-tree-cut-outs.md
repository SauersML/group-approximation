---
rg: 2
id: linear-dl-factor-kills-lamplighter-tree-cut-outs
kind: claim
title: "In a tree cut-out of a lamplighter-type P = L x| Z (L infinite locally finite) with H torsion-free and rho injective on H, the flat fixator H ∩ Σ lies in a split torus normalized by H as soon as ONE factor where the shift is hyperbolic acts through PGL_2 of a local field; so H is virtually abelian, a contradiction: every host with a faithful PGL_2(k) factor among the hyperbolic ones (all S-arithmetic quaternionic lattices, with any other factors Aut(T)) is killed, and in three-tree lattices the lamp preimage must be a free group acting freely on the third tree, with H ∩ Σ infinitely generated free"
distinct_from:
  tree-cut-outs-force-locally-finite-by-abelian-quotients: That forces the Diestel-Leader shape and a nontrivial flat fixator but leaves open whether a lattice can supply one; this shows that a single linear PGL_2 factor among the two DL factors already forbids it, and pins down the fixator as an infinitely generated free group otherwise.
  rank-one-cut-outs-kill-amenable-non-abelian-quotients: That needs every factor AS (all rank-one algebraic), a VSA host and injective subproduct projections; this needs only one linear factor among the hyperbolic ones, a torsion-free H and injectivity of that one projection on H, and allows every other factor to be an arbitrary closed subgroup of Aut(T) (e.g. Burger-Mozes universal groups).
---

**ESTABLISHED (proposed, 2026-09-19; referee welcome).** Setting and
notation of `tree-cut-outs-force-locally-finite-by-abelian-quotients`
(Theorem B): a tree cut-out `ρ : Λ -> G_1 × ... × G_s`, `K ≤ G` compact
open, `H = φ(F)` with `H ∩ Σ = H ∩ ρ^{-1}(K)`,
`P = H/(H ∩ Σ) = L ⋊ ⟨t⟩` finitely generated with `L ≠ 1` locally finite, no
nontrivial finite normal subgroup and `C_L(t^d) = 1` for `d ≠ 0`
(e.g. `A ≀ Z`, `A` finite nontrivial). `τ₀ ∈ H` maps to a power `t^m`,
`J` is the set of factors where `ρ_j(τ₀)` is hyperbolic, `ℓ_j` its axis.
Write `N = H ∩ Σ` and `H_L` for the preimage of `L` in `H`.

**Theorem C (one linear DL factor kills).** Suppose `H` is torsion-free,
`ρ` is injective on `H`, and for some `j ∈ J` the factor action is linear:
`T_j` is the Bruhat–Tits tree of `PGL_2(k)` for a non-archimedean local
field `k` (any characteristic), `ρ_j(H) ≤ PGL_2(k)` acting in the standard
way, and `ρ_j` is injective on `H`. Then `H` is virtually abelian. Since
`P` is then virtually abelian but has the infinite locally finite normal
subgroup `L`, **no such cut-out exists**.

The mechanism, in three lines:
1. `ρ_j(N)` fixes `ℓ_j` pointwise (Theorem B2), and the pointwise fixator
   of an apartment in `PGL_2(k)` is the compact torus `T(O)` of the split
   torus `T` whose apartment is `ℓ_j`.
2. `N ≠ 1` (Theorem B3), so `N` contains an element `n` of infinite order;
   `ρ_j(n)` is a regular element of `T` with centralizer exactly `T`.
3. For `h ∈ H`, `h n h^{-1} ∈ N`, so `ρ_j(h)` conjugates `T` to the
   centralizer of `ρ_j(hnh^{-1}) ∈ T`, which is `T`. So
   `ρ_j(H) ≤ N(T) = T ⋊ Z/2`, which is virtually abelian.

**Corollaries.**
1. **Arithmetic hosts.** Every torsion-free `S`-arithmetic group `Λ` of a
   quaternion algebra over a global field, embedded as a lattice in
   `∏_{v ∈ S} PGL_2(k_v)`, has each projection injective. So Theorem C
   kills every `Aut(T)` cut-out of `A ≀ Z` from such a `Λ`, **whatever the
   ambient groups `G_j ≤ Aut(T_j)`** are (enlarging `G_j` to all of
   `Aut(T_j)` does not help, because only `ρ_j(Λ)` enters). This covers the
   arithmetic lattices in products of two or more trees (e.g. those of
   Mozes, Stix–Vdovina and Rungtanapirom), in every characteristic.
2. **Mixed hosts.** A lattice in `PGL_2(k) × Aut(T_2) × ... ` with injective
   first projection is killed whenever the linear factor is cut out and
   `τ₀` is hyperbolic there (B1 gives two such factors). What survives
   must have **both** DL factors non-linear on `H`.
3. **Three-tree lattices, general case (Theorem D).** Let `Λ` be a
   torsion-free lattice in `G_a × G_b × G_c`, cut out in `(b, c)` with
   `ρ = pr_{bc}` injective. Then:
   - the preimage `E` in `H` of every finite subgroup of `L` has
     relatively compact image in `G_b × G_c`, hence acts freely on `T_a`
     and is free;
   - `H_L` acts freely on `T_a` and is a free group, and
     `H = H_L ⋊ ⟨τ₀'⟩` for any `τ₀' ∈ H` mapping to `t`;
   - `N` is a normal subgroup of `H` that is an **infinitely generated**
     free group; for `P = Z/2 ≀ Z`, `N ≅ Z` or `N` of finite rank is
     impossible, and so is any abelian `N`
     (more generally: whenever `L` has a non-cyclic finite subgroup).
   So a surviving three-tree witness needs, inside `Λ_F`, an infinitely
   generated free normal subgroup of `H`, with
   `H_L` free and `ρ(H_L)` locally elliptic in both DL factors.

**Calibration.**
- For `P = Z^k` or other virtually abelian `P` (not of the `L ⋊ Z` shape)
  nothing is claimed; they are realized by flats of arithmetic lattices.
- The discrete `DL(2,2)` action of `Z/2 ≀ Z` is not a counterexample: it
  has `N = 1`, i.e. `H ≅ P` has torsion, which Theorem C excludes by
  hypothesis (`H` torsion-free).
- The abstract group-theoretic part of D is attainable: `H = F_2 = ⟨a, t⟩`
  maps onto `Z/2 ≀ Z` with `H_L` free on `{t^i a t^{-i}}` and `N`
  infinitely generated free. So D does not kill by itself; it constrains
  where the fixator can live.

Proof: route `linear-dl-factor-kills-lamplighter-tree-cut-outs-proof`.

## Attempts

- 2026-09-19 (w18-117): Theorems C and D proved. Proposed-established.
  Open: a torsion-free irreducible lattice in three trees whose two DL
  projections are both non-linear on `H` (e.g. Burger–Mozes, Wise or
  Rattaggi non-residually-finite lattices), with an infinitely generated
  free `N ⊴ H` inside the flat fixator `Λ_F`.
