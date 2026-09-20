---
rg: 2
id: pcf-rational-nekrashevych-groups-are-f-infinity
kind: claim
title: For every post-critically finite rational map f of degree d >= 2, including sub-hyperbolic maps with critical points in the Julia set, V_{d,r}(IMG f) has type F_infinity; the cover is the orbifold fundamental group of Thurston's orbifold, and its kernel dies because short orbifold loops are elliptic while the kernel is torsion-free
requires:
  - wreath-recursion-thompson-groups-inherit-fn
distinct_from:
  hyperbolic-pcf-rational-nekrashevych-groups-are-f-infinity: that covers hyperbolic PCF maps (no postcritical point in the Julia set), where the cover is the ordinary fundamental group of a planar surface; this covers every PCF map, where postcritical points in the Julia set force torsion into the cover, and replaces Nekrashevych's short-loop lemma by an orbifold version.
  contracting-rover-nekrashevych-groups-are-f-infinity: that is the Skipper-Zaremsky question for all contracting G; this settles the class of iterated monodromy groups of PCF rational maps, whatever their activity growth.
  contracting-groups-have-dying-kernel-covers-of-type-fn: that asks for dying-kernel F_n covers of every contracting group; this supplies them, of type F_infinity, for IMGs of PCF rational maps.
---

**OPEN (proof claimed, under review).** The lane proof is by bh-sz-vdg, 2026-09-19. Referees:
- bh-ref-g for this node;
- bh-ref-q12 for `wreath-recursion-thompson-groups-inherit-fn`, the unreviewed lane proof it rests on.

The status flips to ESTABLISHED only after both pass. No priority claimed.

**Search status.** The result was not found in:
- Belk–Hyde–Matucci arXiv:2407.03149, which covers bounded automata;
- Skipper–Zaremsky arXiv:1709.06524 and 2109.13389;
- Nekrashevych arXiv:1312.5654, which proves finite presentation and asks the question;
- a 09-19 web search.

## Statement

**Lemma 1 (short displacement is elliptic).** Let a group `Γ` act properly, cocompactly and by isometries on a proper
geodesic space `Y`. Then there is `ε_0 > 0` such that for every `y ∈ Y`, every `γ` with `d(y, γy) < ε_0` lies in the
stabilizer of some point of `Y`. That stabilizer is a finite subgroup.

**Lemma 2 (orbifold dying kernel).** Let `M` be a compact, connected, good 2-orbifold, possibly with boundary, carrying
an orbifold length metric. Let `M_1 ⊆ M` be a closed suborbifold region, with `ι : M_1 → M` the inclusion, an orbifold
map. Let `f : M_1 → M` be a degree-`d` orbifold covering that is **expanding**: there is `λ < 1` such that for every
orbifold path `γ` in `M` and every `f`-lift `γ'` of it, `length(ι γ') ≤ λ · length(γ)`.

Let `B = π_1^orb(M, t)` with its wreath recursion `ψ : B → B ≀ S_d`, given by lifting through `f` and pushing forward
by `ι` along connecting paths, as in Nekrashevych's orbifold iterated monodromy construction. Let `G = B/K` be its
faithful quotient. Assume:

> **(T)** every finite subgroup of `B` meets `K` trivially.

Then the recursion has dying kernel: `K = ⋃_n K_n`, with `K_n` as in `wreath-recursion-thompson-groups-inherit-fn`.

**Theorem.** Let `f` be a post-critically finite rational map of degree `d ≥ 2`. Then `V_{d,r}(IMG f)` has type `F_∞`
for every `r ≥ 1`.

## Proofs

**Lemma 1.**
- Let `K ⊆ Y` be compact with `ΓK = Y`. By properness, the set `F = {γ : γ N_1(K) ∩ N_1(K) ≠ ∅}` is finite, where
  `N_1` is the closed 1-neighborhood.
- For `x ∈ K`, put `ε(x) = min(1, min{d(x, γx) : γ ∈ F, γx ≠ x}) > 0`.
- Cover `K` by finitely many balls `B(x_i, ε(x_i)/4)` and put `ε_0 = min_i ε(x_i)/2`.
- **The case `y ∈ K`.** Let `y ∈ B(x_i, ε(x_i)/4)` and `d(y, γy) < ε_0`. Then `γ ∈ F`, and
  `d(x_i, γx_i) ≤ d(x_i, y) + d(y, γy) + d(γy, γx_i) < ε(x_i)`. So `γ` fixes `x_i`.
- **General `y`.** Write `y = hy_0` with `y_0 ∈ K`, and conjugate: `h⁻¹γh` fixes some `x_i`, so `γ` fixes `hx_i`.
- Point stabilizers are finite by properness. ∎

**Lemma 2.**
- **Setup.** Let `g ∈ K`, represented by an orbifold loop at `t` of length `ℓ`. Let `Y` be the universal orbifold
  cover of `M`, which is a manifold because `M` is good. It carries the lifted length metric, and `B` acts on it
  properly, cocompactly and isometrically. Take `ε_0` from Lemma 1 and `n` with `λ^n ℓ < ε_0`.
- **Vertices.** `g` fixes every level-`n` vertex `v`, since it acts trivially.
- **Sections.** The `f^n`-lift of `g` from the point `z_v` over `v`, pushed forward by `ι`, is therefore an orbifold loop
  at `z_v`. Its length is `≤ λ^n ℓ`. Call its class `δ_v ∈ π_1^orb(M, z_v)`.
  - The section `g|_v` is `δ_v`, transported to `t` along the connecting path of `v`.
  - Identify `π_1^orb(M, z_v)` with `B` via that path, and choose a lift `z̃_v ∈ Y`. Then `d(z̃_v, δ_v z̃_v) ≤ λ^n ℓ <
    ε_0`.
- **So `g|_v = 1`.**
  - By Lemma 1, `g|_v = δ_v` lies in a finite subgroup of `B`.
  - `g|_v ∈ K`, since a section of an element acting trivially acts trivially.
  - By (T), `g|_v = 1`.
- **Conclusion.** `g` fixes `X^n` and all its level-`n` sections are trivial, so `g ∈ K_n`. ∎

**Theorem.**

1. **Thurston's orbifold.** Let `ν = ν_f : Ĉ → {1, 2, …, ∞}` be Thurston's function: `ν(p)` is the lcm of
   `deg_z(f^k)` over `k ≥ 1` and `z ∈ f^{−k}(p)`. It satisfies `deg_z(f) · ν(z) | ν(f(z))`.
   - `ν(p) > 1` exactly on the postcritical set `P_f`.
   - `ν(p) = ∞` exactly on the periodic cycles in `P_f` that contain a critical point. For other points of `P_f`, the
     backward chains visit each critical point at most once, so the local degrees are bounded.
   - Let `P_∞ = ν^{−1}(∞)`. It lies in the Fatou set, as superattracting cycles.
   - The orbifold `O_f = (Ĉ ∖ P_∞, ν)` is hyperbolic or Euclidean, never bad (Thurston; recalled).
2. **The pair.**
   - Take `U` to be a finite union of small Böttcher discs around `P_∞`, with `f(U) ⊂ U`. Take `M = Ĉ ∖ U`, with
     cone orders `ν`. It is compact, connected and good.
   - Put `M_1 = f^{−1}(M) ⊆ M`, with orders `ν_1(z) = ν(f(z))/deg_z f`.
   - Then `f : M_1 → M` is an orbifold covering of degree `d`, and `ι` is an orbifold map because `ν(z) | ν_1(z)`.
   - The recursion on `π_1(M ∖ P_f)` descends to `B = π_1^orb(M)`. A section of `r_p^{ν(p)}` at `z ∈ f^{−1}(p)` is
     conjugate to `r_z^{ν(p)/deg_z f}`, which is a power of `r_z^{ν(z)}`. Here `r_p` is a small loop around `p`.
   - The faithful quotient is `IMG f`.
3. **Expanding.** `f` is expanding for the orbifold metric on `M` (Douady–Hubbard; Nekrashevych, *Self-similar groups*,
   §5.5 and §6.4; recalled, not re-read).
   - In the hyperbolic case, `ι` is a holomorphic orbifold map that is not a covering, so it strictly contracts
     hyperbolic orbifold metrics (Schwarz–Pick). The contraction is uniform on the compact `M_1`.
   - In the Euclidean case (`z^{±d}`, Chebyshev maps, Lattès maps), `f` expands the flat metric by `d^{1/2}` or more.
4. **(T) holds.** Every finite subgroup of `B` is conjugate into a cone group `⟨r_p⟩ ≅ Z/ν(p)`.
   - If `∂M ≠ ∅`, `B` is a free product of these cyclic groups and a free group, and Kurosh applies.
   - If `M = Ĉ`, `B` is a cocompact Fuchsian or crystallographic group of the sphere, and finite subgroups are point
     stabilizers.
   - The image of `r_p` in `IMG f` has order exactly `ν(p)`. On level `k`, lifting `r_p` by `f^k` permutes `f^{−k}(t)`
     with cycle lengths `deg_z(f^k)` for `z ∈ f^{−k}(p)`, so its order on level `k` is `lcm_z deg_z(f^k)`. The lcm of
     these over `k` is `ν(p)`.
   - So `⟨r_p⟩ ∩ K = 1`.
5. **Conclusion.**
   - By Lemma 2, the recursion on `B` has dying kernel.
   - `B` has type `F_∞`: it is virtually free if `∂M ≠ ∅`, and virtually a surface group or virtually `Z^2` otherwise.
   - Part 2 of `wreath-recursion-thompson-groups-inherit-fn` then gives `V_{d,r}(B, ψ) ≅ V_{d,r}(IMG f)` of type
     `F_∞`. ∎

## Scope

**New cases.**
- Some PCF IMGs were already known to give `F_∞` groups:
  - PCF polynomials, which have bounded IMGs;
  - hyperbolic PCF maps, by `hyperbolic-pcf-rational-nekrashevych-groups-are-f-infinity`;
  - Euclidean-orbifold maps, where the orbifold group is itself `F_∞` and faithful, the Skipper–Zaremsky case.
- The genuinely new ones are non-polynomial sub-hyperbolic maps, e.g. PCF rational maps whose Julia set is the whole
  sphere and whose orbifold is hyperbolic, such as `f(z) = ((z−2)/z)^2` (recalled example).
  - Their limit space is `S^2`, which is not finitely ramified, so they are not bounded.
  - The activity growth of these IMGs is not computed here. The expectation is exponential, i.e. case (E) of
    `level-set-route-reaches-only-bounded-rover-nekrashevych-groups`. That is a check, not a claim.

**Why the obvious orbifold transcription fails, and what replaces it.** Nekrashevych's `pr:expandingpi1` uses
"short loops are null-homotopic". In an orbifold, a short loop around a cone point is a nontrivial torsion element.
Lemma 1 says short loops are elliptic, and (T) says elliptic elements never die. So a dying kernel is exactly a
torsion-free kernel.

**Lesson.**
- A dying kernel needs only that the cover's finite subgroups inject into the self-similar group.
- For dynamical covers, torsion is exactly the local branching data, which the self-similar group sees.
- So the right cover is the orbifold group, never the surface group of the punctured sphere.

**Next.** Contracting groups not of dynamical origin, the rest of case (E).
- The candidate cover is Nekrashevych's `U(N)` with its length-3 relations.
- Lemma 2's argument needs a geometric model: a cocompact proper action on which sections contract displacement.
- Bartholdi's non-positively-curved contracting covers (arXiv:1107.5339, abstract only) look like exactly that.
