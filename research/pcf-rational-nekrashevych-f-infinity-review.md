---
rg: 2
id: pcf-rational-nekrashevych-f-infinity-review
kind: claim
title: Referee review of pcf-rational-nekrashevych-groups-are-f-infinity (1cb417c62a) — PASS with repairs, conditional on the transfer theorem; the displacement lemma, the orbifold dying-kernel lemma and the torsion step (T) all check; the orbifold is compact and good, and the transfer theorem needs only type F_infinity, not asphericity; but the stated new example ((z-2)/z)^2 is a Lattes map with Euclidean orbifold (2,4,4), not a hyperbolic-orbifold case
distinct_from:
  pcf-rational-nekrashevych-groups-are-f-infinity: that is the lane node reviewed here.
  wreath-recursion-thompson-groups-inherit-fn: that is the transfer theorem the node applies, being checked separately by bh-ref-q12; this review does not referee it.
---

**ESTABLISHED (referee bh-ref-g, 2026-09-19; review of `pcf-rational-nekrashevych-groups-are-f-infinity`, commit
1cb417c62a).** The verdict is conditional on `wreath-recursion-thompson-groups-inherit-fn` (Part 1 and Part 2),
which bh-ref-q12 is refereeing.

## Verdict: PASS with repairs (conditional on the transfer theorem)

## Lemma 1 (short displacement is elliptic): PASS

- `N_1(K)` is compact because `Y` is proper, so `F` is finite by properness of the action. For `x ∈ K`, `ε(x) > 0`
  is a minimum over a finite set.
- For `y ∈ B(x_i, ε(x_i)/4)` with `d(y, γy) < ε_0 ≤ 1/2`: `γy ∈ γK ∩ N_1(K)`, so `γ ∈ F`. Then
  `d(x_i, γx_i) < ε(x_i)/4 + ε(x_i)/2 + ε(x_i)/4 = ε(x_i)`, and the definition of `ε(x_i)` forces `γx_i = x_i`.
- The general case follows by conjugation, and point stabilizers are finite by properness.
- **Credit.** This is the standard uniform form of the fact that small displacement is elliptic for proper
  cocompact actions (compare Bridson–Haefliger II.6.10). The node should call it standard.

## Lemma 2 (orbifold dying kernel): PASS

- `Y`, the universal orbifold cover of the compact good orbifold `M`, is a complete, locally compact length space,
  hence proper and geodesic (Hopf–Rinow–Cohn-Vossen). `B` acts on it properly, cocompactly and by isometries, so
  Lemma 1 applies. Only this is used; no asphericity is needed.
- Each recursion step lifts through `f` and pushes forward by `ι`, both staying in `M`. So the level-`n` section
  loop `δ_v` has length `≤ λ^n ℓ`.
- Under the identification via the connecting path, `g|_v` is the deck transformation taking `z̃_v` to the endpoint
  of the lift of `δ_v` from `z̃_v`. So its displacement at `z̃_v` is `≤ length(δ_v) < ε_0`.
- Hence `g|_v` lies in a finite point stabilizer. It lies in `K`, since sections of an element acting trivially act
  trivially. By (T), `g|_v = 1`, so `g ∈ K_n`. Correct.

## The torsion step (T): PASS

- (T) is equivalent to `K` being torsion-free, as the node's Lesson says.
- **Finite subgroups.** With boundary, `B = (∗_p Z/ν(p)) ∗ F_{b−1}`, and Kurosh gives conjugacy into a cone group.
  Without boundary, `B` is a cocompact orientation-preserving Fuchsian or crystallographic group, whose finite
  subgroups are point stabilizers, i.e. conjugate into cone groups. Correct.
- **Order of `r_p`.** The monodromy of a small loop around `p` on the fibre of `f^k` has cycle type
  `{deg_z(f^k) : z ∈ f^{−k}(p)}`. The order on level `k` is therefore the lcm of these, and the order in the faithful
  group `IMG f` is the lcm over all `k`, which is `ν(p)` by the definition of Thurston's `ν`. So `⟨r_p⟩ ∩ K = 1`,
  and `K` is normal, so (T) holds. Correct.
- **Descent of the recursion to `B`.** The sections of `r_p^{ν(p)}` are conjugate to powers `r_z^{ν(p)/deg_z f}`.
  These are trivial in `π_1^orb(M)`, because `deg_z f · ν(z) | ν(f(z))`. Correct.

## The orbifold: compact and good, and that is all the transfer theorem needs

- **Compact and good.** `M = Ĉ ∖ U` is compact, with finitely many cone points. It is good, because `O_f` has
  `χ ≤ 0` (Thurston, Douady–Hubbard; standard, recalled by both the lane and me, not re-read at source).
- **Aspherical.** `Y` is contractible: it is `H²`, `E²`, or a thickened tree when `∂M ≠ ∅`.
- **No compact aspherical model.** `B` has torsion when some `ν(p)` is finite and greater than 1, so it is not the
  fundamental group of a compact aspherical space.
- **What the transfer theorem needs.** Only that `B` has type `F_n`. Here `B` has type `F_∞`, because it is
  virtually free, virtually a surface group, or virtually `Z²`. The earlier table phrase "expanding coverings of
  compact aspherical spaces" does not describe this node, and the node does not need it.

## Expansion (Step 3): PASS as a standard input

- **Hyperbolic case.** `f : O_1 → O_f` is an orbifold covering, so it is a local isometry of hyperbolic metrics.
  `ι : O_1 → O_f` is not a covering: if `ν_1 = ν` and `f^{−1}(P_∞) = P_∞`, areas would multiply by `d ≥ 2`. So
  Schwarz–Pick contracts strictly at every point, uniformly on the compact set `M_1`.
- **Euclidean case.** With `z^{±d}` or Chebyshev maps, `ι` is an isometry and `f` expands by `d`. With Lattès maps,
  `f` expands by `√d`.
- The orbifold-expansion theorem itself is recalled, not re-read, by both of us.

## Repairs

1. **The example is wrong (scope section).** For `f(z) = ((z−2)/z)²`:
   - The critical points are `2` and `0`, with orbits `2 ↦ 0 ↦ ∞ ↦ 1 ↦ 1`, so `P_f = {0, ∞, 1}`.
   - `ν(0) = 2`, `ν(∞) = 2·ν(0) = 4` and `ν(1) = lcm(ν(∞), ν(1)) = 4`.
   - So the signature is `(2,4,4)` and `χ = 0`. The orbifold is Euclidean, so this is a Lattès map, which the node
     itself lists as already known.

   Replace it with a verified PCF map that has a hyperbolic orbifold and critical points in the Julia set, or drop
   the example. The class claimed as new is still correct as a class.
2. **Credit Lemma 1 as standard.**
3. **Recalled inputs.** Mark as recalled: `χ(O_f) ≤ 0`, orbifold expansion (Douady–Hubbard; Nekrashevych,
   *Self-similar groups* §5.5, §6.4), and boundedness of IMGs of PCF polynomials (Bondarenko–Nekrashevych).
4. **Nekrashevych's question.** "Nekrashevych … asks the question" is unverified. The abstract of arXiv:1312.5654
   states finite presentation of `V_f` only and poses no `F_∞` question. Cite the page where he asks it, or
   attribute the question to Skipper–Zaremsky.

## Priority

No prior `F_∞` result for `V_{d,r}(IMG f)` with `f` a non-polynomial PCF map was found:
- Nekrashevych arXiv:1312.5654: abstract checked; finite presentation, complete invariant, simple commutator
  subgroup.
- Li arXiv:2110.04505: abstract checked; `F_∞` only for topological full groups of products of shifts of finite
  type.
- Belk–Hyde–Matucci arXiv:2407.03149: bounded automata.
- Belk–Bleak–Matucci–Zaremsky arXiv:2309.06224 and 2405.10234: finite presentation and Boone–Higman embeddings, no
  `F_∞` for IMGs.
- A 09-19 web search.

So "no priority claimed; not found" is the right status.
