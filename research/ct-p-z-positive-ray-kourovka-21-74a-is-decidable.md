---
rg: 2
id: ct-p-z-positive-ray-kourovka-21-74a-is-decidable
kind: claim
title: "Kourovka 21.74(a) is decidable for every g in CT_P(Z) (P finite) whose slopes lie in γ^Z for an integer γ ≥ 2: refined along the ray, g is an almost-automorphism of a forest, neutral primes and outside primes become unit-slope fibres, and the attractor–repeller holonomy bound and finite box search of the V case go through; mixed-sign and rank-two slopes are exactly where the base itself becomes hyperbolic"
distinct_from:
  ct-empty-z-kourovka-21-74a-is-decidable: that is the case P = ∅ (γ = 2, base the binary tree); this allows odd primes in the moduli, as long as the slopes stay on one positive ray.
  ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44: that is the orbit-transversal question (20.44) under the same ray hypothesis; this is the partition question (21.74(a)).
---

**ESTABLISHED** (lane proof, not reviewed). No priority claimed.
- **The problem.** Kourovka 21.74(a) (S. Kohl) asks whether it is decidable if a given
  `g ∈ CT(Z)` permutes a nontrivial partition of `Z` into residue classes.
- **What this settles.** (a) for every `g` whose slopes lie on one positive ray, with classes of
  any moduli.
- **What stays open.** 21.74(a) itself is OPEN for mixed-sign and rank-two slopes.
- **The proof.** It is that of `ct-empty-z-kourovka-21-74a-is-decidable`, after the reduction
  below. Only the changes are written out.

## Reduction to a forest

- **Notation.** Let `S = P ∪ {2}`, `m_d = ∏_{p∈S} p^(d_p)`, and let `v ∈ N^S ∖ {0}` with
  `γ = m_v`. Every piece `r(m_d) → s(m_(d+κv))` of `g` has degree change `κv`.
- **The primes.** Split `S` into `S_+ = {v_p ≥ 1}` and `S_0 = {v_p = 0}`, the *neutral*
  primes. Let `b ∈ N^(S_0)` bound the `S_0`-degrees of all pieces. These degrees are the same on
  both sides of a piece, since `v_p = 0`.
- **Refining.** Refine each piece's domain to cylinders of degree `Nv + b` (with `N` large). Their
  images have degree `(N + κ)v + b`, and `N + κ ≥ 0` because some `v_p ≥ 1`.
- **The forest `F`.** Its level-`n` vertices are the classes mod `m_(nv+b)`, and a vertex's
  children are its refinements mod `m_((n+1)v+b)`. So `F` has `m_b` roots, each an `m_v`-ary tree,
  and a canonical map between two such classes is a prefix replacement of `F`. Hence `g` acts on
  `∂F = ∏_{S_+} Z_p × ∏_{S_0} Z/p^(b_p)` as an almost-automorphism of `F`, a locally finite
  rooted tree once one root is added.
- **The fibre.** `Ẑ = ∂F × Φ`, where the fibre `Φ` consists of the neutral digits beyond depth
  `b_p` (`p ∈ S_0`), times `Ẑ_(S′)`. `ĝ` is a skew product over `∂F`, with affine fibre maps of
  unit slope `γ^κ`: on `Ẑ_(S′)` by the piece's own formula, and on a neutral `Z_p` by the same
  formula written in the deep digits.
- **Parts.** A residue class is a box: a product of balls, one per prime. It is (base box) ×
  (fibre box), and the base box is a finite union of cylinders of `F`.

## The three changes to the V proof

1. **Base dynamics.**
   - Gilabert Vio (arXiv:2412.08784v3, Cor. 2.4) holds for almost-automorphisms of any locally
     finite rooted tree. It gives `∂F = U ⊔ V`, with finitely many hyperbolic periodic points and
     uniform flow on `V`.
   - Revealing pairs exist (Goffer–Lederle, Lemma 2.17, cited there) and are found by
     enumerating tree pairs of `F`.
   - The flow components `R_j`, Lemma A and their computability transfer word for word, with
     cylinders of `F` in place of cones.
2. **Hulls.** A part meeting `R_j × Φ` has base shadow `⊇ R_j`, by the Lemma B.1 argument
   (projection of `ĝ^K(C) = C`). Boxes containing `R_j` form a finite product of chains of balls,
   one chain per prime, so there are finitely many base candidates.
3. **Holonomy bound on the fibre.**
   - Near an attractor `a`, the formula of `g^M` is `C(y) = a_Q + γ^(κ_a)(y − a_Q)` with
     `κ_a ≥ 1`. Near a repeller it is `R(y) = r_Q + γ^(κ_r)(y − r_Q)` with `κ_r ≤ −1`.
   - `a_Q, r_Q ∈ Q` are the unique fixed points of these formulas, embedded diagonally in `Ẑ`.
     They project to `a` and `r`, so `a ≠ r` forces `a_Q ≠ r_Q`.
   - On every fibre coordinate (neutral `Z_p` or `Z_ℓ`, `ℓ ∉ S`), `ψ_n = C^(−n)R^n` has unit slope
     `γ^(n(κ_r − κ_a)) ≠ 1`, and it preserves every box of the fibre partition `Π_j` (Lemma B.3).
   - The Vandermonde argument (bases `γ^(κ_a)`, `γ^(κ_r)` and `1`, pairwise distinct) shows that
     two of `ψ_1, ψ_2, ψ_3` have distinct fixed points.
   - So every fibre depth is at most `v_p(p_n − p_(n′)) + max v_p(λ − 1)`, and every fibre modulus
     divides a computable `m*`.

The torsion part `U × Φ` splits as before: `g^N = id` on `U` means identity formulas, so
`ĝ^N = id` there. The finite search over (base candidates) × (classes mod divisors of `m*`)
decides YES. ∎

## Where the mechanism breaks

- **Mixed-sign rays and rank two.** A piece with slope `3/2` (degree change `(−1, 1)`) expands
  `Z_2` and contracts `Z_3` at once. No refinement makes `g` a tree almost-automorphism, since
  cylinders of the two primes move in opposite directions.
- **What the base can then contain.**
  - Hyperbolic invariant Cantor sets. Conway's amusical permutation (rank two) is conjugate to the
    full 3-shift (`conway-amusical-permutation-is-the-full-three-shift`), with infinitely many
    periodic orbits and no attractor–repeller decomposition.
  - Collatz-type components (`ct-z-orbit-transversal-dichotomy-is-collatz-hard`).
- **Which ingredient fails.** The finite flow decomposition, and with it the finite hull search.
  The holonomy bound itself only needs two hyperbolic fixed points with distinct rational
  locations, so it survives wherever such pairs exist.
- **The same line elsewhere.** It separates tame from Collatz-hard for Kourovka 20.44 and torsion
  (`kourovka-20-44-holds-for-rank-one-slope-groups`,
  `ct-p-z-positive-ray-torsion-and-finiteness-are-decidable`).

## Not Kohl's "respected partitions"

- **Kohl's notion.** In Kohl's RCWA theory an rcwa mapping *respects* a residue-class partition if
  it permutes the parts **and is affine on each part** (RCWA manual, `RespectedPartition`, `IsTame`).
  Such a partition exists iff the mapping is tame, i.e. has finite order in `CT(Z)`.
- **21.74(a).** It asks only that `g` **permute** the parts. The pieces of `g` may cut them.
- **Different questions.** For example, `h = ψ_{0(2)}ψ_{1(2)}` has infinite order, so it
  respects no partition, yet it permutes `{0(2), 1(2)}`. The decision procedure here is for the
  permutation question. (Distinction noted by bh-ref-q11.)

## Lesson for general BH

**For arithmetic hosts, "tree-like after refinement" is exactly "slopes on one positive ray".**
- On that side, element-level dynamics (flow components), coordinate structure (holonomy depth)
  and orbit statistics are all finite and computable.
- Off it, hyperbolicity enters the base: one prime expands while another contracts. With it come
  horseshoes and Collatz-type components.
- So a positive-ray element of `CT_P(Z)` is a V-element in disguise, with passenger fibres.
  Genuinely new behaviour in `CT(Z)` needs slopes that pull primes in opposite directions.
