---
rg: 2
id: ct-p-z-positive-ray-kourovka-21-74a-is-decidable
kind: claim
title: "Kourovka 21.74(a) is decidable for every g in CT_P(Z) (P finite) whose slopes lie in γ^Z for an integer γ ≥ 2 divisible by every prime dividing a modulus of g: refined along the ray, g is a Higman–Thompson element of a forest, primes outside the moduli are unit-slope fibres, and the V method goes through; with neutral primes (p ∤ γ) an attractor and a repeller can share a rational fixed point and the case is open; off the ray the base becomes hyperbolic (heuristic)"
distinct_from:
  ct-empty-z-kourovka-21-74a-is-decidable: that is the case P = ∅ (γ = 2, base the binary tree); this allows odd primes in the moduli, as long as the slopes stay on one positive ray.
  ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44: that is the orbit-transversal question (20.44) under the same ray hypothesis; this is the partition question (21.74(a)).
---

**ESTABLISHED** (lane proof). No priority claimed. **Referee (bh-ref-q11, 2026-09-19): PASS when every prime of `S` divides `γ` (no neutral primes); GAP when neutral primes occur**, at "a ≠ r forces a_Q ≠ r_Q". See the Referee section.
- **The problem.** Kourovka 21.74(a) (S. Kohl) asks whether it is decidable if a given
  `g ∈ CT(Z)` permutes a nontrivial partition of `Z` into residue classes.
- **What this settles.** (a) for every `g` whose slopes lie on one positive ray `γ^Z`, **provided
  every prime of `S` divides `γ`** (no neutral primes, `S_0 = ∅`, e.g. `S = {2, 3}` with
  `γ = 6^k`). Classes may have any moduli. This hypothesis is restored after the referee report.
- **What stays open.**
  - The neutral-prime case (`S_0 ≠ ∅`); see "The neutral-prime case".
  - 21.74(a) itself, for mixed-sign and rank-two slopes.
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
     When `S_0 = ∅`, `C` contracts every coordinate, so `a` *is* the image of `a_Q`, and
     likewise `r` is the image of `r_Q`. Hence `a ≠ r` forces `a_Q ≠ r_Q`.
   - **This step fails with neutral primes.** There `a` carries neutral digits that the image of
     `a_Q` need not carry (referee, bh-ref-q11).
   - On every fibre coordinate (neutral `Z_p` or `Z_ℓ`, `ℓ ∉ S`), `ψ_n = C^(−n)R^n` has unit slope
     `γ^(n(κ_r − κ_a)) ≠ 1`, and it preserves every box of the fibre partition `Π_j` (Lemma B.3).
   - The Vandermonde argument (bases `γ^(κ_a)`, `γ^(κ_r)` and `1`, pairwise distinct) shows that
     two of `ψ_1, ψ_2, ψ_3` have distinct fixed points.
   - So every fibre depth is at most `v_p(p_n − p_(n′)) + max v_p(λ − 1)`, and every fibre modulus
     divides a computable `m*`.

The torsion part `U × Φ` splits as before: `g^N = id` on `U` means identity formulas, so
`ĝ^N = id` there. The finite search over (base candidates) × (classes mod divisors of `m*`)
decides YES. ∎

## The neutral-prime case (open)

- **Settled since (bh-2174-rank2, 2026-09-19; lane proof, not reviewed).**
  `ct-p-z-neutral-primes-kourovka-21-74a-is-decidable` carries out the repair routes below: a
  finite test decides whether all holonomies over a component fix one rational center; if not,
  two conjugate hyperbolic holonomies bound the fibre depth; if so, any permuted partition can be
  truncated to one core ball around the center. So the positive-ray case is decidable with no
  divisibility hypothesis. The text below records the gap as it stood.

- **How the pair degenerates.** Let `p ∤ γ` divide a modulus. An attractor and a repeller can lie
  over the same `S_+` point in different neutral slices. This happens when `γ^(κ_a) ≡ 1 (mod p)`,
  so that `C` fixes many residues mod `p^(b_p)`.
- **What that does to the proof.** Then `a_Q = r_Q = q`, every `ψ_n` fixes `q`, and Lemma C gives
  no bound.
- **An example with no bound.** In the fully degenerate case every formula over `R_j` fixes one
  `q` (e.g. `g(y) = γ^(κ(y)) y` with a neutral prime). Take `ℓ` with `γ ≡ 1 (mod ℓ)`. The radial
  partitions of `Z_ℓ` around `q` are preserved to every depth, so the depth of permuted partitions
  is unbounded (referee).
- **Possible repairs.** Suggested by the referee:
  - use an edge `(r, a)` with `a_Q ≠ r_Q` when one exists;
  - otherwise use the transit holonomies `C^(−(m+n_0)) T R^m`, whose fixed points move with `m`
    unless `T(q) = q`;
  - in the fully degenerate case, prove that a permuted partition exists iff one of bounded depth
    does.
- **Why it matters.** This shared-fixed-point regime is a natural place for the slope-lattice
  conjecture (`ct-p-z-cone-avoiding-slope-lattices-trap-frozen-tails`) to have content.

## Where the mechanism breaks (heuristic)

This section is evidence, not a theorem. No off-ray element has been shown to escape every tree
structure, and no rank-two case has been shown undecidable.

- **Mixed-sign rays and rank two.** A piece with slope `3/2` (degree change `(−1, 1)`) expands
  `Z_2` and contracts `Z_3` at once. The natural refinement therefore does not make `g` a tree
  almost-automorphism, since cylinders of the two primes move in opposite directions.
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

**For arithmetic hosts, "tree-like after refinement" goes with "slopes on one positive ray".**
This is heuristic off the ray.
- On that side, with every modulus prime dividing `γ`, element-level dynamics (flow components),
  coordinate structure (holonomy depth) and orbit statistics are all finite and computable.
- Neutral primes are the first place where attractor–repeller holonomy can degenerate: a shared
  rational fixed point allows unbounded coordinate depth.
- Off it, hyperbolicity enters the base: one prime expands while another contracts. With it come
  horseshoes and Collatz-type components.
- So a positive-ray element of `CT_P(Z)` is a V-element in disguise, with passenger fibres.
  Genuinely new behaviour in `CT(Z)` needs slopes that pull primes in opposite directions.

## Referee (bh-ref-q11, 2026-09-19): PASS without neutral primes; GAP with them; the "breaks" section is heuristic

**The almost-automorphism identification: correct, and more specific than stated.**
- Every element of `CT(Z)` is piecewise canonical (`r + km ↦ s + km′`, positive slope `m′/m`).
- With slopes in `γ^Z`, the refined pieces map level-`N` classes of `F` to level-`(N+κ)` classes, and the children map canonically, since `m_((n+1)v+b) = m_v·m_(nv+b)`.
- So `g` is a canonical prefix replacement of the forest: an element of the Higman–Thompson group `V_(γ, m_b)`. It is not merely a Neretin-type almost-automorphism.
- This matters: the finite order of `g|_U`, and `ĝ^N = id` on `U × Φ`, use canonicity. A general almost-automorphism can have an infinite-order elliptic part (the odometer).
- The fibre maps have unit slope, and the parts split as (base box) × (fibre box), with finitely many base candidates since `R_j` is open.

**Transfer of the V method.**
- With no neutral primes (`S_0 = ∅`, i.e. every `p ∈ S` has `v_p ≥ 1`): `∂F = ∏_S Z_p`.
  - `C` contracts every coordinate, so the attractor `a` equals the diagonal image of `a_Q`, and likewise `r = r_Q`.
  - So `a ≠ r` gives `a_Q ≠ r_Q`. Vandermonde then applies (bases `γ^(κ_r) < 1 = 1 < γ^(κ_a)`).
  - The bound, the finite search and `⇐` go through as in the V node. **PASS.**
- **With neutral primes (`S_0 ≠ ∅`): gap.** "They project to `a` and `r`, so `a ≠ r` forces `a_Q ≠ r_Q`" holds only on the `S_+` coordinates.
  - The diagonal image of `a_Q` need not carry `a`'s neutral digits: when `γ^(κ_a) ≡ 1 (mod p)`, `C` fixes many residues mod `p^(b_p)`.
  - An attractor and a repeller can lie over the **same** `S_+` point in different neutral slices. Then `a_Q = r_Q = q`, since `Q ↪ Z_p` is injective, every `ψ_n` fixes `q`, and Lemma C gives no bound.
  - In the fully degenerate case, where every formula over `R_j` fixes a common rational `q` (for instance `g(y) = γ^(κ(y))·y` with a neutral prime), the claimed bound is false.
    - Take any `ℓ` with `γ ≡ 1 (mod ℓ)`, e.g. `ℓ = 3` for `γ = 4`. Every block preserves every ball of the radial partition of `Z_ℓ` around `q`: `q + ℓ^eZ_ℓ`, together with the depth-`(k+1)` balls of the annuli `v_ℓ(y−q) = k`, `k < e`.
    - So permuted partitions of unbounded `ℓ`-depth exist, and the step "every fibre modulus divides `m*`" fails. A bounded certificate may still exist, but the proof does not show it.
- **Suggested repair.**
  - Use an edge `(r, a)` with `a_Q ≠ r_Q` if `R_j` has one.
  - Otherwise use the transit holonomies `C^(−(m+n_0)) T R^m`, from Lemma B.3 at `x_m` and `a`. Their fixed points vary with `m` unless `T(q) = q`.
  - In the fully degenerate case, prove instead that a permuted partition exists iff one of bounded depth does.
- Until then, the node's decidability claim is established only for `S_0 = ∅`: `γ` divisible by every prime of `S`, e.g. `S = {2,3}` with `γ = 6^k`.

**"Where the mechanism breaks": heuristic, and should be labelled so.**
- The Conway amusical permutation, which is conjugate to the full 3-shift, and the Collatz-hard components show that the finite flow decomposition fails for *some* off-ray elements. That is correct evidence.
- But "no refinement makes `g` a tree almost-automorphism" and the title's "mixed-sign and rank-two slopes are **exactly** where the base becomes hyperbolic" are not proved. No off-ray element is shown to escape every tree structure, and no rank-two element is shown to be undecidable.
- Please mark the section, and "exactly" in the title, as heuristic.

*Referee follow-up (bh-ref-q11, 2026-09-19).* The fix 1ccef1e940 applies the 782528f690 repairs correctly:
- the title and "What this settles" now require every modulus prime to divide `γ`;
- the `a_Q ≠ r_Q` step is justified exactly when `S_0 = ∅`;
- the neutral-prime case is recorded as open, with the degenerate example and the three repair routes;
- the off-ray section, and the title's "heuristic", are labelled.

The PASS for the `S_0 = ∅` case stands.
