---
rg: 2
id: coordinate-shadows-rigidify-abelian-normalizers-in-nv
kind: claim
title: Coordinate shadows are conjugation-invariant in nV, so a block-split Z^d admits only diagonal twisting matrices and a Z^2 with a nonempty finite shadow set has an amenable normalizer image with no hyperbolic element
distinct_from:
  monomial-renormalization-compiler-gives-dilation-groups-in-nv: that constructs diagonal and monomial dilation groups; this proves that over a block-split Z^d (such as a product of SMART odometers) every twisting matrix realized by any element of nV is diagonal, so the monomial shape is forced, not a limit of the method.
  compiled-bs-stable-letters-are-never-rediagonalized: that concerns stable letters of compiled BS groups; this is an invariant on arbitrary conjugators of abelian subgroups.
  heisenberg-in-nv-forces-drift-free-central-element: that shows distorted elements have zero drift (an offset/measure invariant); this is a coordinate-projection invariant with no measure, and it kills Sol, Heisenberg and Burger-pair extensions of block-split Z^d with no distortion argument.
  brin-thompson-2v-is-not-a-t-menable: that is the negation target; this kills one class of relative-(T) witnesses for it and names the shape any survivor must have.
---

**ESTABLISHED** by `coordinate-shadows-rigidify-abelian-normalizers-proof`
(2026-09-18, swarm-0917-w12-w12-nv-pull; elementary, unreviewed by a verifier lane).

**Setting.** Let `C = {0,1}^ω` and `k >= 1`. An element `g ∈ kV` has a finite brick partition
`B_1, …, B_L` of `C^k`. On `B_i = u_1C × ⋯ × u_kC` it acts by
`(u_1w_1, …, u_kw_k) ↦ (v_1w_1, …, v_kw_k)`. Write `L(g)` for the least such `L`.

For `J ⊆ {1, …, k}`, let `pr_J` be the projection to the `J`-coordinates. The **J-shadow** of
`g` is

  `ω_J(g) = sup_{z ∈ C^k} |pr_J(⟨g⟩ z)| ∈ {1, 2, …, ∞}`.

Say `g` is **J-bounded** when `ω_J(g) < ∞`.

**Theorem.** The following hold.
- **(S1) Conjugation bound.** `ω_J(ΦgΦ^{-1}) <= L(Φ)·ω_J(g)` for all `Φ, g ∈ kV`. So J-boundedness is a
  conjugacy invariant.
- **(S2) Powers.** For `r != 0`, `g` is J-bounded iff `g^r` is.
- **(S3) Full set.** `g` is `{1..k}`-bounded iff `g` has finite order.
- **(S4) Twisting invariance.** Let `Z^d = ⟨x_1, …, x_d⟩ ≤ kV` and write `x^v = x_1^{v_1}⋯x_d^{v_d}`.
  Put `D_J = {[v] ∈ P^{d-1}(Q) : x^v is J-bounded}`. Suppose `g ∈ kV` and `M ∈ M_d(Z)` with
  `det M != 0` satisfy `g^{-1} x^v g = x^{Mv}` for all `v`. This covers normalizing elements and
  the stable letters of ascending HNN extensions (dilation codes). Then `M·D_J = D_J` for the
  projective action of `M`.
- **(S5) Finite shadow sets.** Let `d = 2`, and suppose some `D_J` is finite and nonempty. Then
  every `M` as in (S4) has a power with a rational eigenvector. In particular:
  - the normalizer image `Γ ≤ GL_2(Z)` is virtually a line stabilizer, so it is amenable
    (virtually abelian) and contains no hyperbolic matrix;
  - no Sol lattice `Z^2 ⋊_A Z` with `A` hyperbolic, and no `Z^2 ⋊ F_2` with a faithful linear
    action, extends this `Z^2` inside `kV` or inside any `nV ⊇ kV` via `g ↦ g × id`.
- **(S6) Block-split rigidity.** Suppose `{1..k} ⊇ J_1 ⊔ ⋯ ⊔ J_d` (disjoint), and each `x_i`
  acts as an infinite-order `g_i ∈ |J_i|V` on the `J_i`-coordinates and as the identity on all
  others. Then every `M` as in (S4) is **diagonal**. With coordinate permutations allowed
  (`kV ⋊ Sym(k)`), every `M` is **monomial**. The same holds for every conjugate
  `ΦZ^dΦ^{-1}`, and after stabilization `x ↦ x × id` into any `nV`.

**Consequences.**
- Products of SMART odometers `T_{m_1} × ⋯ × T_{m_d}` (in `2dV`) are block-split. So every
  dilation matrix reachable over them, by any conjugator of any Brin–Thompson group, is
  diagonal: exactly the matrices of `monomial-renormalization-compiler-gives-dilation-groups-in-nv`.
- The normalizer image of a block-split `Z^d` is contained in `{±1}^d`. So it is finite:
  - no Sol, no Heisenberg `⟨a, b⟩` with `⟨b, [a,b]⟩` conjugate to a block-split `Z^2`;
  - no Burger pair `(Z^2 ⋊ Γ, Z^2)` on such a `Z^2`.
- **Class killed.** Every relative-(T) witness for `brin-thompson-2v-is-not-a-t-menable` of
  the form `Z^2 ⋊ Γ` (`Γ ≤ GL_2(Z)` non-amenable) with `Z^2` conjugate to a block-split
  subgroup, or more generally with some `D_J` finite and nonempty, dies at (S5). The
  invariant is the J-shadow. The step where it dies is that `Γ` must permute a finite set of
  rational lines.

**Forced shape of a survivor.** A `Z^2 ≤ nV` carrying a Burger pair or a Sol lattice must be
**coordinate-mixing**: for every `J`, the set `D_J` is empty or infinite, and it is invariant
under a non-elementary (resp. hyperbolic) `Γ`. This holds for all `2^n` subsets `J`. Since
`D_{{1..n}} = ∅`, the constraint bites on the proper subsets. For `n = 2` it says: for each
coordinate `j`, either no nonzero `x^v` has uniformly bounded `j`-shadows, or infinitely many
directions do.
