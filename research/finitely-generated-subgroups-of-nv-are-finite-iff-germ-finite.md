---
rg: 2
id: finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite
kind: claim
title: "A finitely generated subgroup of nV is finite iff it has finitely many germs at every point; a subgroup whose finite-index subgroups have finite abelianization is finite iff all its orbits on C^n are finite"
distinct_from:
  bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets: that treats one element g, where finite order is equivalent to every point being periodic with zero exponent; this treats a whole finitely generated subgroup, where the compactness step needs bounded offsets at every point and a brick-level induction over words.
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that is the open finiteness statement for Kazhdan subgroups; this is an elementary finiteness criterion, which turns that statement into a statement about orbits only (kazhdan-subgroups-of-nv-act-with-finite-orbits).
  brin-thompson-brick-charts-are-not-commensurated: that shows the set of brick charts is not commensurated by nV; this uses bricks only inside one finitely generated subgroup whose offsets are bounded, where every element acts brick by brick.
---

**ESTABLISHED** (elementary; proof in
`fg-subgroups-of-nv-finite-iff-germ-finite-proof`).

**Setting.**
- `C = {0,1}^N`. A *brick* `Π_j C(a_j) ⊆ C^n` has *level* `(|a_1|, …, |a_n|)`.
- `g ∈ nV` acts on each brick of a table by prefix replacement
  `(u_j w_j)_j ↦ (v_j w_j)_j`. Its *offset* at `x` in that brick is
  `c(g)(x) = (|v_j| - |u_j|)_j ∈ Z^n`. This is the exponent cocycle `δ_g` of
  `brin-thompson-exponent-cocycle-proof`, Step 0: it is locally constant, and
  `c(gh)(x) = c(g)(hx) + c(h)(x)`.
- The *germ* of `g` at `x` is its class modulo elements that are the identity
  near `x`.

**Theorem.** Let `K ≤ nV` be finitely generated. The following are equivalent.
1. `K` is finite.
2. **Uniform bound.** `sup { |c(g)(x)|_∞ : g ∈ K, x ∈ C^n } < ∞`.
3. **Pointwise bound.** For every `x ∈ C^n`, `sup_{g ∈ K} |c(g)(x)|_∞ < ∞`.
4. **Finite germs.** For every `x`, the set of germs of elements of `K` at `x`
   is finite.
5. **Finite orbits, locally trivial stabilizers.** Every `K`-orbit in `C^n` is
   finite, and every `h ∈ Stab_K(x)` is the identity on a neighbourhood of `x`.
6. **Coboundary.** `c|_K = ∂ξ` for some bounded function `ξ: C^n → Z^n`, that is
   `c(g)(x) = ξ(x) - ξ(gx)`. When `K` is finite, `ξ` can be taken continuous.

**Addendum (orbits alone).** Suppose every finite-index subgroup of `K` has
finite abelianization. Then `K` is finite iff every `K`-orbit in `C^n` is
finite. In particular this holds when `K` has property (T), since finite-index
subgroups of Kazhdan groups are Kazhdan and Kazhdan groups have finite
abelianization (Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*,
Theorem 1.7.1 and Corollary 1.3.6; textbook facts, cited by number and not
imported verbatim).

**Corollaries.**
- **Kazhdan reformulation.** For a Kazhdan subgroup `K ≤ nV`: `K` is finite iff
  for every `x` the quasi-regular representation `ℓ^2(Kx)` has almost invariant
  vectors, for example when the Schreier graph of `K` on `Kx` is amenable. Such
  vectors force an invariant unit vector, which is constant on the transitive
  set `Kx`, so `Kx` is finite.
- **Torsion.** A finitely generated torsion subgroup of `nV` is finite iff all
  its orbits are finite. At a fixed point an element of finite order has zero
  offset, hence trivial germ.
- **Where a counterexample must live.** An infinite Kazhdan subgroup of any `nV`
  has an orbit `Kx` whose Schreier graph has a spectral gap, and `c` is unbounded
  at `x`. This removes every construction whose subgroups have only amenable
  orbit graphs. For example, the topological full group of the full shift inside
  `2V` has orbits inside `Z`-orbits with bounded jumps. The bandwidth and
  spectral-gap count of Attempt (b) on `kazhdan-subgroups-of-brin-thompson-groups-are-finite`
  is then unnecessary.
