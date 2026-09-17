---
rg: 2
id: finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite
kind: claim
artifacts: [research/artifacts/fg-subgroups-of-nv-finite-iff-germ-finite-proof-2026-09-17.md]
title: "A finitely generated subgroup of nV is finite iff it has finitely many germs at every point; a subgroup whose finite-index subgroups have finite abelianization is finite iff all its orbits on C^n are finite"
distinct_from:
  bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets: that treats one element g, where finite order is equivalent to every point being periodic with zero exponent; this treats a whole finitely generated subgroup, where the compactness step needs bounded offsets at every point and a brick-level induction over words.
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that is the open finiteness statement for Kazhdan subgroups; this is an elementary finiteness criterion, which turns that statement into a statement about orbits only (kazhdan-subgroups-of-nv-act-with-finite-orbits).
  brin-thompson-brick-charts-are-not-commensurated: that shows the set of brick charts is not commensurated by nV; this uses bricks only inside one finitely generated subgroup whose offsets are bounded, where every element acts brick by brick.
---

**OPEN.** A drafted proof is recorded as an attempt (see Attempts); it is not
established because referee lenses refuted the statement as written: the
orbits-alone clause of the title and the Addendum omit the hypothesis that `K`
is finitely generated, and without it that clause is false.

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

## Attempts

- **2026-09-17 · brick induction over words (refuted at the statement level by
  audit).** The direct proof formerly routed as
  `fg-subgroups-of-nv-finite-iff-germ-finite-proof` is kept as the attempt artifact
  `research/artifacts/fg-subgroups-of-nv-finite-iff-germ-finite-proof-2026-09-17.md`.
  Both refuting lenses found Steps 0-6 (the theorem for finitely generated `K`)
  sound. The failure is Step 7 and the title/Addendum, which drop finite
  generation. Restore the route once "finitely generated" is added to the
  Addendum and title, the finite-generation import for Kazhdan groups is added,
  the BdlHV citations are imported verbatim, and a full referee pass survives.
  Referee reasons, verbatim:
  - lens 1 (refuted): Steps 0-6 of research/fg-subgroups-of-nv-finite-iff-germ-finite-proof.md hold. I checked the brick induction, compactness (3=>2), counting (2=>1), the zero-offset local identity (1=>5), 5=>4=>3, and the coboundary max formula. The offset is well defined per coordinate, which the imported brin-thompson-exponent-cocycle-proof Step 0 provides. The first step that fails for the claim as recorded is Step 7, the addendum. It shows condition 5 and then concludes "K is finite". That uses the theorem's 5=>1 direction, which needs K finitely generated: the depth L in Steps 1 and 3 comes from a finite generating set. The claim's title states the addendum with no finite-generation hypothesis ("a subgroup whose finite-index subgroups have finite abelianization is finite iff all its orbits on C^n are finite"). Step 7 never states the hypothesis either. Stated that way it is false. Counterexample: K = direct sum over m>=0 of copies of A_5, where copy m permutes 5 of the level-(m+4) subcones of C(0^m1) by prefix replacement. K is infinite and every orbit has size at most 5. Any finite quotient kills all but finitely many factors (commuting copies of A_5 cannot share an image). So every finite-index subgroup has the form F x (direct sum of cofinitely many A_5), with finite abelianization. Stabilizer elements are also the identity near their fixed points, so condition 5 holds while K is infinite. The same gap affects the 'Kazhdan reformulation' and 'Where a counterexample must live' corollaries. They apply the addendum to 'a Kazhdan subgroup K <= nV' without importing that countable Kazhdan groups are finitely generated (BdlHV Theorem 1.3.1). The BdlHV Theorem 1.7.1 and Corollary 1.3.6 citations are marked as 'cited by number and not imported verbatim', so they fail the verbatim-citation requirement. The one downstream user, kazhdan-subgroups-of-nv-finite-from-finite-orbits, derives finite generation itself, so the damage is local. Still, the ESTABLISHED statement is false as written, and it needs 'finitely generated' added to the addendum and title plus the finite-generation import. Verdict posted to the bus (d3dd5ce4). cairn check for this claim timed out, and experiments/germ-models-2026-09-17 was not run. Files: /home/user/ga-audit-main/research/finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite.md, /home/user/ga-audit-main/research/fg-subgroups-of-nv-finite-iff-germ-finite-proof.md, /home/user/ga-audit-main/research/brin-thompson-exponent-cocycle-proof.md.
  - lens 2 (refuted): The main theorem holds, but the claim's title says more than was proved, and that broader version is false.

    Checked and correct: Steps 0-6 of research/fg-subgroups-of-nv-finite-iff-germ-finite-proof.md. These are the depth lemma, the induction over words (which needs the bound only at the single point x), compactness for 3=>2, counting bricks for 2=>1, zero offset giving local identity for 1=>5, 5=>4=>3, and the continuous coboundary from the max over K. The prerequisite brin-thompson-exponent-cocycle-proof (Step 0, the cocycle is well defined; Step 2, local identity) is COMPLETE and says what is used. The torsion, Kazhdan and full-shift corollaries are fine, and they all concern finitely generated groups.

    The failure: the title's second clause reads "a subgroup whose finite-index subgroups have finite abelianization is finite iff all its orbits on C^n are finite". The Addendum paragraph also does not restate that K is finitely generated. Step 7 needs finite generation, because it concludes "condition 5 holds, so K is finite" through Steps 1-3. Those steps need a finite generating set S with maximum depth L.

    Counterexample in V (n=1): let K be the restricted direct sum over k of copies of Alt(8). The k-th copy permutes the 8 level-3 subcylinders of C(1^k 0) by prefix replacement. The supports are disjoint, so each element is in V.
    - K is infinite.
    - Every orbit has size at most 8, and 1^inf is a fixed point.
    - Every normal subgroup of this direct sum of nonabelian simple groups is a sub-sum over an index set I. A finite-index normal subgroup therefore misses only finitely many factors, so any finite-index subgroup H has the form H_0 x (sum over I) with H_0 finite. So H^ab is finite.

    Title clause 2 therefore fails without finite generation. The fix is to add "finitely generated" to the title and to the Addendum. The body theorem with that hypothesis survives.
