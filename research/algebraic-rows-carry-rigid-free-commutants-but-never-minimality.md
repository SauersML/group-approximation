---
rg: 2
id: algebraic-rows-carry-rigid-free-commutants-but-never-minimality
kind: claim
title: The square of Ledrappier's shift is a quantum-rigid zero-entropy Z^2-SFT whose automorphism group contains GL_2 of its endomorphism ring, hence F_2, all Haar-preserving; it is never minimal or free, but every closed invariant subset inherits rigidity, so target T1 is exactly an F_2-invariant, free, minimal, uniquely ergodic subset of an algebraic rigid row
requires:
  - ledrappier-crossed-product-is-finitely-presented
  - quantum-rigidity-is-product-stable
  - quantum-rigid-subshifts-cluster-the-modifications-of-each-point
  - group-subshifts-are-quantum-rigid-iff-the-lamp-group-is-fp
  - ra-forces-amenable-commutants-of-uniquely-ergodic-rigid-rows
  - two-sided-locality-holds-for-matrix-linear-automata
  - profinite-skew-layers-collapse-into-the-equicontinuous-factor
  - minimal-system-automorphisms-fix-every-proximal-factor
distinct_from:
  two-sided-locality-holds-for-matrix-linear-automata: that builds commuting free lift and transport groups on periodic data; this puts the free lift inside the automorphism group of a rigid algebraic SFT, where rigidity and an invariant measure come for free, and isolates minimality as the one missing property.
  group-subshifts-are-quantum-rigid-iff-the-lamp-group-is-fp: that shows rigid group subshifts over non-amenable groups are measure-preserving, non-amenable and never minimal; this realizes that case as the time lift of an explicit Z^2-row, and turns the minimality defect into a precise target.
---

**ESTABLISHED** (lane bh-invent-16, 2026-09-19; lane proof, elementary given the cited nodes; not
reviewed). The Pontryagin duality facts for algebraic `Z^2`-actions are recalled, not re-read
(Kitchens–Schmidt). That `GL_n` of the endomorphism ring acts on `n`-fold products is standard, and no
priority is claimed for it.

**The T1 test, end to end, on this object.**
- `F_2 ≤ Aut`: yes.
- Rigid: yes.
- Invariant measure fixed by `F_2`: yes.
- Minimal: **no**.
- Free: **no**.

## Setting

- `X_L = {x ∈ F_2^(Z^2) : x(z + e_2) = x(z) + x(z + e_1)}` is Ledrappier's shift, and `s, t` are the
  shifts by `e_1, e_2`.
- `A = F_2[s^(±1), t^(±1)] / (t − 1 − s) ≅ F_2[s^(±1), (1 + s)^(-1)]`. It acts on `X_L` by polynomials in
  the shifts, which are cellular automata.

## Statement

1. **The free commutant.** `GL_2(A)` acts on `X_L^2 = X_L × X_L` by matrices whose entries are these
   cellular automata. This gives a faithful action by SFT automorphisms, which are continuous group
   automorphisms and so preserve Haar measure. `GL_2(F_2[s]) ≤ GL_2(A)` contains a free group `F ≅ F_2`
   (Nagao, recalled).
2. **Rigidity.** `X_L^2` is quantum rigid at every scale:
   - Ledrappier's shift is rigid (`ledrappier-crossed-product-is-finitely-presented`);
   - rigidity is product-stable (`quantum-rigidity-is-product-stable`).

   It has zero entropy. Its time lift over `F × Z^2` is rigid and measure-preserving, and its acting
   group is non-amenable, so the action is not topologically amenable. It is **not minimal and not free**,
   since `0` is a fixed point. It is an instance of the fp-lamp-group case of
   `group-subshifts-are-quantum-rigid-iff-the-lamp-group-is-fp`.
3. **Minimality is the whole of T1.** Every closed invariant subset of `X_L^2` is quantum rigid
   (monotonicity, Corollary 4 of the clustering node). So T1 is achieved as soon as there is a closed
   `M ⊆ X_L^2` with these properties:
   - (i) `Z^2` acts on `M` minimally and freely;
   - (ii) `F·M = M`, and `F` acts faithfully on `M`;
   - (iii) some `Z^2`-invariant probability measure on `M` is fixed by `F`, for example because `M` is
     uniquely ergodic.

   (RA_free) concerns subshifts, not SFTs, so such an `M` is admissible. Its time lift over `F × Z^2` is
   then a minimal, free, rigid subshift with an invariant measure. That refutes (RA_free), by item 1 of
   `ra-forces-amenable-commutants-of-uniquely-ergodic-rigid-rows`.
   - *Caveat.* That node's time-lift transfer is stated for SFT rows. The proof reads the row only through
     patterns forbidden at scale `D`, so it should apply to subshifts, but this is not checked.
4. **Where `M` cannot come from.** By `profinite-skew-layers-collapse-into-the-equicontinuous-factor`
   and the squeeze nodes:
   - `M` must have infinite fibres over its maximal equicontinuous factor;
   - hierarchical (Toeplitz, or Pascal-adic self-similar) minimal subsets collapse, so `F` would act on
     them through an abelian group.

   A minimal set of `X_L^2` that is Toeplitz, or a substitution fixed point under the Frobenius
   self-similarity `x ↦ x(2·)`, never works.

## Proof

**1.**
- *Dual module.* By duality, `X_L` is the dual of the `F_2[s^(±1), t^(±1)]`-module `A`. So `a ∈ A` acts by
  zero only if `a = 0`, and `X_L^2` is the dual of `A^2`.
- *Automorphisms.* A matrix `g ∈ GL_2(A)` acts on `X_L^2` as the dual of its action on `A^2`. That is a
  continuous automorphism of the compact group `X_L^2`, and it commutes with the shifts, because `A` is
  commutative and contains them. Its entries are polynomials in `s, t^(±1)`, so it is a cellular
  automaton. Its inverse comes from `g^(-1)`.
- *Faithfulness.* The dual action of `GL_2(A)` on `A^2` is faithful.
- *Haar measure.* Continuous automorphisms of compact groups preserve Haar measure.
- `(1 + s)` is invertible in `A`, being `t`. `SL_2(F_2[s])` is a nontrivial amalgam and contains `F_2`.

**2.** As cited. Zero entropy: an `n × n` pattern is determined by its bottom row extended to length `2n`, so there are at
most `2^(2n)` of them, and `log 2^(2n) / n^2 → 0`. The time-lift statements are item 1 of the
measured node, applied without minimality, and the invariant-measure obstruction to amenability.

**3.**
- *Monotonicity.* A closed invariant subset has more forbidden patterns at every scale, so (Q3) is only
  stronger (clustering node, Corollary 4).
- *The rest.* The lift of `M` is the time lift of a rigid row: minimal because `Z^2` alone is minimal,
  free by the argument of the time-lift node (a fixed set of `g σ_p` is `Z^2`-invariant; `F` meets the central
  scalar shifts trivially, since a free group has trivial center), and carrying the
  fixed measure.

**4.** A hierarchical (Toeplitz or substitutive) minimal subset is an almost 1-1 extension of its odometer,
which is its MEF. So its fibre-preserving automorphisms are trivial, by item 5(a) of
`minimal-system-automorphisms-fix-every-proximal-factor`, and `Aut` embeds in the abelian translation group
of the odometer. Infinite profinite layers over the MEF would collapse anyway (collapse node, item 2). ∎

## Lesson for general BH

**For the time-lift face of (RA_free), rigidity, the free commutant and the invariant measure are cheap,
and only minimality is hard.**
- Algebraic rows supply all three at once: Ledrappier's square with `GL_2` of its endomorphism ring. Any
  closed invariant subset keeps rigidity.
- T1 is therefore exactly this question: **does a rigid algebraic row contain a free, minimal, uniquely
  ergodic set invariant under a free group of its algebraic automorphisms?**
- Every hierarchical minimal set is excluded by the profinite collapse. A positive answer needs a
  non-profinite almost periodic structure inside an algebraic system.

This is the sharpest form yet of bh-star-b's observation that "minimal carries the whole content of (RA)".
