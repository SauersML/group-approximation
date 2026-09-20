---
rg: 2
id: char-2-benoist-quint-for-free-groups-on-ledrappier-rows
kind: claim
title: (BQ_2, open crux) For a free subgroup F of GL_2(A) acting with the shifts on Ledrappier's square, every ergodic probability measure invariant under F × Z^2 is Haar measure on a coset of a closed subgroup; if true, the algebraic route to T1 is dead, and if it fails with a Z^2-minimal support, (RA_free) is refuted
requires:
  - algebraic-t1-needs-failure-of-char-p-measure-rigidity
  - algebraic-rows-carry-rigid-free-commutants-but-never-minimality
distinct_from:
  algebraic-t1-needs-failure-of-char-p-measure-rigidity: that proves the implication (BQ_2) ⇒ no algebraic T1 and rules out the natural candidates; this states (BQ_2) itself as the open crux, records the literature status, and separates the two outcomes.
---

**OPEN.** Crux for the time-lift face of (RA_free) on algebraic rows (lane bh-invent-16, 2026-09-19).

## Statement

`X = X_L^2`, `A = F_2[s^(±1), (1+s)^(-1)]`, `F ≤ GL_2(A)` free of rank 2, `Γ = F × Z^2`. **(BQ_2):** every
`Γ`-invariant ergodic Borel probability measure on `X` is **algebraic**, meaning Haar measure on a coset of
a closed subgroup.

Natural strengthenings are:
- the stationary version, for random walks on `F`;
- the same statement for every free (or Zariski-dense) `F ≤ GL_n(A)` on `X_L^n`, and for other
  zero-dimensional algebraic `Z^d`-actions.

## The two outcomes

- **(BQ_2) true.** No free, minimal subset of `X` is invariant under `F` with an `F`-fixed invariant measure
  (`algebraic-t1-needs-failure-of-char-p-measure-rigidity`, item 2). The algebraic route to T1 is dead, and
  T1 and T2 must use non-algebraic rows. If the strengthenings also hold, this covers every algebraic
  rigid row.
- **(BQ_2) false, via a non-algebraic ergodic `ν` whose support is `Z^2`-minimal and free.** Then
  `M = supp ν` satisfies (i)–(iii) of `algebraic-rows-carry-rigid-free-commutants-but-never-minimality`:
  - (ii) holds because the support of a `Γ`-invariant measure is `F`-invariant;
  - (iii) holds because `ν` itself is `F`-fixed.

  So T1 holds, and (RA_free) is refuted. **Scope:** `M` need not be an SFT, and rigidity ⇒ finite
  presentation is proved on main only for SFTs. Refuting (RA_free) this way gives no finitely presented
  group for BH until `M` is shown to be sofic or of finite type. The time-lift transfer for subshift rows was confirmed by bh-ref-t0 (ba95be4ac). A non-algebraic `ν` with a non-minimal support does not suffice by
  itself.

## Evidence

- **For rigidity.**
  - Benoist–Quint (Lie groups, homogeneous spaces) and Bourgain–Furman–Lindenstrauss–Mozes (`SL_d(Z)` on
    tori): non-abelian, Zariski-dense groups of automorphisms force invariant measures to be algebraic.
  - `F` is Zariski dense in `SL_2` over `F_2(s)`, so this is the natural analogue.
- **Against rigidity.**
  - In positive characteristic, `Z^d`-invariance alone is far from rigid: Einsiedler (2004) found
    non-algebraic closed invariant sets and measures.
  - Frobenius self-similarity `x ↦ x(2·)` is an extra non-algebraic symmetry with no counterpart over
    `R`.
  - Invariant measures of zero entropy are abundant for the abelian action.
- **Literature.** No positive-characteristic analogue for non-amenable automorphism groups of compact
  zero-dimensional groups was found (checked 2026-09-19): searches on Benoist–Quint over function fields,
  BFLM analogues, and measure rigidity for algebraic cellular automata (Sablik; Pivato; Einsiedler–Ward).
  Sablik's results concern abelian `N × Z` actions and need positive entropy.

## First tests

1. **Stationary measures of zero entropy.** Can a Frobenius-invariant (self-similar) measure also be
   `F`-invariant? Frobenius commutes with `F` only up to the ring map `s ↦ s^2`. So an `F`-invariant
   self-similar measure would need `F` stable under that map, as for `GL_2(F_2[s])`. That makes the
   question concrete.
2. **Topological version.** Is every closed `Γ`-invariant subset of `X` a finite union of cosets? This is
   a Berend-type statement. If it holds, T1 fails on `X` even without measures.

## Lesson for general BH

On algebraic rows, the time-lift face of (RA_free) is **exactly** a positive-characteristic
homogeneous-dynamics rigidity question for a free group of automorphisms. The relevant object is a free
subgroup of `SL_2(F_2[s])` acting, together with the shifts, on the dual of `A^2`. A theorem there, in
either direction, decides whether algebraic rigid rows can carry a minimal free commutant.

## S-arithmetic form, and the natural attack route (added 2026-09-19)

- **Identification (standard adelic duality, recalled).** `A = F_2[s, s^(-1), (1+s)^(-1)]` is the ring of
  `S`-integers of `F_2(s)` for `S = {s = 0, s = 1, s = ∞}`. It is a cocompact lattice in `K_S = ∏_(v∈S) K_v`,
  and `X_L ≅ K_S / A` as compact groups. The shifts act by multiplication by the units `s` and `1 + s`.
  So `X = X_L^2 ≅ K_S^2 / A^2`, an **`S`-arithmetic solenoid in characteristic 2**. `F ≤ SL_2(A)` acts
  linearly, and (BQ_2) is the characteristic-2 analogue of the torus case of Benoist–Quint and of
  Bourgain–Furman–Lindenstrauss–Mozes, with extra diagonal units.
- **Route.**
  - (a) An exponential-drift argument in positive characteristic, making `F`-stationary measures invariant
    under a unipotent subgroup. This is not found in the literature.
  - (b) Positive-characteristic rigidity of measures invariant under unipotent or semisimple subgroups:
    Einsiedler–Ghosh, Proc. LMS 100 (2010); Mohammadi (horospherical); Einsiedler–Lindenstrauss–Mohammadi
    (diagonal actions). These are recalled from titles and abstracts, not read.
- **Lane decision.** This is deep positive-characteristic homogeneous dynamics. bh-invent-16 leaves it
  as a crux and pivots to non-linear two-sided locality (T2). T2 is what BH needs, since algebraic rows
  lift only exact groups.

## Attempts

- **bh-bq2 (2026-09-19): statement corrected, crux sharpened; still open.**
  - *The one-coset form is false for every `F`.* Orbits of period-3 points have size divisible by 3.
  - *Frobenius-twisted `F ≤ GL_2(A')` carry a positive-entropy, non-Haar, homogeneous four-subgroup measure.*
  - *The correct statement is (BQ_2'),* with Haar measure on one `Γ`-orbit of cosets. It still rules out
    algebraic T1.
  - *Under the non-square-trace condition (NS)*, (BQ_2') is equivalent to: every ergodic measure of infinite
    support is invariant under infinitely many translations.

  See `char-2-benoist-quint-needs-the-homogeneous-form`. Any T1 set must carry a free, uniformly distal action
  of `F ∩ SL_2(A)`, with `[F, F]` acting inside the equicontinuous fibres; see
  `algebraic-t1-sets-carry-free-distal-commutator-actions`. Neither outcome of (BQ_2') is proved.
