# STW ranks, comparison, and divisibility cluster audit (2026-08-30)

## Primary source

Christopher Schafhauser, Aaron Tikuisis, and Stuart White,
_Nuclear C*-algebras: 99 problems_, arXiv:2506.10902, especially Problems
XVIII, XXIII, XXV, XXVI, and XXVII.

The statements recorded in Cairn use the source's hypotheses literally:

- Problem XVIII asks whether strict comparison forces Jiang--Su stability
  for simple separable nuclear non-elementary C*-algebras.
- Problem XXIII asks whether every lower-semicontinuous affine rank function
  on the quasitrace simplex is realized by a positive element.
- Problem XXV asks whether stable rank one and a unique trace force
  Jiang--Su stability in the simple separable nuclear non-elementary class.
- Problem XXVI asks whether Cuntz-semigroup Jiang--Su absorption already
  forces algebraic Jiang--Su stability.

## Logical boundary

These problems are linked but none of the links silently solves another.
Realization of all ranks supplies divisibility; strict comparison supplies
comparison.  Together these are the two halves of purity.  Problem XXVI asks
whether the resulting Cuntz-semigroup regularity lifts to Jiang--Su
absorption, while Problem XVIII asks for that conclusion from strict
comparison alone.

In the unital stably finite setting, the established CETW theorem says that
strict comparison plus uniform property Gamma implies Jiang--Su stability.
Andrew Toms's 2026 AH example refutes universal uniform property Gamma, so
uniform Gamma can no longer be treated as an automatic universal bridge.
That counterexample does not by itself refute Problem XVIII: failure of the
sufficient intermediate property is not failure of Jiang--Su stability under
the strict-comparison hypothesis.

Andrea Vaccaro's 2026 theorem establishes uniform property Gamma for
Villadsen algebras of the first type and other stable-rank-one tracially
locally homogeneous classes.  It closes STW Problem XX, not the universal
rank, unique-trace, Cuntz-semigroup, or Toms--Winter questions recorded here.

## Repository role

This audit is shared by the Cairn records for Problems XVIII, XXIII, and XXV.
It exists to keep the hypotheses and one-way implications explicit and to
prevent the 2026 uniform-Gamma resolutions from being overextended.

## Addendum: cluster wiring and post-Toms recalibration (same day, second lane)

*This section is by the lane that authored the XVIII/XXI/XXIII--XXVIII
root drafts; it complements the audit above and postdates the Toms and
Vaccaro imports.*

### Internal wiring recorded as routes

1. **XVIII ⟹ XXVI** (`stw99-xviii-implies-xxvi`) and
   **XXVI + XXVII(1) ⟹ XVIII** (`stw99-xxvi-xxvii-imply-xviii`), via
   STW Prop `prop:cu-regular` (pure ⟺ Cu(A) ≅ Cu(A⊗Z) ⟺ strict
   comparison + ranks almost occur) plus Lin's sr1 theorem.  So
   **Toms--Winter = Winter's Cu-question + "comparison gives
   divisibility"** — an exact factorization into an ultrapower half
   (XXVI) and a Cuntz-semigroup-combinatorics half (XXVII part 1).
2. **XXIII ⟹ XXVII(1)**: exact rank realization implies almost
   realization; with strict comparison that is pureness ((7) ⟺ (5)).
3. The formerly drafted route XIX ⟹ XVIII (CETW) died with Problem
   XIX: Toms's `B` refutes the premise, so it was never landed.  What
   survives of it: XVIII is EQUIVALENT to "strict comparison ⟹ uniform
   Γ" on the stably finite nuclear class (CETW both ways), so any proof
   of Toms--Winter must now derive Γ FROM comparison.

### Toms's algebra B provably fails strict comparison

`toms-gamma-counterexample-fails-strict-comparison`: any unital simple
separable nuclear non-elementary stably finite AH algebra without
uniform Γ fails strict comparison and is not pure.  Chain: AH ⟹ ranks
almost occur (BPT) ⟹ strict comparison would give pureness
(`prop:cu-regular`) ⟹ Cu-regularity ⟹ Z-stability (Winter, since AH
has locally finite nuclear dimension) ⟹ uniform Γ (CETWW),
contradiction.  So XVIII and XXVI are structurally immune to Toms-type
AH counterexamples; an XVIII refutation needs a non-AH construction or
a failure of almost-occurrence.

### B as the universal test object for the surviving Γ problems

* **XXI** (tracial-ultrapower RR0 ⟹ Γ): open; refuted iff some
  Toms-type example has `(\bar B^{T(B)})^ω` of real rank zero — no such
  computation exists yet.
* **XXVIII** (tracial divisibility ⟹ Γ): refuted iff `B` (or a
  variant) has Winter's tracial divisibility property.  Ranks cannot
  decide this: `B` already realizes the rank consequence of tracial
  divisibility, so the order-zero form is the whole question.
* **XXVII(2)** (almost divisible ⟹ pure): `B` is not pure but has
  ranks almost occurring; if `B` is almost divisible, XXVII(2) is
  refuted outright.

### Sharp reformulations retained from the root drafts

* **XXV ⟺ "sr1 + unique trace ⟹ strict comparison"**: unique trace
  makes Γ automatic (Sato; also the finite-boundary theorem), CETW
  reduces Z-stability to comparison, Thiel makes rank realization free
  from sr1.  A counterexample needs trace-invisible perforation with
  sr1 and one trace — no known instance (V1 is Poulsen, V2 has higher
  stable rank).
* **XXVIII = Winter's step (2)** (divisibility transfer to the central
  sequence algebra) with lfnd removed; content is CENTRALIZATION of
  trace-perfect order zero maps.  Dual to XXI, whose RR0 ingredients
  are central but need SELECTION.  Both are the same CPoU-free glueing
  obstruction over a wild tracial boundary.

### The Villadsen almost-divisibility computation (XXVII(2) candidate)

STW ask whether V1 algebras without strict comparison are almost
divisible.  In the Euler calculus of the LXVI no-go
(`uniformly-doubled-rordam-steps-force-proper-infiniteness`): exact
2-divisibility of tower classes crosses the section-existence boundary
(rank = half-dimension), but almost divisibility (`ny ≤ x ≤ (n+1)y`)
carries one rank unit of slack per stage.  The naive hope that this
slack alone crosses the barrier is now REFUTED for compact witnesses:
the mod-`ell` Chern/Frobenius computation
(`stw27-coordinate-euler-slack-obstructs-compact-dividers`, second
lane's audit `stw27-villadsen-compact-divider-no-go-audit-2026-08-30.md`)
shows an `ell`-almost projection divider forces the coordinate Euler
fraction below `1/(ell+1)`, whatever the factorial divisibility of the
total rank — the analogue of LXVI's Hall bound killing the exact form.
What survives: any V1 counterexample to XXVII(2) must divide the seed
Hopf class by a genuinely NONCOMPACT soft Cuntz element, so the slack
computation has to run on the constant-rank strata of variable-rank
elements, where the Chern obstruction acts stratum-by-stratum and the
`+1` slack can move between strata.  That soft-divider question is the
remaining finite-stage hinge; the `B` test above is the independent
second verdict channel.
