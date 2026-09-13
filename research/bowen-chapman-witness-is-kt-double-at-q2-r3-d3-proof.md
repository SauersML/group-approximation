---
rg: 2
id: bowen-chapman-witness-is-kt-double-at-q2-r3-d3-proof
kind: route
title: Identify the Lean pushout with the Kun--Thom double and chain the established equivalences
target: bowen-chapman-witness-is-kt-double-at-q2-r3-d3
requires:
  - kt-wreath-hyperlinear-iff-double-hyperlinear
  - kt-q2-double-hyperlinear-iff-relative-embeddable
  - kt-free-action-hyperlinear-iff-wreath-hyperlinear
  - kt-wreath-models-never-round-on-the-vertex
artifacts:
  - research/artifacts/q34-bc-witness-hyperlinear-2026-09-12.md
  - GroupApproximation/BowenChapman/LaurentPair.lean
---

The item numbers are those of the claim.

1. **1 ⇔ 2.** Use the isomorphism `E ≅ D` from the claim (artifact §1). Hyperlinearity is invariant under
   isomorphism.
2. **2 ⇔ 3 ⇔ 4.** Apply `kt-wreath-hyperlinear-iff-double-hyperlinear` at `(2, 3, 3)`. Its hypotheses are that `q`
   is a prime power and `r, d >= 3`. `kt-q2-double-hyperlinear-iff-relative-embeddable` gives `2 ⇔ 4` separately.
3. **3 ⇔ 5.** `kt-free-action-hyperlinear-iff-wreath-hyperlinear`.
4. **3 ⇔ 6.**
   - A countable group is hyperlinear iff it has a trace-preserving homomorphism into `U(∏_U M_n)` for some
     nonprincipal ultrafilter `U`.
   - Restricting such a homomorphism of `W` to `G` gives 6.
   - Conversely, the extension in 6 is such a homomorphism of `W`.
5. **6 ⇔ 7.** `7 ⇒ 6` is immediate. `6 ⇒ 7` is `kt-wreath-models-never-round-on-the-vertex`: no wreath-extendable
   actor model has an (H1) rounding on `Γ`.

**No cycle.** None of the four premises uses this claim. `kt-wreath-models-never-round-on-the-vertex` uses only
the five rigidity claims its own route requires.
