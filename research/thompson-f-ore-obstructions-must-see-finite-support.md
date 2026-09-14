---
rg: 2
id: thompson-f-ore-obstructions-must-see-finite-support
kind: claim
title: No leading-term invariant and no division-ring overring can show that a pair in the group ring of Thompson's F has no common multiple
distinct_from:
  thompson-f-amenable-iff-group-ring-is-ore: that is the equivalence with amenability; this is a barrier on which invariants could ever produce a non-Ore pair.
  monoid-ring-no-common-multiple-iff-harmonic-splitting: that says what a non-Ore pair is equivalent to; this rules out two families of would-be certificates.
  thompson-f-cardinality-certificates-need-tower-degree: that bounds the size of counting certificates on the amenable side; this is about obstructions on the non-amenable side.
artifacts:
  - research/artifacts/hl-f-p22-invariant-2026-09-13.md
---

**ESTABLISHED** through `thompson-f-ore-obstructions-must-see-finite-support-proof` (elementary, with
one classical import; not independently reviewed; no priority claimed).

Let `K` be a field, `F` Thompson's group, and `M` its positive monoid.

1. **Bi-order.** `F` has a bi-invariant total order: `g > 1` iff the right derivative of `g` at the
   leftmost point of its support is `> 1`.
2. **Division-ring overring.** For that order, `K[F]` embeds in the Malcev–Neumann division ring
   `K((F, <))` of series with well-ordered support. There every nonzero `a, b` have the common right
   multiple `a·(a^-1 b) = b·1`. So any argument that a pair has no nonzero common multiple in `K[F]` has
   to use that `u, v` are finitely supported. It cannot factor through an injective ring homomorphism
   into a division ring.
3. **Leading terms.** For nonzero `x, y ∈ K[F]`, `max supp(x y) = max supp(x) · max supp(y)`, and the
   same holds for `min`. For any `a, b ∈ K[M]` the leading-term equation
   `max(a)·p = max(b)·q` has solutions `p, q ∈ M`, because any two elements of `M` have a common right
   multiple in `M`. So no leading-term, valuation or Gröbner-type invariant attached to one bi-order
   separates `a K[M]` from `b K[M]`.
4. **Finite linear counts.** These only certify common multiples, never their absence
   (`research/artifacts/thompson-f-ore-over-f2-2026-09-13.md` §1). Gradings reduce to such counts.

**Consequence for Guba's Problem `P_(2,2)`.** A proof that some pair has no common multiple, which would
make `thompson-f-is-not-amenable` true, must be finiteness-sensitive and infinitary. The splitting
criterion `monoid-ring-no-common-multiple-iff-harmonic-splitting` is one such formulation.
