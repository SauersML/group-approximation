---
rg: 2
id: exact-models-cannot-separate-marked-pair
kind: claim
title: No exact finite model gives two-point data at the marked pair
invalidates: [two-point-via-congruence-cuts]
distinct_from:
  marked-pair-cut-problem: that asked for the deleted set on the exact congruence models; this is its refutation, in the stronger form that covers every exact model — arbitrary finite G-sets, arbitrary stabilizers — not only the regular congruence ones.
  two-point-orbit-approximation: that quantifies over all approximately multiplicative models and remains open; this closes exactly the exact-model subclass, so whatever witnesses that claim must carry genuine multiplicativity defect.
  finite-quotient-blindness: that says the image of Γ is normal in every finite quotient; this is the quantitative consequence one level up — even with an ε-density deleted set, no genuine finite action can keep the marked cosets apart at any Kazhdan-small ε.
  coordinate-action-not-sofic: that refutes full-window injective equivariant charts for approximate actions; this refutes one-pair charts for exact actions, by expansion rather than rigidity, and neither statement implies the other.
  marked-quotients-not-lef: that is a statement about group homomorphisms — the marked quotient groups admit no exact finite models as groups, killing the via-exact-finite-models routes; this is a quantitative statement about G-set models — even a genuine action assisted by an ε-density deleted set cannot keep the two marked cosets labelled apart — and its expander mechanism has no counterpart there.
---

Let `Γ = EL_r(R_+) < G = EL_r(R) ⋊ SL_d(ℤ)` be the Kun--Thom Theorem E pair,
`(p,q) = (Γ, hΓ)` the marked pair, `h = e_12((x_1⋯x_d)^{-1})`.  Fix a finite
generating set `S_Γ` of `Γ` (`Γ` is Kazhdan, hence finitely generated) with
Kazhdan constant `κ > 0`, and set

```text
F₀ = S_Γ ∪ S_Γ^{-1} ∪ {h}.
```

**Theorem.**  There is `ε₀ > 0`, depending only on `κ` and `|S_Γ|`, such that
for every `ε < ε₀` and every **exact** model — a genuine action
`φ : G → Sym(A)` on a finite set `A`, with arbitrary stabilizers — there is
no `S ⊆ A` with `|S| > (1−ε)|A|` admitting two-point label data at `(p,q)`
for the window `F₀` in the sense of `two-point-orbit-approximation`.

Explicitly one may take `ε₀ = 1/(4K)` with `K = 1 + 4|S_Γ|/κ²`: property
(T) forces edge expansion `c₀ = κ²/2` on every Schreier graph of
`(Γ, S_Γ)` without invariant vectors, uniformly over all finite `Γ`-sets.
The constant is non-explicit only because Kazhdan constants for the Theorem
E pairs are; positivity is all the statement needs.

**Consequences.**

1. `marked-pair-cut-problem` is **false** — its regular congruence models
   are the special case `A = Q_M` — and the route
   `two-point-via-congruence-cuts` is invalidated.  The transporter girth of
   `congruence-transporter-girth` is real but cannot be converted into a
   deleted set: expansion beats girth.
2. If `two-point-orbit-approximation` is true, its witnessing models must
   carry genuine multiplicativity defect: no choice of finite group action,
   however deep, however cleverly restricted to a subset, works.  Combined
   with `witness-yields-two-point-approximation`, any Hilbert embeddable
   witness for the wreath must already be non-exact at the level of the
   underlying pair data — a structural fact about the witness search, not
   only about this lane.
3. *(Revised 2026-08-15, same day.)*  The lane closed without answering
   the sheet-expansion question: `two-point-approximation-fails` was
   established by the window-free fixed-algebra route
   (`two-point-fails-via-fixed-algebra`), which spends the `∀F ∀ε`
   quantifier on a sequence so the deleted set vanishes in the
   ultraproduct and nothing needs to expand.  The two results are
   complementary, not nested: this theorem is fixed-window with explicit
   constants but exact-models-only; that one covers all models but is
   non-constructive in the window.  Whether sheet expansion survives
   `(F,ε)`-defects remains open and is now only of independent interest
   (`kun-block-transfer-lemma`, superseded for the lane).

**Mechanism in one paragraph.**  Exactness forces the collapse
`φ(h) ∈ φ(Γ)` (conjugacy into `Γ` plus normality of the image), so the
`h`-matching `s ↦ φ(h)s` preserves every `Γ`-orbit.  On each orbit the
`S_Γ`-letters draw the Schreier graph of `Γ` on the `p`-slot, an expander by
property (T); the matching joins each `(s,q)` to `(φ(h)^{-1}s, p)`.  An
ε-density deletion cannot separate an expander into two large pieces, so for
almost every surviving `s` the slots `(s,p)` and `(s,q)` are joined through
the surviving giant component and the matching, and by
`pair-constraint-graph-criterion` the labels must agree there — against
distinctness.  The very fact that makes the pair hard to separate
(`φ(h) ∈ φ(Γ)`, the finite-quotient collapse) is what welds the two slot
sheets into one expander.

## Attempts

Not applicable — this claim is born with a complete proof
(`exact-models-cannot-separate-marked-pair-proof`); recorded here because
the statement's own history is the attack log of `marked-pair-cut-problem`:
the union-bound attempt (fails against `|F|^k` word growth), the girth
route (real, `congruence-transporter-girth`, but insufficient), and the
expander argument that closed it.
