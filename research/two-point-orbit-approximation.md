---
rg: 2
id: two-point-orbit-approximation
kind: claim
title: The Kun–Thom coset action admits a two-point approximation at the marked pair
root: true
distinct_from:
  coordinate-action-not-sofic: that refutes the ORBIT approximation, which asks for an injective equivariant chart of every finite window on a density-(1−ε) set of states; this asks only that ONE prescribed pair of points stay distinct, quantified over no other window, and is not known to imply it
  lamp-character-orbit-separation: that computes what a Hilbert embeddable length does on the lamps once a model is given; this asks whether the underlying site data a model would need can exist at all, and mentions no length, no character and no lamp
  finite-quotient-blindness: that says every exact finite quotient identifies the two marked cosets; this asks whether an APPROXIMATELY multiplicative model can keep them apart, which is exactly the gap that statement leaves open
  marked-double-coset-infinite-degree: that computes an exact index in the real group, `[Γ : Γ ∩ hΓh⁻¹] = ∞`, and rules out finite-degree invariant graphs; this asks nothing about the real group's indices and everything about approximate finite models, where an infinite index is no obstruction because the model need not be a quotient
artifacts:
  - docs/TRUE_LAMP_CHARACTER_ORBIT_SEPARATION.md
---

Let `Γ < G` be the Kun–Thom Theorem E pair, `X = G/Γ`, and fix the marked pair
`p = Γ`, `q = hΓ` with `h = e_12((x_1⋯x_d)^{-1})` the marked element — the
site of the wreath mark `w = a_Γ a_{hΓ}`.  Here `p ≠ q` because every element
of `Γ = EL_r(R_+)` has entries in `R_+` while `h` has the entry
`(x_1⋯x_d)^{-1} ∉ R_+`.

**Definition (two-point approximation at `(p,q)`).** For every finite `F ⊆ G`
and `ε > 0` there exist a finite set `A`, a unital `(F,ε)`-multiplicative
`φ : G → Sym(A)` in the normalized Hamming metric, a subset `S ⊆ A` with
`|S| > (1−ε)|A|`, a finite set `B`, and maps `j_s : {p,q} → B` for `s ∈ S`
with

```text
j_s(p) ≠ j_s(q),        and       j_{φ(g)·s}(x) = j_s(g⁻¹·x)
```

for all `g ∈ F`, `s ∈ S` with `φ(g)·s ∈ S`, and `x ∈ {p,q}` with
`g⁻¹·x ∈ {p,q}`.

The claim asserts that such approximations exist.

**REFUTED (2026-08-15).**  The negation claim
`two-point-approximation-fails` is established: no such approximations
exist.  Mechanism (`two-point-fails-via-fixed-algebra`): the definition's
own equivariance clause makes the `p`-label exactly `Γ`-invariant, its
truth at all windows assembles a sofic representation with a `Γ`-invariant
projection moved by `σ(h)`, and Kun--Thom Theorem 4.1 forbids that because
`h` lies in the normal closure of `Γ`.  The refutation is non-constructive
in the window; the exact-model theorem
`exact-models-cannot-separate-marked-pair` remains the fixed-window
quantitative statement.  Everything below is retained as the record of the
question as it was posed.

## Why this is not a restatement of the target

The sofic-action definition quantifies the same data over **every** finite
window `E ⊆ X`, and demands `π_s : E ↪ B` injective and equivariant for all of
`E`. This asks for `E = {p,q}` only. The equivariance clause is therefore
vacuous except for the `g ∈ F` that map the pair into itself, and no
compatibility across different windows is required. `coordinate-action-not-sofic`
refutes the universally quantified statement; it does not refute this one, and
nothing in the graph derives one from the other. The claim also names no length,
no character, no lamp group and no von Neumann algebra, so it is not
`hilbert-embeddable-witness-for-kun-thom-wreath` in different words: it is a
statement purely about the `G`-set `G/Γ`.

## Quantifier check against a dumb model

The one-point model — `A = {∗}`, `S = A`, `φ(g) = id`, `B = {0,1}`,
`j_∗(p) = 0`, `j_∗(q) = 1` — satisfies multiplicativity and distinctness
trivially. It **fails** the equivariance clause: the action is transitive, so
some `g ∈ G` has `g⁻¹·p = q`, and then `φ(g)·∗ = ∗ ∈ S` forces
`j_∗(p) = j_∗(q)`, contradicting distinctness. So the definition is not
vacuous, and the content sits exactly where it should — in the interaction of
approximate multiplicativity with the requirement that a compressor-related
pair not be collapsed.

The neighbouring degenerate reading is also excluded: dropping the density
condition on `S` would let one take `S = ∅`. The condition `|S| > (1−ε)|A|` is
what forbids that, and it is the same density condition the sofic-action
definition uses.

## Why it is the live question

Every **exact** finite quotient of `G` identifies `p` and `q`, and for this
pair that is a one-line theorem rather than a gloss: `h` is a `G`-conjugate of
an element of `Γ` (`h = u e_12(x_1) u^{-1}` for a monomial substitution
`u ∈ SL_d(ℤ)` sending `e_1` to `−(1,…,1)`), and by `finite-quotient-blindness`
the image of `Γ` is **normal** in every finite quotient, so the image of `h`
lies in the image of `Γ` and the cosets collapse: `q̄ = p̄` always.
`lamp-character-orbit-separation` shows that once a model keeps `p` and `q`
distinct as sites, a generic character orbit separates the mark by an absolute
constant, with no dilution — so the lamp side costs nothing. What remains
between the graph and Question 3.4 on this route is precisely whether
approximate multiplicativity buys what exact multiplicativity provably does
not — and "provably" is now quantitative:
`exact-models-cannot-separate-marked-pair` (2026-08-15) shows no genuine
finite `G`-action, with any ε-density deleted set at Kazhdan-small ε, admits
the label data at this pair. Any witness of this claim must therefore carry
genuine multiplicativity defect; the exact lane, including the congruence
cut problem, is closed. The prover space is bracketed from the other
degenerate end too: one-bit parity models witness this claim exactly at any
window where the transport parity extends locally additively
(`parity-flip-models-satisfy-two-point`), and they die at the explicit
thirteen-element window of `parity-trap-window`, where the marked element
is a six-letter Steinberg word in slot-fixing letters. A witness at large
windows must therefore be genuinely non-exact AND genuinely non-parity; a
refutation must amplify the six-letter odd cycle by defect-robust
expansion.

A **refutation** of this claim would close the weak-soficity route to
hyperlinearity of `W` and, by `clifford-ce-implies-bernoulli-ce`, the Clifford
lane with it.

## Pair correction (2026-08-15)

This node previously stated the marked pair as `(Γ, tΓ)` with `t` a strict
compressor.  That was the wrong pair: for any `t` with nontrivial
`SL_d(ℤ)`-component — every strict compressor in `SL_d(ℤ)` in particular —
the coset `tΓ` is **residually visible**, and the two-point approximation at
`(Γ, tΓ)` holds exactly, with `S = A` and one congruence model serving all
windows at once (`compressor-coset-two-point-exact`).  Blindness kills the
compression `tΓt⁻¹ ⊊ Γ`, not the coset `tΓ`.  The pair every finite quotient
genuinely collapses is `(Γ, hΓ)` above, because `h` — unlike `t` — lies in
the conjugacy closure of `Γ`.  The route
`witness-yields-two-point-approximation` always computed at the mark sites
`(Γ, hΓ)`, so the correction re-aligns this node with the route that feeds
it; nothing downstream consumed the old pair.

**On the reachability warning.** `bin/cairn check` reports this claim as open
but unreachable from a root, and that is correct rather than an oversight: it
is a **necessary** condition for a witness, not a prerequisite of one. Both
routes touching it — `witness-yields-two-point-approximation` from the witness
claim, and `two-point-via-congruence-cuts` from the congruence cut problem —
run *into* it. Nothing requires it, and nothing should until the converse —
the resolution question of that route's final section — is settled. If the
converse is proved, this claim becomes a genuine prerequisite and the warning
resolves itself.
