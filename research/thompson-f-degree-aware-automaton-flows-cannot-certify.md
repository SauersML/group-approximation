---
rg: 2
id: thompson-f-degree-aware-automaton-flows-cannot-certify
kind: claim
title: No expansion certificate on Thompson's group F can be computed from a finite tree automaton profile, the number of trees and the total caret count, even when it reads the negative part of the element arbitrarily
distinct_from:
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that kills rules on the positive monoid reading only a finite automaton profile and the number of trees; this adds the total caret count (degree), which has no idempotent measure, and lifts the kill from flows on M to flows on the whole group F, with arbitrary dependence on the negative part of the normal form.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that is the doubling criterion; this constrains which data a flow certificate for it must read.
  thompson-f-moment-data-cannot-certify-nonamenability: that is about finitely many return probabilities; this is about local transport rules.
  thompson-f-evacuation-schemes-need-capacity-three: that bounds capacities on one Cayley graph; this is capacity-independent.
artifacts:
  - experiments/thompson-f-degree-aware-flow-certificates-2026-09-17/check_pumped_leaf_model.py
  - experiments/thompson-f-degree-aware-flow-certificates-2026-09-17/output.txt
---

**ESTABLISHED** through `thompson-f-degree-aware-automaton-flows-cannot-certify-proof`
(direct proof; imports only Brouwer's fixed point theorem and, for one example, the
Cannon–Floyd–Parry normal form; not independently reviewed; no priority claimed).

**Setting.** `M` is the positive monoid of `F`, identified with forests `y = (t_0, t_1, ...)` of finite
binary trees, almost all trivial, where `x_k` merges roots `k` and `k+1`
(`thompson-f-finite-state-flows-cannot-prove-nonamenability`, Lemma 1.1 of its proof). For `y ∈ M`:
- `N_y` is the number of trees up to the last nontrivial one;
- `deg y` is the total number of carets, which equals the word length of `y` in the `x_i`;
- `p(y) = (q(t_0), q(t_1), ...)` is the profile of a finite tree automaton `(Q, δ, ℓ)`, meaning
  `q(•) = ℓ` and `q(L ∧ R) = δ(q(L), q(R))`.

A *certificate on F* for a finite `S ⊆ F` and `λ > 0` is a function `w : S × F → [0, ∞)` with
- (out) `Σ_(s ∈ S) w(s, g) >= λ` for every `g ∈ F`;
- (in) `Σ_(s ∈ S) w(s, s^-1 h) <= 1` for every `h ∈ F`.

A certificate with `λ > 1` gives `|S Y| >= λ|Y|` for all finite `Y ⊂ F`, so `F` is not amenable.
Conversely, if `F` is not amenable, `{0,1}`-valued certificates with `λ = 2` exist on `M`, by Lemma 2.1(b)
of the proof of `thompson-f-finite-state-flows-cannot-prove-nonamenability`.

**Theorem.**
- *Monoid form.* Let `S ⊆ M` be finite, `(Q, δ, ℓ)` a finite tree automaton and `G >= 0` arbitrary. The rule
  `w(s, y) = G(s, p(y), N_y, deg y)` on `M` satisfies `sup_z (in-sum at z) >= inf_y (out-sum at y)`.
- *Group form.* Let `S ⊆ F` be finite and `Ψ : F → X` any map whose restriction to `M` is a function of
  `(p(y), N_y, deg y)` for one finite automaton. No certificate on `F` of the form
  `w(s, g) = G(s, Ψ(g))` has `λ > 1`.

*Example of the group form.* Write `g = p_g q_g^-1` in Cannon–Floyd–Parry normal form. Any rule reading
- the automaton profile, the tree count and the caret count of the positive part `p_g`, and
- anything at all about the negative part `q_g`

is excluded. On `M` the normal form is `(y, 1)`, so the hypothesis holds.

**Mechanism (the pumped leaf model).**
- *Why the old model fails.* In the random forest of the earlier theorem, splitting changes
  `(N, deg)` by `(+d, −d)`. The total leaf count `Λ = N + deg` is split-invariant, but in that model `Λ` is
  tied to `N`, and a rule reading `(N, Λ)` sees the difference.
- *Pump.* Let `f = δ(ℓ, ·)`, with preperiod `j0` and period `m`. The right vines with `j0` and `j0 + m`
  carets have the same state and the same leaf count mod `m`, and differ by exactly `m` leaves.
- *Refined automaton.* Pass to `Q × Z/m`, which records leaf counts mod `m`, and put an idempotent measure
  `π` on the states of trees that contain the shorter vine.
- *Random pumps.* Each hung tree independently gets the longer vine with probability 1/2. This leaves
  every state unchanged and adds `m · Binomial` to `Λ`.
- *Estimate.* Given the profile, splitting changes only a bounded part of `Λ`, with the right residue
  mod `m`, while `Λ` contains a Binomial with `≳ N` trials. So the conditional laws of `Λ` differ by
  `O(1/√N)` in total variation. The averaging principle then gives inflow `>=` outflow.
- *Group form.* Pass from `F` to `M` by right-translating `S` into `M` (common right multiples).
  Averaging only at points of `M` needs nothing about the rule off `c M`.

**Where the method sits.**
- *Covered, read jointly:* all tree states of any finite automaton, the number of trees, the total caret
  count and anything about the negative part of the normal form. On `M` this includes the word length.
- *Gate, unchanged:* per-tree unbounded data such as individual sizes, depths or exact shapes. A
  certificate, if one exists, must read such data about the positive part.
- *Calibration.* In the free group with `S = {a, b}`, `w ≡ 1` is a certificate. The proof does not apply
  there, because `aM ∩ bM = ∅` in the free monoid. The coin is necessary: without it the check script
  finds total variation 1 at every `N` for single-state automata, where `Λ` becomes a function of `N`.

**Scope.** This proves neither answer to `thompson-f-is-not-amenable`. It kills a wider class of
witnesses than `thompson-f-finite-state-flows-cannot-prove-nonamenability`.

**Check.** The artifact script checks the following.
- *Pump and measure.* The pump identity and an idempotent `π` (residual `<= 1.1e-16`) for 6 automata:
  leaves mod 2, depth truncated at 2, "is a right vine", and three random ones.
- *Brute force.* For `N = 2`, `H = 2` and `s = x_0, x_1`, it enumerates every forest of the model and
  applies the splits. The law of (refined profile, `N`, degree) equals the predicted product law exactly
  (difference `0`), and `N` and the degree shift by `+d` and `−d`.
- *Exact total variation.* It computes the total variation between the Ψ-laws for `s = x_1` (`n` up to
  64, and up to 512 for one-state supports) and for `s = x_0 x_2` (`n` up to 32, and up to 128 for
  one-state supports). Every value lies below the proof's bound, and `√n · TV` levels off (for leaves
  mod 2: 1.41, 1.57, 1.67, 1.72, 1.75).
- *Control.* Without the coin, the total variation stays 1 for the one-state automata ("depth truncated
  at 2" and "is a right vine"). For leaves mod 2 it still decays, to 0.29, because there the `T0` sizes
  already differ by state.
