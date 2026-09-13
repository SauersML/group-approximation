---
rg: 2
id: thompson-v-bernoulli-finitely-determined-iff-pos
kind: claim
title: Thompson's V has positive Rokhlin entropy exactly when some nontrivial finite-alphabet Bernoulli measure over V is finitely determined, and then all are
distinct_from:
  thompson-v-has-positive-rokhlin-entropy-action: that is the open existence claim POS(V); this proves it equivalent to finite determination of Bernoulli measures over V.
  bernoulli-measures-not-finitely-determined-at-zero-supremum: that proves non-determination at zero supremum on any group with a rigid free ergodic action; this combines it with the zero-or-infinity dichotomy and a rigid action of V into an equivalence.
---

**ESTABLISHED (unreviewed)** by [[thompson-v-bernoulli-finitely-determined-iff-pos-proof]].

"Finitely determined" is Seward's notion from `seward-bernoulli-measures-finitely-determined-under-rbs`. A
Bernoulli measure `λ^V` is nontrivial when `λ` is a probability vector on a finite set and not a point mass.

**Theorem.** The following are equivalent:
1. some free ergodic p.m.p. action of `V` has positive Rokhlin entropy (POS(V));
2. `h^Rok_sup(V) = ∞`;
3. every nontrivial finite-alphabet Bernoulli measure over `V` is finitely determined;
4. some nontrivial finite-alphabet Bernoulli measure over `V` is finitely determined.

**General form.** Let `Γ` be countably infinite with a rigid free ergodic p.m.p. action. Then 4 ⇒ 1 and
2 ⇒ 3 hold for `Γ`. If moreover `h^Rok_sup(Γ) ∈ {0, ∞}`, all four are equivalent.

**Reading.**
- This is a d-bar form of the dichotomy for `V`. Under POS(V) Seward's perturbative factor theorem makes every
  Bernoulli measure finitely determined. Without POS, models of the Gaussian rigid action of
  `thompson-v-has-a-rigid-free-ergodic-action` approach each `λ^V` weak* with the same zero Rokhlin entropy and
  stay d-bar far.
- It gives no shortcut to POS(V). At supremum `0` the entropy condition in the definition is automatic, and
  d-bar continuity fails there, so a proof of item 4 has to use a lower bound on `h_G(λ^V)`, which is the
  question itself. The open form is recorded as `thompson-v-bernoulli-measure-finitely-determined`.
- Item 1 makes `V` surjunctive and `K[V]` directly finite (`thompson-v-surjunctive-via-positive-rokhlin-entropy`).
