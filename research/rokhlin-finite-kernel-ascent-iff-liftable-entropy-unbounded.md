---
rg: 2
id: rokhlin-finite-kernel-ascent-iff-liftable-entropy-unbounded
kind: claim
title: A finite extension W of W/N is Rokhlin-maximal exactly when the twisted section action of W/N joined with Bernoulli shifts has unbounded Rokhlin entropy
distinct_from:
  rokhlin-maximality-ascends-finite-normal-extensions: that is the open ascent from W/N to W; this proves that the ascent for a given pair is equivalent to an entropy statement about actions of the quotient alone.
  rokhlin-entropy-quotient-formula-for-finite-normal-subgroups: that compares one free W-action with its N-quotient; this uses it together with a splitting of W-Bernoulli shifts to characterize maximality of W.
artifacts:
  - research/artifacts/rokhlin-finite-kernel-ascent-equivalence-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by [[rokhlin-finite-kernel-ascent-equivalence-proof]].

Let `W` be countably infinite, `N ◁ W` finite with `n = |N|`, and `Q = W/N` finitely generated.
- **The section action.** Let `Ω` be the space of set-theoretic sections `σ : Q -> W`, with independent uniform choice
  in each coset and the action `(w.σ)(π(w)q) = w σ(q)`.
- **Lifts.** A free ergodic `Q`-action `Y` **lifts** when `Y ≅ X/N` for a free `W`-action `X`.

The following are equivalent.
- (a) `W` is Rokhlin-maximal at every `q`.
- (b) Liftable free ergodic `Q`-actions have finite but arbitrarily large Rokhlin entropy.
- (c) `sup_k h^Rok_Q(Ω/N × ((A^k)^N)^Q) = ∞` for some, equivalently every, finite `A` with `|A| >= 2`, where `Q` acts
  on `((A^k)^N)^Q` by the shift.

**Key facts** (artifact Sections 1–2).
- `Ω` is a factor of `[0,1]^W` (take the argmax in each coset), so it is weakly contained in every free `W`-action.
- `N` acts freely on `Ω`, and `Ω/N` is a free `Q`-action of entropy at most `(n + r) log n`. When the extension does
  not split, it is the shift twisted by the extension cocycle.
- **Splitting.** `A^W × Ω ≅ Ω × (A^N)^Q` `W`-equivariantly, via `d(q)(m) = x(σ(q) m)`. So
  `(A^W × Ω)/N ≅ Ω/N × (A^N)^Q`.

**Reading.** Ascent across a finite kernel asks whether the small twisted action `Ω/N` can absorb the entropy of
arbitrarily large Bernoulli shifts over the quotient. It does not ask for any Følner count along the kernel.
