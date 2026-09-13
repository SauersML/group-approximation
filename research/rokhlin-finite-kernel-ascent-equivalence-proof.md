---
rg: 2
id: rokhlin-finite-kernel-ascent-equivalence-proof
kind: route
title: Split the W-Bernoulli shift over the section action, discard the section action by weak containment, and apply the quotient formula
target: rokhlin-finite-kernel-ascent-iff-liftable-entropy-unbounded
requires:
  - rokhlin-entropy-quotient-formula-for-finite-normal-subgroups
  - seward-weak-containment-relative-entropy-equality
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
  - seward-rokhlin-entropy-subadditivity
artifacts:
  - research/artifacts/rokhlin-finite-kernel-ascent-equivalence-2026-09-13.md
---

Sections 1 and 2 of the artifact.

1. **Section action (Lemma 1.1).**
   - The argmax in each coset is a factor map `[0,1]^W -> Ω`, so `Ω` is weakly contained in all free actions.
   - A point `w.σ = m.σ` with `π(w) ≠ 1` needs infinitely many independent coincidences of probability `1/n`, so
     `Ω` and `Ω/N` are free.
   - `σ -> σ(1_Q)` generates `Ω` with entropy `log n`.
2. **Splitting (Lemma 1.2).** `(x, σ) -> (σ, d)` with `d(q)(m) = x(σ(q)m)` is a coordinate relabelling for fixed `σ`,
   and `w.(x, σ) -> (w.σ, π(w).d)`.
3. **(a) ⇒ (c).** Seward's Theorem 1.2 with `X = (A^k)^W` and `Y = Ω` gives
   `h^Rok_W(X × Ω) >= h_W(X × Ω | B(Ω)) = k log|A|`. The quotient formula (2.1) on the `N`-quotient
   `Ω/N × ((A^k)^N)^Q` gives at least `nk log|A|`.
4. **(c) ⇒ (b).** `Ω/N × ((A^k)^N)^Q` lifts to `Ω × ((A^k)^N)^Q`. Its Rokhlin entropy over `W` is at most
   `log n + nk log|A|`, so by (2.2) the quotient has finite entropy.
5. **(b) ⇒ (a).** If `Y = X/N` with `C < h^Rok_Q(Y) < ∞`, the quotient formula gives
   `(C - r log n)/n < h^Rok_W(X) < ∞`, where `X` is ergodic because `W`-invariant sets are `N`-invariant. So
   `h_sup(W) = ∞`, and Seward's Theorem 1.10 gives maximality.
