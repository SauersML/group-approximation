---
rg: 2
id: infinite-simple-quotient-count-iff-marked-limit-quotient
kind: claim
title: A finitely presented group has infinitely many finite simple quotients exactly when it maps onto an infinite marked limit of finite simple groups
distinct_from:
  convergent-quotient-count-decides-gromov-question: that turns a finite first moment of the simple-quotient count X into a quotientless hyperbolic group; this characterizes X = ∞ for one group as the existence of an infinite quotient that is a marked limit of finite simple groups, and splits it by projective degree
  linear-quotient-exclusion-lifts-from-char-zero: that decides, one degree at a time, in which characteristics a finitely presented group has nontrivial projective representations; this shows that infinitely many simple quotients of bounded projective degree force an infinite linear quotient over an ultraproduct field
  local-approximation-properties-are-marked-closed: that proves approximation properties are closed in the space of marked groups; this uses compactness of that space to find the quotient responsible for infinitely many simple quotients
artifacts:
  - research/artifacts/solve-hyperbolic-rf-simple-quotients-2026-09-13.md
---

**ESTABLISHED** (direct proof; not independently reviewed; no novelty claimed).

**Notation.**
- **Markings and X.** `F_m` is free on `a_1, …, a_m`. A marked group is `F_m/N`. For
  `Λ = F_m/N_Λ` let `X(Λ)` be the number of normal subgroups of `Λ` with finite simple
  quotient.
- **Convergence.** `N_n -> N` means: for each `w`, `w ∈ N_n` for all large `n` if `w ∈ N`,
  and `w ∉ N_n` for all large `n` if `w ∉ N`.
- **Projective degree.** `pdeg(S)` is the least `D` such that `S` has a nontrivial
  homomorphism to `PGL_D(F)` for some field `F`.

**THEOREM.**

```text
(M1) If X(Λ) = ∞, there are epimorphisms φ_n: F_m ->> S_n onto finite simple groups with
     N_Λ ⊆ ker φ_n, pairwise distinct kernels, |S_n| -> ∞ and ker φ_n -> N_∞. The group
     G_∞ = F_m/N_∞ is an infinite, locally embeddable into finite (LEF) quotient of Λ.
(M2) Let Λ = F_m/<<R>> with R finite, and let φ_n: F_m ->> S_n be epimorphisms onto
     finite simple groups with |S_n| unbounded and ker φ_n -> N ⊇ R. Then every S_n with
     n large is a quotient of Λ, and X(Λ) = ∞.
(M3) If in (M1) infinitely many S_n have pdeg(S_n) <= D, the sequence can be chosen so
     that G_∞ embeds in GL_(D^2)(K) for some field K. So Λ has an infinite quotient that
     is linear of degree D^2.
(M4) If X(Λ) = ∞ and no infinite quotient of Λ embeds in any GL_N(K), then for every D
     only finitely many simple quotients of Λ have pdeg <= D, and (M1) holds with
     pdeg(S_n) -> ∞.
(M5) Some non-elementary hyperbolic group maps onto no infinite marked limit of finite
     simple groups (for some marking) iff some infinite hyperbolic group has no
     nontrivial finite quotient.
```

**Reading.**
- For finitely presented groups, `X = ∞` is a single object: one infinite LEF quotient
  that is a marked limit of simple groups.
- (M3) and (M4) sort the family by projective degree. Bounded degree yields linear
  quotients, and everything else lives in unbounded degree.
- If `Λ` has property (T), so does `G_∞`, since (T) passes to quotients.

Proof: `infinite-simple-quotient-count-marked-limit-proof`.
