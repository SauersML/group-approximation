---
rg: 2
id: nuclear-tracial-completions-are-amenable-citation
kind: route
title: CCEGSTW Theorem 1.2 with Connes's theorem makes completions of nuclear algebras amenable
target: nuclear-tracial-completions-are-amenable
requires: []
---

**Source.** CCEGSTW, *Tracially complete C\*-algebras*, arXiv:2310.20594v6 (7 Aug 2026). MSI copy,
text extracted locally, 2026-09-13.

**Quotations.**
- **Definition 4.1:** "Let A be a C∗-algebra and let (N, Y) be a tracially complete C∗-algebra. We say
  that a c.p. map θ : A → N is tracially nuclear if there are nets of finite dimensional C∗-algebras
  Fλ and c.p. maps A → Fλ → N such that lim_λ ∥ϕλ(ψλ(a)) − θ(a)∥2,Y = 0, a ∈ A. Further, we say
  (N, Y) is amenable if idN is tracially nuclear."
- **Theorem 1.2:** "Let (M, X) be a tracially complete C∗-algebra. The following are equivalent:
  (i) (M, X) is amenable, in the sense that the completely positive approximation property holds in
  the point-∥ · ∥2,X topology; (ii) for all τ ∈ X, πτ(M)′′ is semidiscrete, in the sense that the
  completely positive approximation property holds for πτ(X)′′ in the point-weak∗ topology;
  (iii) every τ ∈ X is uniformly amenable in the sense of [15, Definition 3.2.1]."
- **Immediately after:** "In particular, via Connes’ theorem, the uniform tracial completion of a
  nuclear C∗-algebra is amenable as a tracially complete C∗-algebra."

**Why (ii) holds.**
- `A` is `‖·‖_{2,X}`-dense in the unit ball of `M`, so `π_τ(M)'' = π_τ(A)''`.
- Tracial von Neumann completions of nuclear algebras are injective, hence semidiscrete (Connes).
