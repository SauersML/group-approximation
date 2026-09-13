---
rg: 2
id: fp-simple-kac-moody-lattices-are-lim-free
kind: claim
title: "Rybak: the finitely presented simple non-affine Kac--Moody groups over finite fields act on a hyperbolic space with general type and topologically free on the limit set"
distinct_from:
  fp-simple-kac-moody-lattices-are-mif: that is the algebraic conclusion, MIF; this is the geometric input Rybak proves on the way, a specific general type action whose limit-set action is topologically free, which later arguments use directly.
---

**ESTABLISHED (literature import).** Let `Γ(F)` be a finitely presented Kac--Moody
group over a finite field as constructed by Caprace--Rémy [CR09], such that
`G(F) = Γ(F)/Z(Γ(F))` is an infinite finitely presented simple group. Let `X` be the
Davis realization of the building on which Rybak works, `X_D` its curtain model,
and `E(X_D)` the injective hull. Then `G(F)` acts on the hyperbolic space `E(X_D)`
with an action of general type, and the induced action on the limit set
`Λ_{E(X_D)}(G(F))` is faithful and topologically free. In Rybak's terms, `G(F)` is a
lim-free weakly hyperbolic group.

**Source.** E. Rybak, arXiv:2605.14159v3, TeX source on MSI
(`/scratch.global/sauer354/km-ht/2605.14159.d/main.tex`), proof of Proposition A
(`Kac-Moody`):
- l.1549: "We want to show that $G(F)$ is lim-free weakly hyperbolic."
- l.1557 (end of the first part): "Thus, we can pass to the space $E(X_D)$ to
  conclude that $G(F)$ is faithful weakly hyperbolic."
- l.1560: "Therefore, the action of $G(F)$ on $\Lambda_{E(X_D)}(G(F))$ is
  topologically free and, by Theorem \ref{main_theorem}, $G(F)$ is MIF."

**Proof chain, as Rybak gives it:**
1. By [CF10, Proposition 5.3] the action on one of the two buildings contains two
   rank-one elements with disjoint limit points.
2. By Petyt--Spriano--Zalloum (Theorems B, C, L, N), these become loxodromic on the
   hyperbolic curtain model and on its injective hull, with four distinct endpoints.
   So the action is of general type, and it is faithful on the limit set because
   `G(F)` is simple.
3. A limit-set action that is not topologically free would give torsion-free rigid
   stabilizers containing `Z^n` for every `n`, against finite asymptotic dimension.

The full chain, with the unchecked inputs listed, is recorded in
`fp-simple-kac-moody-lattices-are-mif`. Not re-verified here, and no independent
review.

Citation: `fp-simple-kac-moody-lattices-lim-free-citation`.
