---
rg: 2
id: fp-simple-kac-moody-lattices-are-mif
kind: claim
title: The finitely presented simple non-affine Kac--Moody groups over finite fields are mixed-identity-free (Rybak)
distinct_from:
  fp-simple-kac-moody-lattices-are-highly-transitive: that is the high-transitivity part of BFFHZ Question 3.6, still open; this imports Rybak's answer to its MIF part, which is formally weaker.
  burger-mozes-simple-lattices-are-highly-transitive: that is the Burger--Mozes case, handled through trees; this is the Kac--Moody case, handled through a hyperbolic curtain model of the Davis building.
---

**ESTABLISHED (literature import).** Let `Γ(F)` be a finitely presented Kac--Moody
group over a finite field as constructed by Caprace--Rémy [CR09], such that
`G(F) = Γ(F)/Z(Γ(F))` is an infinite finitely presented simple group. Then `G(F)`
is MIF, and its reduced C*-algebra is selfless.

**Source.** E. Rybak, *Boundary dynamics, triple transitivity, and mixed identities
in weakly hyperbolic groups*, arXiv:2605.14159v3, TeX source fetched on MSI on
2026-09-13 (`/scratch.global/sauer354/km-ht/2605.14159.d/main.tex`).

- Proposition A, l.251--252: "Non-affine simple finitely presented Kac-Moody
  groups over finite fields constructed in \cite{CR} are MIF, and their reduced
  $C^*$-algebras are selfless."
- l.213: "One of the applications of Theorem \ref{main_theorem}, not covered by
  \cite[Theorem B]{FMMS}, is the proof that infinite simple Kac-Moody groups over
  finite fields are MIF (see Example \ref{ex BM}). This partially answers Question
  3.6 from \cite{BFFHZ}."
- Theorem A, l.197--204: "For any faithful weakly hyperbolic group $G$, the
  following conditions are equivalent: (a) $G$ is lim-free; (b) for any general
  type action of $G$ on a hyperbolic space with trivial elliptic radical, the
  induced action on the limit set is topologically free; (c) $G$ is MIF."

**Proof chain, as Rybak gives it (l.1548--1558).**
1. `G(F)` is a non-uniform lattice in the product of its two buildings. The Davis
   realization `X` of one of them is a proper CAT(0) space, `G(F)` acts
   Weyl-transitively [CF10, proof of Corollary 1.3], and the action has two
   rank-one elements with disjoint limit points [CF10, Proposition 5.3].
2. The curtain model `X_D` of Petyt--Spriano--Zalloum (Adv. Math. 450 (2024),
   Theorems B, C, L, N) is hyperbolic, the rank-one elements act loxodromically,
   and after passing to the injective hull the action is of general type with
   trivial elliptic radical, because `G(F)` is simple. So `G(F)` is faithful weakly
   hyperbolic.
3. If the action on the limit set were not topologically free, rigid stabilizers of
   non-dense open subsets would contain infinite direct sums. Torsion there would
   give elements of unbounded finite order, contradicting Caprace (J. Algebra 317
   (2007), Corollary 1.3), so they are torsion-free. Then `Z^n ≤ G(F)` for all `n`,
   so `G(F)` has infinite asymptotic dimension (Bell--Dranishnikov, Theorem 64),
   against the finite asymptotic dimension of the product of buildings
   (Skipper--Witzel--Zaremsky; Dymara--Schick).
4. So the action on the limit set is topologically free, and Theorem A gives MIF.

**Scope.** This covers the explicit members recorded in
`km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`, whose finite
presentation and simplicity come from [CR09] Theorem 20 and Corollary 21.

**Not re-verified here:** CF10 Proposition 5.3 and Corollary 1.3; PSZ Theorems B,
C, L and N; Caprace 2007 Corollary 1.3; Bell--Dranishnikov Theorem 64; the
asymptotic-dimension bound; and the proof of Rybak's Theorem A. No independent
review.

Citation: `fp-simple-kac-moody-lattices-are-mif-citation`.
