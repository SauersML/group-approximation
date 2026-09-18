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

## Source re-read (lane bh-major-product, 2026-09-18)

Rybak's TeX (`km-ht/2605.14159.d/main.tex` on MSI) was re-read at the places the chain uses.
**Everything read checks. The credit is Rybak's.**
- **Theorem `real main theorem`, direction (2)⇒(1).** Topologically free on the limit set implies
  MIF (l.946–990). The argument is a complete ping-pong. It uses only:
  - density of loxodromic fixed-point pairs, Gromov / Hamann (l.401);
  - north–south dynamics (l.364);
  - the Hull–Osin reduction to one variable.
- **Lemmas used in step 3.** Non-topologically-free implies micro-supported (l.741). Rigid
  stabilizers form infinite direct sums (l.749). Torsion in a compressible rigid stabilizer gives
  wreath products, hence elements of unbounded finite order (l.758).
  - One wording point: the open set `V` built in the wreath lemma should be taken inside `U`. That
    is possible because `g ∈ rist(U)` preserves `U`, and it changes nothing.
  - The order growth is explicit. If `c` has order `m`, then (copy of `c`)`·g` has order at least
    `k m`.
- **The asymptotic-dimension step.** A properly acting finitely generated group coarsely embeds
  by its orbit map, and asymptotic dimension is monotone under coarse embeddings, so the bound
  `asdim G(F) ≤ asdim(X_+ × X_−) < ∞` holds.
- **Published inputs, cited and not read.**
  - Caprace–Fujiwara, GAFA 19 (2010), Prop. 5.3 and the proof of Cor. 1.3.
  - Petyt–Spriano–Zalloum, Adv. Math. 450 (2024), Thms. B, C, L and N.
  - Caprace, J. Algebra 317 (2007), Cor. 1.3, a uniform bound on nilpotency degree, hence bounded
    torsion.
  - Bell–Dranishnikov, Topology Appl. 155 (2008), Thm. 64.
  - Dymara–Schick, Russ. J. Math. Phys. 16 (2009).
  - Skipper–Witzel–Zaremsky, Invent. 215 (2019), last paragraph.
  - Caprace–Rémy, Invent. 176 (2009), for finite presentation and simplicity.

**Remaining trust.** The KM row now rests on Rybak's unrefereed preprint, whose steps were read
here, and on published theorems. The only step not re-derived is the curtain-model input.
