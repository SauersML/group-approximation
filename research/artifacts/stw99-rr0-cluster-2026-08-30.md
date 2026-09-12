# STW 99-problems: the real rank zero cluster (XXIX, XXX, XXXI)

*2026-08-30 goal session.  Source: Schafhauser--Tikuisis--White,
arXiv:2506.10902 v2, section "Does real rank zero give rise to
regularity?" (labels q:RR0dichotomy, q:RR0Z, q:cu-algebraic; paper
numerals XXIX, XXX, XXXI = extraction #31–33).*

## Wiring

* XXX ⟹ XXIX (`stw99-xxx-implies-xxix`): Kirchberg's dichotomy for
  `Z`-stable simple algebras.
* Perera--Rordam's central question ⟹ XXX
  (`stw99-pr-approx-divisible-implies-xxx`): approximately divisible ⟹
  `Z`-stable (Toms--Winter CJM 2.3).  PR's own Thm 5.8 gives the
  non-central half (weak divisibility) unconditionally from RR0, so
  the entire question is a CENTRALIZATION gap — the third instance of
  the same missing glueing this session isolated at XXVIII (order-zero
  maps, trace-perfect but not central) and XXI (central projections,
  but needing uniform selection).  RR0 supplies scale-wise unital
  `M_n ⊕ M_{n+1}` embeddings; nothing known moves them to `A_ω ∩ A'`
  without dimension control.

## How the cluster meets the session's Euler calculus

The three problems triangulate the same tension: real rank zero wants
`ρ(K_0) ⊆ Aff(T(A))` dense (spectral cutting by projections), while
every known regularity counterexample mechanism (Villadsen coordinate
Euler mass, the mod-`ell` Chern thresholds landed in the XXVII lane,
Rordam's finite+infinite towers) works by keeping the projection
lattice SPARSE so characteristic-class obstructions survive.
Concretely:

* **XXIX.**  A counterexample needs finite and infinite projections
  coexisting with dense spectral cutting.  Rordam 2005 killed RR0 for
  his own mixed example; there is still NO abstract theorem "finite +
  infinite ⟹ not RR0", and that is the honest open residue — the
  OPR corona-factorization hypothesis is exactly what rules out the
  known (Euler-obstruction) mechanism, so a counterexample must invent
  a new non-CFP mechanism compatible with dense cutting.
* **XXX.**  In the sr1 + unique-trace cell the problem is EXACTLY
  "K_0 weakly unperforated" (peer node
  `stw25-real-rank-zero-k0-perforation-is-exact-obstruction`), so a
  counterexample there must hide perforation inside `ker ρ` while
  keeping `ρ(K_0)` dense: perforation classes are differences of
  same-trace projections, and the Villadsen machines produce these
  only with sparse trace values.  Either engineer density (refute) or
  prove RR0 + weak divisibility washes `ker ρ`-perforation out.
* **XXXI.**  The deciding quantity for the natural (Villadsen type II)
  test family is density of `ρ(K_0)` under coordinate-duplicating
  branch maps: dense ⟹ algebraic Cu without obvious RR0 (candidate
  refutation), sparse ⟹ the problem lives only at the sr1 boundary
  where CEI proves it.

## Status

All three roots OPEN with the above as recorded Attempts; the
Perera--Rordam central question added as its own root
(`perera-rordam-rr0-approximately-divisible`) since it is the natural
attack surface and PR's weak-divisibility theorem pins its content to
centralization.  No claims established in this wave; the wave's value
is the triangulated frontier and the identification of the
centralization gap as one recurring obstruction across XXI, XXVIII,
XXX.
