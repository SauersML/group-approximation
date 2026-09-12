---
rg: 2
id: kazhdan-fd-block-representation-algebras-are-not-exact
kind: claim
title: A Kazhdan group representation with infinitely many inequivalent finite-dimensional irreducible blocks generates a non-exact C*-algebra
distinct_from:
  ozawa-leg-algebra-carries-non-amenable-trace: that shows Ozawa's leg algebra D is not nuclear, through a trace with non-injective GNS closure; this shows D is not even exact, and holds for every direct sum of finite-dimensional representations of a Kazhdan group with infinitely many inequivalent irreducible constituents.
  mf-min-tensor-exact-mf-is-mf: that is permanence of MF under spatial tensor products with exact MF algebras; this is a non-exactness certificate for the second factor that Ozawa's Kazhdan-projection construction carries.
artifacts:
  - research/artifacts/uct-ozawa-leg-exactness-2026-09-12.md
---

**ESTABLISHED (derivation `kazhdan-fd-block-algebras-not-exact-proof`).** Let `G`
be a discrete group with property (T), and let `ρ` be a direct sum of
finite-dimensional unitary representations of `G` with infinitely many pairwise
inequivalent irreducible constituents. Then `C*_ρ(G)` is not exact, and neither is
any C\*-algebra containing it.

**Instance.** For Ozawa's block representation `π = ⊕_k π_k` of `SL(3,Z)` on
`ℓ²(P²(F_{p_k})) ⊖ ℂ1`, both `D = C*(π(SL(3,Z)))` and its conjugate `D̄` are not
exact. This settles the gate recorded on `ozawa-leg-algebra-carries-non-amenable-trace`
and on `nuclear-factor-with-infinite-mf-tensor-exists`: no nuclear C\*-algebra
contains `D` or `D̄`.

**Consequence for the UCT route.** Ozawa's construction forms its spectral-gap
projection from the Kazhdan element `Σ_s σ(s) ⊗ π̄(s)`. Any second factor `C`
containing that element contains `π̄(G)`, so it is not exact. So the construction as
written cannot supply the nuclear factor that
`nuclear-non-uct-via-infinite-mf-tensor` needs.

**What this does not decide.** It says nothing about a second factor containing no
copy of `π̄(G)`. By `mf-min-tensor-exact-mf-is-mf`, an exact such factor carrying a
proper isometry would already be non-MF, which is the route premise itself.

Credit: the mechanism is Wassermann's, *C\*-algebras associated with groups with
Kazhdan's property T*, Ann. of Math. 134 (1991). It was not re-read from the source
here. Exactness is used in Kirchberg's tensor-sequence form. No novelty is claimed.
