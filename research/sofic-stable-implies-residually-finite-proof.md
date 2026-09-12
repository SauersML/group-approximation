---
rg: 2
id: sofic-stable-implies-residually-finite-proof
kind: route
title: Cycle-parity separating set plus weak containment in finite actions
target: sofic-stable-implies-residually-finite
requires: []
artifacts: [notes/SOFIC_STABLE_IMPLIES_RESIDUALLY_FINITE_2026-08-14.md]
---

## Direct proof

`notes/SOFIC_STABLE_IMPLIES_RESIDUALLY_FINITE_2026-08-14.md`, Theorem 3.1.
Let `G` be countable, sofic, and stable in finite actions, and let `g != 1`.

Fix a sofic approximation `sigma_n : G -> Sym(Omega_n)`.  In each permutation
`sigma_n(g)`, discard the fixed points and take alternate points along every
remaining cycle: that gives `A_n` with `sigma_n(g)A_n` disjoint from `A_n` and
`|A_n| >= (|Omega_n| - |Fix(sigma_n(g))|)/3` (Lemma 2.1).  Asymptotic freeness
makes the fixed-point fraction vanish, so in the limit action on the
ultraproduct the set `A = [A_n]` has `mu(A) >= 1/3` and
`mu(gA intersect A) = 0` (Corollary 2.2).

Stability in finite actions says that limit action is weakly contained in the
finite `G`-actions, so with the partition `{A, complement}` and `eps = 1/12`
there are a finite `G`-set `Y` with uniform measure and `B <= Y` with
`nu(B) > 1/4` and `nu(gB intersect B) < 1/12`.  Fixed points of `g` in `B` lie
in `gB intersect B`, so `g` moves a point of `Y`; the kernel of
`G -> Sym(Y)` has finite index and misses `g`.  Every nonidentity element
therefore survives a finite quotient.

Only asymptotic freeness, the statistic-matching consequence of weak
containment, and finiteness of `Sym(Y)` are used — no cohomology, no
expansion, no standardness of the limit space.  The published statements of
this fact (Gohla--Thom section 3.2; Chapman--Dikstein--Lubotzky, crediting
Glebsky--Rivera 2009) now corroborate the node instead of supporting it.
