---
rg: 2
id: sofic-stable-implies-residually-finite
kind: claim
title: A sofic group that is stable in finite actions is residually finite
distinct_from:
  gohla-thom-stable-base-nonsofic-extension: That is the cohomological Theorem 3.13, needing a cosystolic inequality and a non-residually-finite central extension; this is the elementary principle their section 3.2 states, with no expansion hypothesis and no central extension.
  finite-quotient-blindness: That says finite quotients of the compression pattern cannot see the mark; this is a general permanence statement about stability and soficity.
artifacts:
  - notes/SOFIC_STABLE_IMPLIES_RESIDUALLY_FINITE_2026-08-14.md
  - notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md
---

A group that is sofic and stable in finite actions is residually finite.
"Stable in finite actions" is Gohla--Thom Definition 3.7: the limit action of
any sofic approximation is weakly contained in the family of finite actions of
the group.  Any group stable in a stronger sense — flexibly, weakly flexibly,
or `rho`-stable in permutations — is stable in finite actions, so the
implication applies to all of those notions.

**PROVED IN REPO** — `notes/SOFIC_STABLE_IMPLIES_RESIDUALLY_FINITE_2026-08-14.md`.
The derivation is elementary and needs no ergodic machinery: inside any sofic
approximation, choosing alternate points along each nontrivial cycle of
`sigma_n(g)` gives `A_n` with `sigma_n(g)A_n` disjoint from `A_n` and
`|A_n| >= (|Omega_n| - |Fix|)/3`, so the limit action has a set `A` with
`mu(A) >= 1/3` and `mu(gA intersect A) = 0`.  Weak containment in finite
actions then supplies a finite action and a set `B` with `nu(B) > 1/4` and
`nu(gB intersect B) < 1/12`, so `g` moves a point of a finite `G`-set and
survives the finite-index kernel of that action.  The cycle-parity step is
what replaces a Rokhlin argument, and it sidesteps the fact that the
ultraproduct space is not standard.

**Citation, now corroboration rather than support.**  The statement is
asserted by Gohla--Thom, `arXiv:2403.09582v2` section 3.2 ("any sofic group
which is stable in finite actions must be residually finite") and by
Chapman--Dikstein--Lubotzky, `arXiv:2410.02913v2` ("as sofic stable groups are
residually finite [GR09]"), both crediting Glebsky--Rivera, *Almost solutions
of equations in permutations*, Taiwanese J. Math. 13 (2009) 493--500,
`arXiv:0709.1134`.  Both secondary statements were read from the PDFs by
`cairn-scout`.

**Primary now read (2026-08-14 scout) — and the attribution is too generous.**
Glebsky--Rivera prove:

> **Proposition 3.** If `G = <x_1,...,x_k | w_i(x_1,...,x_k) = u_i(x_1,...,x_k),
> i = 1,...,r>` is sofic and System 2 is stable, then `G` is residually finite.

with the contrapositive as the second bullet of their Theorem 2: "If the group
`G` is sofic but not residually finite, then the system (2) is unstable in
permutations."

Their "stable" is Definition 1.3: stability *of a system of equations*, with a
rate `delta_eps -> 0` independent of `n`, and the exact solution required to
lie in the **same** `S_n`.  So it is **strict** permutation stability — no
enlargement, hence not flexible — and it is a property of a **finite
presentation**, not of an abstract countable group.  Glebsky--Rivera therefore
do not prove the statement in this node's title; the Gohla--Thom form (weaker
stability notion, arbitrary countable group) is strictly stronger, and they
assert it in section 3.2 as their own observation, without proof and without a
pinpoint into Glebsky--Rivera.

This is now harmless, because the in-repo proof above discharges it.  Two
things worth keeping from the primary anyway: for a finitely presented group,
"sofic and not residually finite implies the defining system is unstable in
permutations (strict sense)" is available with **no** second-hand step at all;
and the worked example printed after their Theorem 2 calls a system "unstable
in permutations, because the corresponding group is finite", contradicting
their own first bullet — a typo in the source, so do not quote that sentence.
