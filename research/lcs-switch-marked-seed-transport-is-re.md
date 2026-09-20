---
rg: 2
id: lcs-switch-marked-seed-transport-is-re
kind: claim
title: Finite marked radical seed transport cannot certify every nonhalting output of a perfectly quantum-complete LCS compiler
distinct_from:
  monotone-mf-switch-positive-branch-barrier: That is quotient functoriality for a persistent MF mark; this permits arbitrary branch-dependent homomorphisms and uses recursive enumerability to exclude even existential finite marked transports on every nonhalting input.
  lcs-compiler-target-is-goal-equivalent: That concerns weak commuting completeness satisfied by a constant separating game; this requires a matrix-ultraproduct model preserving the halting output mark.
  reverse-kleene-does-not-remove-tv-completeness-loss: That audits changing noise and proof-gap crossings in Taller--Vidick outputs; this is independent of noise and rules out finite marked seed certificates for all nonhalting outputs.
artifacts:
  - research/artifacts/lcs-halting-switch-audit-2026-09-20.md
---

Let D be any recursively enumerable family of finite presentations K_i
with specified words j_i such that every homomorphism from K_i to every
unitary group of a tracial matrix ultraproduct kills j_i. For a group G define N_D(G) as
the normal closure of all phi(j_i), over i in D and homomorphisms
phi:K_i->G.

There is no total computable family of finite presentations G_e with
specified words J_e satisfying both:

1. If machine e halts, some homomorphism from G_e to a tracial matrix
   ultraproduct's unitary group does not kill J_e.
2. If machine e does not halt, J_e belongs to N_D(G_e).

In particular a fixed finite killed-sign seed cannot map to every
nonhalting solution group with its mark sent to the output sign, while
the halting games have quantum value one. The map need not be given
computably, injective, bounded in word length, or present on halting
inputs. A uniform soundness constant is not needed for the obstruction.

The proof enumerates finite source substitutions, finite relator
derivations and finite normal-closure certificates. These make the
predicate in clause 2 recursively enumerable. Clause 1 excludes it on
every halting index, so the two clauses would enumerate coHALT.

This is a restriction on seed-based proofs of the strong LCS endpoint,
not a refutation of that endpoint. The singleton library containing
`leavitt-central-sign-seed-for-lcs` is the motivating application, whose
analytic premise retains Liu's and the existing construction authors'
attribution. The general theorem is independent of that premise's proof.
