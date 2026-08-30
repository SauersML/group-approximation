---
rg: 2
id: stw99-problem-i-quasitraces-are-traces
kind: claim
title: Every bounded quasitrace on a C*-algebra is a trace (STW Problem I, Kaplansky)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

**Problem I of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902 (v2, addenda through April 2026).**  If `τ` is a bounded quasitrace on a C\*-algebra, must
`τ` be a trace?

Kaplansky's question.  Haagerup (Adv. Math. 2014, circulated 1991) proved it for
exact C\*-algebras (STW, Theorem 8); the general case is open.  STW's footnote
152 (Thiel) notes that even for `C*_r(G)` with `G` C\*-simple it is not known
whether the unique trace is the unique quasitrace; strict comparison with
respect to the trace would give that (`stw99-xc-implies-quasitrace-for-cstar-simple`).

Unconditional permanence results include
`stw01-stable-algebras-are-bounded-quasitrace-invisible` and
`stw01-transfinite-quasitrace-invisible-filtrations`: a continuous ideal
filtration of arbitrary ordinal length is bounded-quasitrace-invisible when
all successor layers are, and quasitrace linearity then transfers from the
terminal quotient.  In particular this applies to stable successor layers
and an exact terminal quotient.  These results produce broad nonexact
positive classes but do not settle the unrestricted problem.

There is also an extension theorem which permits nonzero ideal traces.
`stw01-central-projection-ideal-extensions-preserve-qt-linearity` applies
when an ideal has an increasing approximate unit of projections central in
the ambient algebra, every central corner has quasitrace linearity, and the
quotient has quasitrace linearity.  An ambient quasitrace splits exactly
over each central projection; an ultralimit of its complementary summands
vanishes on the ideal and hence descends to the quotient.  The quotient
trace cancels the remaining additivity defect.  Exact centrality matters:
for merely quasicentral projections the complementary compression is not a
homomorphism, so its composition with a quasitrace need not be a quasitrace
and cannot simply be descended.

The centrality hypothesis itself has a strict quasitracial weakening.
`stw01-qt-central-projection-extensions-preserve-linearity`
only requires the approximate-unit commutators to lie in the intersection
of the square-null ideals of all bounded quasitraces.  For each ambient
quasitrace, the projections then become genuinely central after passage to
its own square-null quotient, and the same tail-ultralimit proof applies.
The ideal may still carry nonzero traces.  This condition is exactly what
makes every tail cut a star homomorphism in the individual quasitracial
quotient; mere quasicentrality in norm remains insufficient for this
argument.

The projectional hypothesis can also be removed.
`stw01-qt-idempotent-approximate-units-preserve-linearity` allows an
increasing positive-contractive approximate unit `(e_n)` provided its
idempotence defects and all its commutators lie in the universal bounded-
quasitrace radical.  Each `e_n` then becomes a central projection only after
passing to the square-null quotient of the quasitrace currently under study.
This applies to traced ideals with no projectional approximate unit; an
explicit example uses a scalar summand together with the stably projectionless
stable algebra `C_0((0,1]) tensor K`.  Hence the exact tail-splitting mechanism
is quasitracial idempotence, not projectionality inside the ambient algebra.
