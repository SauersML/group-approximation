---
rg: 2
id: stw99-problem-i-quasitraces-are-traces
kind: claim
title: Every bounded quasitrace on a C*-algebra is a trace (STW Problem I, Kaplansky)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
  - research/artifacts/stw01-asymptotic-quasitracial-cut-audit-2026-08-30.md
  - research/artifacts/stw01-sigma-unital-extension-audit-2026-08-30.md
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

Exact membership in the universal bounded-quasitrace radical can now be
removed from this mechanism.  By
`stw01-asymptotic-quasitracial-cuts-promote-linearity`, fix one bounded
quasitrace `tau`.  It is enough that the idempotence defects and commutators
of the positive approximate-unit cuts tend to zero in the `tau` square
seminorm.  In the sequence quotient associated to the coordinate
ultralimit of `tau`, the cuts become one exact central projection.  The
hereditary head is linear, while the complementary tail factors through
`A/I`; their exact sum is `tau`.  Thus any nontracial counterexample under
the head/quotient hypotheses must retain either a positive asymptotic
idempotence defect or a positive commutator defect against one fixed
ambient element.

These asymptotic hypotheses now give a full extension theorem with no
countability assumption.  By `stw01-extensions-preserve-qt-linearity`, if
both `I` and `A/I` have bounded-quasitrace linearity, then `A` has
bounded-quasitrace linearity.  For an ambient quasitrace, the ideal
restriction is a finite trace; its multiplier extension makes every
approximate-unit net asymptotically central in the associated
`2`-seminorm.  A cofinal ultrafilter turns the net into one exact central
projection in a quasitracial quotient.  No sigma-unitality or separability
of `I` or `A` is needed.  There is a real distinction from norm
quasicentrality: `stw01-separable-ideal-does-not-force-sequential-qcau`
shows that `K(H)` has no sequential quasicentral approximate unit relative
to `B(H)`, even after adjoining a scalar summand carrying a fixed nonzero
trace.

The extension theorem now iterates through arbitrary ordinal length.
`stw01-transfinite-qt-linearity-filtrations` proves that a continuous ideal
filtration of a unital algebra has quasitrace linearity whenever every
successor quotient does.  At a successor one applies the arbitrary-net
splitting only to the restriction of one fixed ambient quasitrace; this
avoids any extension claim for quasitraces on nonunital intermediate ideals.
At a limit, density and norm continuity finish, with no separability or
cofinality restriction.  Consequently every filtered counterexample already
has a counterexample successor layer; transfinite gluing cannot create the
first additivity defect.

Finally, `stw01-separable-simple-reduction` removes two further possible
sources of pathology.  The unrestricted problem is equivalent to its
restriction to separable unital simple stably finite non-elementary
C*-algebras.  Starting from the classical finite-AW*-factor witness, one
places a pair detecting nonadditivity in a separable simple subalgebra by a
recursive fullness construction.  The restricted faithful quasitrace forces
stable finiteness.  Thus neither nonseparability nor a complicated ideal
lattice is needed for a counterexample; exactness remains the missing wall.

The sharper `stw01-traceless-separable-simple-reduction` also removes every
linear trace.  In the finite AW*-factor witness, compactness of the state
space finds finitely many commutators which no state annihilates
simultaneously.  Adjoin those to a nonadditivity witness before running the
separable-simple fullness construction.  The resulting simple algebra is
stably finite and carries a faithful nontracial quasitrace, but has empty
tracial state space.  Hence even a trace cannot be assumed in the minimal
counterexample class.
