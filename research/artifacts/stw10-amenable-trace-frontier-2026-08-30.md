---
rg: 2
title: STW X(1) amenable-versus-quasidiagonal trace frontier (2026-08-30)
kind: artifact
---

# Status and primary-source screen

STW Problem X(1) asks whether every amenable trace on a C*-algebra is
quasidiagonal.  A primary-source search through 30 August 2026 found no
general solution or counterexample.  The full-group-algebra candidate already
in the graph remains conditional: its canonical trace is proved non-QD, but
amenability still requires the literal group's open factorization property.

The main positive sources remain Brown's foundational memoir
arXiv:math/0304009v2, Tikuisis--White--Winter and Gabe for separable exact UCT
algebras, and Gabe's cone theorem.  Neagu, arXiv:2211.01666, proves homotopy
invariance in a separable exact faithful-amenable setting.  Shulman,
arXiv:2508.00125 (31 July 2025), proves a newer homotopy-domination theorem:
if either `A` or `B` is exact, `A` is homotopy dominated by `B`, and all
amenable traces on `B` are QD, then the same holds for `A`.  None of these
sources claims the universal assertion.

# New local permanence

`directed-unions-preserve-trace-approximations` proves that amenability and
quasidiagonality of a trace are each equivalent to the same property on every
member of a unital directed dense family.  The proof extends a stage u.c.p.
map to the ambient algebra and tracks finite-set errors; it does not assume
exactness.  Applied to full group algebras, this makes both Kirchberg's
factorization property and QD of the canonical full-group trace finitely
local.

The contrapositive recovers the separable reduction: an amenable non-QD trace
restricts to an amenable non-QD trace on some separable unital subalgebra.

# GNS kernels and quotient boundary

For exact `A`, the GNS quotient `A -> A/ker(pi_tau)` is locally liftable, so
amenability descends to the induced faithful trace; QD of that faithful trace
pulls back by composition.  This is the precise faithful-trace reduction used
by STW.  It does **not** say that a QD trace on `A` descends to its GNS image.

Nonexactness permits genuine failure of amenability descent.  If `G` is
nonamenable and has the factorization property, the canonical trace is
amenable on `C*(G)` but not on `C*_r(G)`.  Hence the regular quotient is not
locally liftable.  The free group `F_2` gives an unconditional example: its
residual-finiteness approximations make the full canonical trace QD, while an
amenable reduced canonical trace would give a left-invariant mean on `G`.

This phenomenon is a fence, not a counterexample to X(1): the full canonical
trace of `F_2` is QD.  It explains why quotienting an amenable trace to its
faithful GNS image is illegitimate without exactness or a lifting hypothesis.

# Trust boundary

Imported results are Brown's equivalence between factorization and amenability
of the full canonical trace, the local-lifting amenable-descent theorem, and
the Effros--Haagerup local-lifting consequence for exact quotients.  The
directed-union finite-set proof, full-group-algebra directed-union
identification, residual-finiteness model for `F_2`, and invariant-mean
argument for the reduced trace are explicit in their routes.  No open
factorization premise is used in any established claim here.
