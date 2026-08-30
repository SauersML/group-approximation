---
rg: 2
title: STW LXXVIII finite quasitrace-obstruction audit (2026-08-30)
kind: artifact
---

# Current literature boundary

Problem LXXVIII asks whether every unital map from a unital simple separable
nuclear Z-stable algebra to a unital algebra without normalized quasitraces
is O-infinity-stable.  The cached STW v2 source, with addenda through April
2026, still states the problem as open.  Exact-phrase and concept searches
through 30 August 2026 found no later primary source claiming a solution.

The known positive comparison is Rordam's theorem that Z-stability and
O-infinity-stability coincide for traceless separable nuclear algebras.  It
does not apply to the map target here, which need be neither nuclear nor
exact nor simple.  Bosa--Gabe--Sims--White's map theorem runs in the forward
direction from O-infinity stability to nuclear dimension and likewise does
not settle the problem.

# New finite obstruction theorem

Existence of a normalized 2-quasitrace is finitely local in the following
compactness sense: if every finitely generated unital subalgebra has one,
choose one on each finite-generated stage and take a cofinal ultralimit.
Every defining identity, including the compatible `M_2` extension, involves
only finitely many elements and therefore survives.  Contrapositively, every
quasitraceless unital algebra contains a finitely generated unital
quasitraceless subalgebra.

This is stronger than separable determination.  Given any prescribed unital
subalgebra `D subset B`, adjoining the finite obstruction seed produces an
intermediate algebra containing `D` which is still quasitraceless.  Applied
to the range of an LXXVIII map, it reduces every counterexample to

```text
B_0=C*(phi(A),b_1,...,b_m).
```

Non-O-infinity-stability survives with the same positive finite-set defect,
because the admissible isometry pairs only become scarcer when the codomain
is shrunk.

# Remaining hinge

The reduction does not construct a counterexample or prove the universal
claim.  The remaining problem is now entirely separable and has a finite
quasitrace-obstruction seed.  One must either turn that finite obstruction,
together with the central Z-stability supplied by the domain, into central
Cuntz isometries, or construct a finite obstruction seed whose join with a
Z-stable image retains a finite unit.  The latter remains tied to Problem
LXVI.

# Trust boundary

The new proofs use only the defining identities of normalized 2-quasitraces,
a cofinal ultrafilter, restriction to unital subalgebras, and the already
proved exact central-isometry criterion.  No literature theorem is a premise
of either established claim.
