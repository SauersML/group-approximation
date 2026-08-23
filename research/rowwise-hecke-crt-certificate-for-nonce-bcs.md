---
rg: 2
id: rowwise-hecke-crt-certificate-for-nonce-bcs
kind: claim
title: Solve the finite rowwise Hecke interpolation system for one gapped non-CE BCS
distinct_from:
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that requires exact shared marginals in one common signed corner and hence a homomorphism of the whole BCS algebra; this permits a different large right-ideal mask for every verifier row.
  canonical-high-density-local-sector-groupifier: that forces a large meet from contextwise sectors; this uses weighted independent row deficits and never forms a meet.
  free-relative-placement-closes-one-balanced-chord: that solves one marginal matching after choosing its private coordinate placement; this must retain one fixed context PVM across all of its incidences and one global involution per variable.
---

OPEN.  For one fixed finite BCS with a perfect tracial strategy and
finite-dimensional gap `Delta>0`, construct an ordinary group `Gamma` and
finitely supported elements satisfying

```text
P_(c,a)P_(c,b)=delta_(a,b)P_(c,a),     sum_a P_(c,a)=1,
B_x=B_x^*=B_x^(-1),

(q_c^pred)^2=q_c^pred=(q_c^pred)^*,
F_c q_c^pred=0,

(q_(c,x)^con)^2=q_(c,x)^con=(q_(c,x)^con)^*,
(A_(c,x)-B_x)q_(c,x)^con=0,                            (HCRT1)
```

with the strict canonical budget

```text
sum_c mu_c tau_Gamma(1-q_c^pred)
+sum_(c,x)mu_(c,x)tau_Gamma(1-q_(c,x)^con)<Delta.      (HCRT2)
```

The masks may be unrelated and noncommuting.  For a variable `x` incident
to contexts `c_1,...,c_r`, the irreducible shared-variable task is the finite
right-ideal interpolation problem

```text
B_x^2=1, B_x^*=B_x,
(B_x-A_(c_i,x))q_i=0,       i=1,...,r,                 (HCRT3)
```

with small weighted canonical codimensions.  This is the **Hecke CRT** gate.

## Attempts

- The new freedom is rowwise masks, not rowwise semantics.  Applying a
  one-overlap escape separately to different incidences is invalid if it
  changes the context PVM or constructs a different `B_x` for each edge.
- Making the `q_i` orthogonal prevents them all from having high trace;
  making them identical returns to the old common-corner holonomy problem.
- `rowwise-shared-involution-forces-pairwise-marginal-closeness` shows that
  every two incidences of one variable already satisfy a canonical `L2`
  distance bound by the sum of their mask deficits.  Thus the Hecke CRT must
  simultaneously correlate the fixed context marginals; it cannot start
  from independent packets and treat `B_x` as a later appendage.
- Literal group elements cannot provide arbitrary one-sided interpolation:
  `finite-support-one-sided-stabilizers-are-torsion` reduces equality on a
  finite-support mask to its finite stabilizer.
- A finite graph of finite packets cannot close the system with budget below
  `Delta`; `finite-edge-hnn-closures-cannot-finish-the-nonce-atlas` and
  `common-corner-literal-contexts-stop-at-bass-serre` give the existing
  hyperlinear firewalls.  The missing cell must be a genuinely multi-piece
  Hecke unitary or another non-Bass--Serre overlap relation.
- The local density/storage half is supplied by
  `affine-frobenius-packets-solve-local-row-mask-storage`.  What remains is
  one global algebraic involution per variable acting as the prescribed
  marginals on its several noncommuting large right ideals.
