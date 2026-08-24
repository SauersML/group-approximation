---
rg: 2
id: stable-camouflage-groups-have-prescribed-representation-spaces
kind: claim
title: Stable camouflage groups have prescribed finite-dimensional representation spaces
root: true
artifacts:
  - research/stable-camouflage-groups-have-prescribed-representation-spaces-proof.md
requires:
  - mf-camouflage-surgery
  - mf-camouflage-surgery-preserves-matricial-stability
distinct_from:
  two-tier-matricial-invisibility: that separates exact and asymptotic visibility of two marked words; this identifies every exact representation space and, under stability, shows all asymptotic models approach those prescribed spaces.
  mf-camouflage-surgery: that gives targetwise Hom-bijections as sets; this adds topology, direct-sum and tensor compatibility, irreducible classifications, and the asymptotic consequence.
  same-bohr-and-profinite-completions-but-mf-differs: that identifies two compact completions; this identifies the entire family of finite-dimensional unitary representation spaces before completion.
---

Let `C_d(Q)` be the camouflage group and `pi_Q:C_d(Q)->Q` its split
quotient.  For every `n>=1`, precomposition is a homeomorphism

```text
Rep_n(Q)=Hom(Q,U(n))
  isomorphic to Hom(C_d(Q),U(n))=Rep_n(C_d(Q)),         (CRS1)
```

for the topology of pointwise convergence.  Its inverse is restriction
along the canonical section `s:Q->C_d(Q)`.

These homeomorphisms commute with:

1. unitary conjugation;
2. direct sums;
3. tensor products;
4. passage to invariant subspaces; and
5. characters.

Consequently `Q` and `C_d(Q)` have canonically isomorphic semirings of
finite-dimensional unitary representations, the same irreducible unitary
representations, and homeomorphic unitary character spaces in every fixed
dimension.

If `Q` is point-norm matricially stable, every operator-norm asymptotic
representation of `C_d(Q)` is pointwise close to a sequence lying in the
prescribed spaces `(CRS1)`.  Thus the exact and asymptotically correctable
finite-dimensional representation theories are both inherited from `Q`,
even when `C_d(Q)` is non-MF.

Two concrete specializations are particularly transparent.

```text
Rep_n(C_d(F_r)) isomorphic to U(n)^r,                  (CRS2)
Rep_n(C_d(Z))   isomorphic to U(n).                    (CRS3)
```

For `C_d(Z)`, every irreducible finite-dimensional unitary representation is
one-dimensional, and every operator-norm asymptotic representation is close
to a representation factoring through `Z`.  Nevertheless

```text
Rad_MF(C_d(Z))=normalClosure(d)!=1,                    (CRS4)
```

so the group is stable and non-MF.  The hidden one-word kernel is invisible
not only to all exact finite-dimensional representations but to every
asymptotic representation after correction, while the visible cyclic
representation moduli remain unchanged.
