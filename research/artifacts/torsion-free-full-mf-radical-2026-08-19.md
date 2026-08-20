# Torsion-free full MF radical via Fournier--Facio and Hull--Osin

Date: 2026-08-19.

## Statement

There is a two-generated finitely presented torsion-free property-(T)
acylindrically hyperbolic group `Q` such that

```text
Res_MF(Q) = Q.
```

Equivalently, every homomorphism from `Q` to the unitary group of every norm
matrix corona is trivial.  Every nontrivial quotient `L` of `Q` again has
`Res_MF(L)=L`, hence is non-MF.

The operator-algebraic part is kernel-checked in
`GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean`.  The external boundary
is the acylindrical-small-cancellation existence step.

## 1. Fournier--Facio compression source

`fournier-facio-torsion-free-skeleton` records a finitely presented torsion-free
property-(T) group carrying the one-sided compression configuration and an
embedded finitely presented nonabelian simple torsion-free subgroup `S`.
The compression defect contains `S`.  The algebraic saturation is formalized as

```text
FournierFacioDefectData.simpleSubgroup_le_defectNormal.
```

It takes the preimage of the defect in the simple subgroup.  That preimage is
normal and contains a nontrivial commutator, so simplicity forces it to be the
whole simple subgroup.

## 2. Route the defect onto the quotient

Let `N=<<S>>`.  The established claim
`defect-normally-generates-torsion-free-quotient` and the source audit in
`notes/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md` verify the following
Hull--Osin route.

* `N` is an infinite normal subgroup of the torsion-free acylindrically
  hyperbolic source and supplies a suitable subgroup for Hull's machinery.
* Apply Hull's Theorem 7.1 to a suitable two-generator subgroup inside `N`,
  using a finite generating set of the source as the prescribed elements and
  protecting a fixed nontrivial element of `S`.
* The resulting quotient `q:G->>Q` is torsion-free and acylindrically
  hyperbolic, preserves the protected element, is two-generated and finitely
  presented, and satisfies

  ```text
  Q = q(N) = <<q(S)>>^Q.
  ```

* Property (T) passes to `Q` because it is a quotient of the property-(T)
  source.

The repository's 2026-08-15 adversarial audit records this routing statement as
`CONFIRMED`; the small-cancellation theorem itself is intentionally kept outside
the Lean trust boundary.

## 3. Full residual

The image of the compression defect is normal and contains `q(S)`.  Since
`q(S)` normally generates `Q`,

```text
q(defectNormal) = Q.
```

This is the conclusion represented in the Lean routing interfaces by
`mapped_defectNormal_eq_top`.

Apply the normal-Kazhdan compression obstruction to the mapped core with
`K=Q`.  The subgroup is normal, has property (T), and lies in the mapped defect
because that defect is all of `Q`.  Therefore every norm-corona homomorphism
kills every element of `Q`:

```text
Res_MF(Q) = Q.
```

The protected element makes `Q` nontrivial, so `Q` is not MF.

## 4. Quotient heredity

If `p:Q->>L` is any quotient, functoriality plus surjectivity gives

```text
Res_MF(Q)=Q  ==>  Res_MF(L)=L.
```

This is kernel-checked as `coronaMFResidual_eq_top_of_surjective`.  Hence every
nontrivial quotient of `Q` is again non-MF and every homomorphism from such a
quotient to an MF group is trivial.

## Trust boundary

* **Kernel-checked:** simple-factor defect saturation; mapped-defect algebra;
  normal-Kazhdan MF obstruction; full-residual functoriality; quotient
  consequences.
* **Source-audited, not formalized:** Hull/Osin production of the concrete
  quotient with torsion-freeness, finite presentation, two generation,
  acylindrical hyperbolicity, survival and normal generation.

Cairn closes the existence claim at this paper-level boundary; it does not
pretend Mathlib contains acylindrically hyperbolic small cancellation.
