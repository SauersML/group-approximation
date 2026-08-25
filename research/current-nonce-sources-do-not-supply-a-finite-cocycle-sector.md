---
rg: 2
id: current-nonce-sources-do-not-supply-a-finite-cocycle-sector
kind: claim
title: The current Manzoor, CDI, and MIP-star sources do not expose a non-CE finite-cocycle twisted sector
distinct_from:
  non-ce-twisted-group-factor-exists: that is the goal-equivalent positive existence claim; this is a primary-source availability audit locating which required datum is absent from each currently cited non-CE construction.
  cdi-torsionization-needs-schur-multiplier-separation: that assumes the CDI factor has already passed the projective-basis gate and isolates the downstream torsion-density test; this proves that the published construction has not reached that hypothesis and records why finite Clifford phases do not repair it.
  mipstar-does-not-supply-effective-projective-basis: that focuses on effectivity and recursive kernels; this drops effectivity entirely and audits the weaker bare finite-image cocycle endpoint.
---

**ESTABLISHED SOURCE AUDIT (2026-08-24).**  None of the currently cited
Manzoor/CDI, `MIP*=RE`, or BCS data supplies a countable group `Gamma` and a
finite-image scalar cocycle `omega` for which `L_omega(Gamma)` is non-Connes
embeddable.  The missing data occur in a strict order.

```text
(P) a multiplication-closed trace-orthonormal projective unitary basis;
(T) finite image of its scalar multiplier, or a torsion-density theorem
    for that particular projective quotient.                 (FCS1)
```

The current sources fail before, or at, `(P)`.

1. **Manzoor IRS.**  The native character is the membership character
   `chi(g)=Pr[g in H]`.  By `zero-one-irs-character-is-normal-dirac`, either
   it has a strictly intermediate coefficient, which violates the native
   projective-word law, or it is a normal Dirac character and its quotient
   group is already nonhyperlinear.  Manzoor proves the non-cohyperlinear IRS
   and the relation-factor embedding, but no unrelated projective basis of
   that relation factor.

2. **CDI envelope.**  Proposition 3.8 has an operator-valued crossed-product
   cocycle.  The exact computation
   `cdi-wreath-extension-preserves-projective-basis-gate` shows that its scalar
   projective-word gate and scalar phase group are inherited from the input
   representation; the envelope creates neither.  The standard allowed
   generator choice has an intermediate coefficient by
   `cdi-standard-generator-choice-fails-projective-gate`.  No alternative
   generating tuple satisfying `(P)` is supplied.

3. **MIP-star/BCS.**  The primary outputs are correlation/star-algebra data
   and a non-CE tracial BCS model.  They do not exhibit a projective unitary
   basis.  For the native Boolean observables,
   `twisted-group-basis-forces-affine-context-support` would force every
   context onto an affine slice, returning exactly to the linear-system
   perfect-completeness problem.  The local context/Pauli algebras are
   finite-dimensional and therefore cannot themselves carry the non-CE
   factor.

Only after `(P)` has been proved does the finite-cocycle question become the
Schur-multiplier test.  If the resulting quotient is `Gamma` with multiplier
`[omega]`, `torsion-dense-schur-multiplier-compiles-twisted-nonce` applies
exactly when

```text
[omega](R_fin(H_2(Gamma,Z)))=0.                         (FCS2)
```

Finite presentability of `Gamma` would imply `(FCS2)`, but none of the
sources constructs the projective quotient, much less proves it finitely
presented or proves its Schur multiplier residually finite.  CDI's finite or
countable scalar phase image controls the values of an already recognized
multiplier; it says nothing about `(FCS2)` before recognition.

**Finite-exponent and Clifford test.**  Pauli/Clifford packets do provide
finite projective phase groups (`mu_2` or `mu_4`) on their local matrix
algebras.  Those algebras are CE and have infinite Jones index in the known
non-CE factors.  Attaching a finite Clifford label to the source generators
  only passes to a finite-index kernel of the label grading: on words in that
  kernel the label is the identity, so the original trace coefficients return.
  If all returned coefficients were projective-regular, the kernel-generated
  algebra would be the finite-index projective core of
  `finite-index-projective-core-yields-central-witness` (finite-index CE
  permanence forces that core to remain non-CE).  This is precisely the
  additional structure whose absence from all four primary constructions is
  recorded in `primary-nonce-sources-miss-finite-index-core`.  Thus finite
Clifford phases solve `(T)` only on a finite-dimensional spectator; they do
not solve `(P)` or transfer non-embeddability to that sector.

This is not a theorem that the known factors admit no hidden unrelated
projective basis.  It is the exact source-level conclusion: no such basis,
finite multiplier, or Schur-multiplier separation is produced by the cited
constructions.  Finding any non-CE finite-cocycle twisted factor would, via
the central Fourier summand theorem, immediately give a nonhyperlinear finite
central extension.

Primary sources audited: Manzoor arXiv:2502.06697; Chifan--Drimbe--Ioana
arXiv:2205.07442, especially Proposition 3.8; Ji--Natarajan--Vidick--Wright--
Yuen arXiv:2001.04383; Paddock--Slofstra arXiv:2310.07901.

DERIVATION
finite-cocycle-source-audit-via-projective-gate-order
