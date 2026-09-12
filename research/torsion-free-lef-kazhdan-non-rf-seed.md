---
rg: 2
id: torsion-free-lef-kazhdan-non-rf-seed
kind: claim
title: A torsion-free LEF Kazhdan group can fail residual finiteness
distinct_from:
  thom-hyperlinear-kazhdan-without-factorization: Thom's published LEF Kazhdan group is built in positive characteristic and has central p-torsion; this characteristic-zero finite-index refinement has no torsion.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that asks in addition for a controlled automorphism, a finitely presented mapping torus and full defect saturation; this supplies the kernel's four intrinsic properties only.
  titz-witzel-simple-kazhdan-cat0-lattices-exist: those groups are finitely presented, torsion-free and simple but their soficity is unknown; this group is LEF but is not claimed finitely presented or simple.
  mapping-torus-mf-radical-lies-in-finite-residual: that result bounds every automorphism mapping-torus MF radical by the finite residual and uses the characteristic centre and residually finite quotient of this seed to rule out a full kernel MF radical.
artifacts:
  - research/artifacts/torsion-free-lef-kazhdan-seed-2026-08-26.md
  - GroupApproximation/Algebra/AmenableMFProof.lean
---

**ESTABLISHED.**  There exists a finitely generated group `K` such that

```text
K is torsion-free, LEF, sofic, operator-MF, property (T),
and not residually finite.                                  (TLK1)
```

The construction is a characteristic-zero version of Thom's one-sided
central quotient, followed by a finite-index extraction which removes all
torsion without removing the invisible central element.

Let `R=Z[t,t^(-1)]` and let `H(R)` be the Kida--Tucker-Drob/Cornulier
parabolic

```text
      [ 1  u  c ]
      [ 0  h  v ],       h in EL_3(R),  u in R^(1x3), v in R^(3x1), c in R.
      [ 0  0  1 ]
```

Its centre `C` is the top-right root group `(R,+)`.  Put

```text
C_+ = Z[t] <= C,                 J = H(R)/C_+ .          (TLK2)
```

Then `J` has property `(T)` and is LEF.  Conjugation by
`diag(t,I_3,1)` shifts the centre, carries `C_+` properly into itself and
induces a surjective noninjective endomorphism of `J`.  Its kernel contains
the nontrivial infinite-order element represented by `t^(-1)`.  Since
property `(T)` makes `J` finitely generated, the standard equal-index-kernel
argument puts this kernel in the finite residual of `J`.

The quotient by the full centre is

```text
J/(C/C_+) ~= EL_3(R) semidirect (R^3 x R^3),             (TLK3)
```

a finitely generated characteristic-zero linear group.  Choose a
torsion-free finite-index subgroup of `(TLK3)` by Selberg's lemma, and replace
it by the intersection of all subgroups of the same index.  The result
`Gamma_0` is characteristic, finite index and torsion-free.  Define `K` to be
its full preimage in `J`.  Its kernel is

```text
C/C_+ ~= directSum_(n<0) Z t^n,
```

which is torsion-free.  Thus an element of finite order in `K` maps trivially
to `Gamma_0` and then lies in a torsion-free central group, proving that `K`
is torsion-free.  Finite-index permanence gives property `(T)`, and LEF
passes to subgroups.

Finally the invisible central element lies in `K`.  If a finite quotient of
`K` separated it, the core of its kernel in the finite-index overgroup `J`
would still omit it (the element is central) and would give a finite quotient
of `J` separating it.  This contradicts its membership in the finite
residual of `J`.  Hence `K` is not residually finite.  Since every LEF group
is sofic and operator-MF (`isSofic_of_isLEF`,
`isOperatorMF_of_isLEF`), `(TLK1)` follows.

The seed nevertheless cannot solve the exact-radical-over-`Z` target.  Its
central tail `A=C/C_+` is exactly the characteristic subgroup `Z(K)`, and the
quotient `K/A=Gamma_0` is finitely generated and residually finite.  By
`mapping-torus-mf-radical-lies-in-finite-residual`, every
automorphism `phi` satisfies

```text
Rad_MF(K semidirectProduct_phi Z) <= Z(K) < K.
```

This rules out not only the obvious Laurent shift but every possible
automorphism and every companion-matrix refinement of this central-extension
seed.  The operator-MF clause also rules out the direct-product route:
`K x Z` is operator-MF.  A successful kernel must avoid any proper
automorphism-invariant subgroup with finitely generated residually finite
quotient; in particular, a central-by-residually-finite seed has the wrong
global quotient geometry.
