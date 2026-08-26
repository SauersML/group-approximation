---
rg: 2
id: torsion-free-lef-kazhdan-non-rf-seed
kind: claim
title: A torsion-free LEF Kazhdan group can fail residual finiteness
distinct_from:
  thom-hyperlinear-kazhdan-without-factorization: Thom's published LEF Kazhdan group is built in positive characteristic and has central p-torsion; this characteristic-zero finite-index refinement has no torsion.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that asks in addition for a controlled automorphism, a finitely presented mapping torus and full defect saturation; this supplies the kernel's four intrinsic properties only.
  titz-witzel-simple-kazhdan-cat0-lattices-exist: those groups are finitely presented, torsion-free and simple but their soficity is unknown; this group is LEF but is not claimed finitely presented or simple.
artifacts:
  - research/artifacts/torsion-free-lef-kazhdan-seed-2026-08-26.md
---

**ESTABLISHED.**  There exists a finitely generated group `K` such that

```text
K is torsion-free, LEF, sofic, property (T), and not residually finite.
                                                               (TLK1)
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
is sofic, `(TLK1)` follows.

This closes the intrinsic seed problem on the extrinsic route.  What it does
**not** provide is an automorphism `phi` for which `K semidirect_phi Z` is
finitely presented and carries a Kazhdan compression defect equal to `K`.
The obvious Laurent shift is only a surjective noninjective endomorphism
after the one-sided quotient, not an automorphism.
