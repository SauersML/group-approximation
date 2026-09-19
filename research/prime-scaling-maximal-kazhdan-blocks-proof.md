---
rg: 2
id: prime-scaling-maximal-kazhdan-blocks-proof
kind: route
title: Read the prime scale from the Bass-Serre block stabilizer
target: prime-scaling-maximal-kazhdan-blocks
requires: []
artifacts:
  - research/artifacts/prime-scaling-kazhdan-block-rigidity-2026-08-30.md
---

Fix a prime `p).  The scaled base is
`B=Z^3 semidirect SL_3(Z)`, and the ascending HNN quotient is

```text
V_p=(Z[1/p]^3 semidirect SL_3(Z)) semidirect <t>,
tut^(-1)=pu.
```

As in the literal block calculation, the lamp sites at height `n` are
`Z[1/p]^3/p^n Z^3`.  The orbit of the marked ordered pair has differences

```text
p^(n-1) epsilon mod p^n Z^3,
epsilon in F_p^3-{0}.
```

Indeed reduction `SL_3(Z)->SL_3(F_p)` is onto and
`SL_3(F_p)` is transitive on nonzero vectors.  Translation gives the full
affine orbit.  Hence every orbital component is exactly a complete graph on
one coset of `p^(n-1)Z^3/p^nZ^3`, with `p^3` vertices.  Centralizing the
marked commutator therefore makes each lamp block
`P_p=ClLamp(p^3)`, and different blocks meet in their common central
involution `w`.  The block stabilizer is
`B_(p,1)=t^(-1)Bt`.  The standard tree-of-blocks calculation gives

```text
E_p=(V_p x <w>) *_(B_(p,1) x <w>) (P_p semidirect B_(p,1)).
```

Write `A_p=V_p x <w>` and `L_p=P_p semidirect B_(p,1)`.
The group `B_(p,1)` has property `(T)`, and property `(T)` is preserved
by a finite kernel, so `L_p` has property `(T)`.

Every property-`(T)` subgroup `H<=E_p` has Serre property FA and fixes a
vertex of this Bass--Serre tree.  If it fixes an `L`-vertex, then it lies in
a conjugate of `L_p`.  If it fixes an `A`-vertex, its image under the
height homomorphism `A_p->Z` is a property-`(T)` subgroup of `Z), hence
is trivial.  Since `H` is finitely generated, it lies in one telescope
level `B_(p,n)x<w>`, a conjugate of an edge group, and hence in the
adjacent conjugate of `L_p`.  Finally `L_p` fixes only its own
`L`-vertex: containment in a second vertex stabilizer would put it in an
edge stabilizer, impossible because
`P_p/<w>` is nontrivial.  Thus the maximal property-`(T)` subgroups are
exactly the conjugates of `L_p`.

It remains to compute their finite radicals.  The affine group
`B_(p,1) ~= Z^3 semidirect SL_3(Z)` has no nontrivial finite normal
subgroup.  A finite normal subgroup projects to a finite normal subgroup of
`SL_3(Z)`; finite conjugacy forces its elements to commute with powers of
all elementary matrices, hence with all elementary matrices, and therefore
to be scalar.  The center of `SL_3(Z)` is trivial.  The remaining kernel
lies in torsion-free `Z^3` and is also trivial.  Consequently every finite
normal subgroup of `L_p` lies in `P_p`.  Since `P_p` is itself finite
and normal, it is the unique largest one.  The Clifford normal form
`w^e c_1^(e_1)...c_(p^3)^(e_(p^3))` gives
`|P_p|=2^(p^3+1)`, completing the proof.
