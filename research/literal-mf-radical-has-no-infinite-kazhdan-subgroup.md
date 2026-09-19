---
rg: 2
id: literal-mf-radical-has-no-infinite-kazhdan-subgroup
kind: claim
title: The exact MF radical of the literal sofic group has no infinite Kazhdan subgroup
distinct_from:
  literal-mf-radical-is-unsquared-defect: That computes the exact radical as the normal closure of one compression defect; this uses the block-amalgam structure of that radical to classify its property-(T) subgroups.
  exact-kazhdan-radical-kernel-cannot-be-lef: That excludes LEF Kazhdan groups with no finite quotients abstractly; this proves directly that every Kazhdan subgroup of one existing sofic non-MF radical is finite, without assuming normality or absence of finite quotients.
  torsion-free-sofic-exact-mf-radical-over-z: That asks for a nontrivial torsion-free Kazhdan radical; this rules out extracting such a kernel from the already-sofic literal group.
artifacts:
  - research/literal-mf-radical-has-no-infinite-kazhdan-subgroup-proof.md
---

Let `E` be the finitely presented sofic literal non-MF group and put

```text
D=Rad_MF(E)=<<[tct^(-1),v_1]>>^E.
```

Every property-`(T)` subgroup of `D` is finite.  Consequently `D` contains
no nontrivial torsion-free property-`(T)` subgroup.  In particular, neither
`D` nor any subgroup extracted from it can be the desired torsion-free
Kazhdan kernel.

The point is structural.  The defect generating `D` belongs to the normal
literal lamp kernel `N_E`, so `D<=N_E`.  The established block-amalgam
calculation gives

```text
N_E = *_(<w>), i in I ClLamp_i(8),
```

where every vertex group has order `512` and the common edge group `<w>` has
order two.  Thus `N_E` acts on its Bass--Serre tree with finite vertex
stabilizers.  Property `(T)` implies Serre's property `FA`, so a Kazhdan
subgroup fixes a vertex and is contained in a finite stabilizer.

This closes a tempting shortcut: the paper's existing explicit sofic
non-MF group cannot solve the torsion-free exact-Kazhdan-radical target by
choosing a better subgroup inside its already computed radical.

---

### Proof

literal-mf-radical-has-no-infinite-kazhdan-subgroup-proof
