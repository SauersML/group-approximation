---
rg: 2
id: mf-camouflage-is-a-faithful-split-extension-functor
kind: claim
title: MF camouflage is a faithful functor by split perfect black-hole extensions
artifacts:
  - notes/MF_REFLECTION_AND_CORONA_SUPPORT_CALCULUS.md
---

Fix a perfect group `B` with full MF radical and a normal generator `d`, and
put `D=<d>`.  The assignment

```text
Q |-> C_d(Q)=B *_D (Q x D)
```

extends to a faithful endofunctor `C_d` on countable groups.  A homomorphism
`f:Q->R` induces the unique map which is the identity on `B` and is

```text
(q,x) |-> (f(q),x)
```

on `Q x D`.  The quotient maps and canonical sections are natural
transformations

```text
pi:C_d => Id,                 s:Id => C_d,
pi_Q after s_Q = id_Q.                                (FSF1)
```

The functor preserves monomorphisms and epimorphisms.  If `f` is injective,
the regular-star description embeds the vertex groups indexed by `Q` into
the distinct vertex groups indexed by `f(Q)`, and amalgam normal form gives
injectivity of `C_d(f)`.  If `f` is surjective, the images of `B` and
`Q x D` generate `C_d(R)`, so `C_d(f)` is surjective.

Every component `pi_Q` is simultaneously:

* a split epimorphism with perfect full-MF-radical kernel;
* an isomorphism on every outgoing Hom functor into an MF group;
* a complete-lattice isomorphism on MF-closed normal subgroups.

Thus the construction functorially thickens every group by an explicitly
structured invisible kernel while preserving its complete MF reflection.
