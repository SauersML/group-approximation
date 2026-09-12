---
rg: 2
id: mf-reflection-colimit-calculus
kind: claim
title: MF reflection computes all countable colimits by reflecting the ordinary group colimit
artifacts:
  - research/mf-reflection-colimit-calculus-proof.md
---

Let `D` be any small diagram of countable groups whose ordinary group colimit
`C=colim_Grp D` is countable.  Then the colimit of the reflected diagram in
the category of countable MF groups exists and is

```text
colim_MF (R_MF o D) ~= R_MF(C).                       (MC1)
```

Consequently:

1. the MF coproduct of a countable family of countable groups `G_i` is the
   reflection of their free product;
2. the MF pushout of `G <- A -> H` is
   `R_MF(G *_A H)`;
3. the MF coequalizer of `f,g:A->B` is the reflection of
   `B/normalClosure{f(a)g(a)^(-1)}`;
4. the MF reflection of an HNN extension is the reflected coequalizer of its
   two edge embeddings;
5. for a presentation `<X|S>`, the reflected presented group is
   `F(X)/mfroot(<<S>>)`, and adjoining relations means taking a coequalizer
   followed by exactly one application of `R_MF`.

Moreover, objectwise replacement of a diagram by its MF reflections does not
change the final reflected colimit:

```text
R_MF(colim_Grp D)
  ~= R_MF(colim_Grp(R_MF o D)).                       (MC2)
```

Thus all MF-visible information in an arbitrary countable gluing problem is
determined before gluing by the MF reflections of its pieces and after
gluing by one final radical quotient.
