---
rg: 2
id: left-right-character-kernel-proof
kind: route
title: Make each Boolean derivative invariant under the opposite Cayley action
target: bounded-degree-left-right-character-code-has-bounded-dimension
requires: []
---

For `a in A`, define the Boolean left derivative

```text
delta_a f(g)=f(ag)+f(g).                                    (LRK1)
```

Square parity is exactly

```text
delta_a f(gb)=delta_a f(g).                                 (LRK2)
```

Since `B` generates `G`, right multiplication by `B` is transitive, so
`delta_a f` is constant; denote the constant by `chi(a)`.  Hence

```text
f(ag)=chi(a)+f(g).                                          (LRK3)
```

Because `A` generates, applying `(LRK3)` along words shows that the generator
labels respect every relation of `G`.  They therefore extend to a homomorphism
`chi:G->F_2`, and `f(g)=f(1)+chi(g)`.  Conversely every function of this form
plainly has zero square parity, proving `(LRC1)`.

A homomorphism from `G` is determined by its values on either generating set,
so `dim Hom(G,F_2)<=min{|A|,|B|}`.  This proves `(LRC2)`.
