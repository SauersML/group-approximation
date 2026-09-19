---
rg: 2
id: agent-bloop-strong-atiyah-corner-quantization-proof
kind: route
title: Quantize every algebraic subprojection of the authenticated half-corner
target: agent-bloop-strong-atiyah-corner-quantization-obstruction
requires: []
---

Let `H=G/<J>` be torsion-free.  Every finite subgroup of `G` maps trivially
to `H`, hence lies in `<J>`.  Since `J` is nontrivial,

```text
lcm(G)=2.                                                   (SAQ1)
```

Assume that `G` satisfies the Strong Atiyah conjecture over `C`.  If

```text
p=p*=p^2 in q C[G]q,          q=(1-J)/2,
```

then left convolution by `1-p` on `ell^2(G)` has kernel `p ell^2(G)`.
Strong Atiyah and `(SAQ1)` therefore give

```text
tau_G(p)=dim_(N(G)) ker(1-p) in (1/2)Z.                    (SAQ2)
```

But `p<=q` and `tau_G(q)=1/2`.  Hence `tau_G(p)` is `0` or `1/2`.
Faithfulness of the canonical trace gives respectively `p=0` or `p=q`.

Now let `B` be projection-generated and have no Connes-embeddable trace.  A
unital star map `B->qC[G]q` cannot send every projection generator to `0` or
`q`, since then its image would be scalar and it would give a character
`B->C`.  Thus it produces a proper projection `0<p<q`, contradicting the
preceding paragraph.  Consequently any such map forces failure of Strong
Atiyah.  End proof.
