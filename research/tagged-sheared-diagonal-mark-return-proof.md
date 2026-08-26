---
rg: 2
id: tagged-sheared-diagonal-mark-return-proof
kind: route
title: Distinct sheared rows force the direct prototype transporters to escape the mark centralizer
target: tagged-sheared-diagonal-one-chart-hits-mark-area
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

Fix one main address `i` and let `j` vary through infinitely many other main
addresses.  The row elements

```text
p_(ij)=x_12(A_i+A_j)                                    (DSDP1)
```

are pairwise distinct, as is immediate in the elementary-matrix quotient
and from linear independence of the orthogonal address rows.

The last equation of `(DSD5)` puts every `g_(ij)` in `C_Delta(z)`.  If two
of them represented the same coset modulo `<z>`, then

```text
g_(ik)=g_(ij)z^epsilon                 (epsilon in {0,1}). (DSDP2)
```

Because `[p_*,z]=1`, conjugating `p_*` by the two sides of `(DSDP2)` gives
the same element.  The first equation of `(DSD5)` would then imply
`p_(ik)=p_(ij)`, contradicting `(DSDP1)`.  Thus the `g_(ij)` occupy
infinitely many distinct cosets in `C_Delta(z)/<z>`.

The word `z=x_13(q)` is a nontrivial involution.  Applying
`finite-mark-centralizer-commutator-area-is-proper` to the representing
words `g_(ij)` shows that every fixed sublevel set of

```text
g<z> |-> Area([g,z])                                    (DSDP3)
```

is finite.  Hence `(DSD6)` is unbounded.

Finally, outer conjugation of the fixed null prototype has boundary

```text
g_(ij)[p_*,h_*]z^(-1)g_(ij)^(-1)
 =[p_(ij),h_(ij)] (g_(ij)zg_(ij)^(-1))^(-1).            (DSDP4)
```

Changing its terminal word to the literal `z^(-1)` is exactly the mark
return `(DSD6)`.  Therefore neither a literal one-chart cell nor a uniformly
bounded factorwise comparison of that cell can fill `(DSD3)`.
