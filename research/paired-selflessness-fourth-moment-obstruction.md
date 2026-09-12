---
rg: 2
id: paired-selflessness-fourth-moment-obstruction
kind: route
title: Compute the crossed-coordinate fourth moment
target: paired-selflessness-witnesses-do-not-tensor
requires: []
---

Since `A != C`, choose `x in A` which is not scalar and set

```text
a=x-tau(x)1.
```

Then `a` is centered and nonzero. Faithfulness of the GNS representation
gives `tau(aa*)>0`. Choose `b in B` in the same way.

Let

```text
x_1=a_0 tensor 1,      x_2=1 tensor b_1,
x_3=a_0* tensor 1,     x_4=1 tensor b_1*.
```

The odd terms lie in `D_0`, the even terms lie in `D_1`, and every term
is centered for the product trace. The tensor coordinates commute, so

```text
x_1 x_2 x_3 x_4
  = (a_0 a_0*) tensor (b_1 b_1*).
```

The free-product states restrict to the original states on each canonical
copy. Therefore

```text
(tau*tau) tensor (sigma*sigma)(x_1 x_2 x_3 x_4)
  = tau(aa*) sigma(bb*) > 0.
```

Freeness of `D_0,D_1` would force every alternating product of centered
elements to have trace zero, a contradiction.

The same computation survives after applying any trace-preserving
ordinary-selflessness embeddings of the two free products to ultrapowers:
the crossed-coordinate elements still commute and retain this positive
fourth moment. Thus a synchronized tensor/Fubini placement of the two
existing witnesses cannot be the missing complete-graph witness. A new
argument would have to use an entangling unitary or the operator-valued
uniformity encoded by complete selflessness.
