---
rg: 2
id: fell-models-inherit-walls-from-coefficients
kind: claim
title: A Fell-absorbed model has a relative wall exactly when its coefficient representation does, for a subgroup with infinite conjugacy classes
distinct_from:
  ce-stabilizer-criterion-needs-no-trace: that uses the tensor product with the regular representation to make an arbitrary model canonical and deduce relative embeddability; this computes the relative commutant of such a tensor model exactly and shows tensoring creates no new walls or stabilizers.
  relative-wall-commutant-growth: that is the general equivalence between a wall and growth of the relative commutant; this identifies that commutant for one class of canonical models.
---

**ESTABLISHED.** Let `Gamma <= G` be countable groups such that every
`h in G - {e}` has infinite `Gamma`-conjugacy class. Let `(M_0,tau_0)` be a
finite von Neumann algebra, `pi : G -> U(M_0)` any homomorphism, and put
`sigma = lambda tensor pi : G -> U(L(G) tensor-bar M_0)`, a canonical
(trace-preserving) model. Then

```text
(L(G) tensor-bar M_0) cap sigma(Gamma)' = 1 tensor (M_0 cap pi(Gamma)'),
Ad sigma(g)(1 tensor b) = 1 tensor Ad pi(g)(b)        (g in G, b in M_0).     (FMW1)
```

The same identity holds for `t Gamma t^(-1)`, which also has infinite
conjugacy classes on `G - {e}`. Consequently:

1. `sigma` has a relative wall at a compressor `t` iff `pi` does;
2. for every family `(b_i) subset M_0 cap pi(Gamma)'`, the common commutation
   stabilizer of `(1 tensor b_i)` under `sigma` equals that of `(b_i)` under
   `pi`, and every element of the relative commutant has this form.

So Fell absorption buys the canonical trace
(`ce-stabilizer-criterion-needs-no-trace`) and nothing else: the walls of the
canonical Fell model are exactly the walls already present in the coefficient
representation.

DERIVATION
fell-wall-inheritance-proof
