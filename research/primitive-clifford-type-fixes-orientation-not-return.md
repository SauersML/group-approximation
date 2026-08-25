---
rg: 2
id: primitive-clifford-type-fixes-orientation-not-return
kind: claim
title: A primitive Clifford type fixes controller orientation but not the Leavitt return
distinct_from:
  controlled-pauli-corner-has-clifford-groupification: that leaves the arbitrary multiplicity involution on the whole marked sector; this removes it by selecting one primitive central block of the finite extension.
  finite-marked-involution-anchor-has-one-third-wrong-mass: that rules out orienting the whole marked Plancherel sector with one finite anchor; this discards the wrong primitive type and records its fixed positive boundary mass.
  paired-same-reservoir-boundary-lemma: that must return the selected type through a scale-changing Whitehead cell or charge its loss; this closes only the local orientation ambiguity before that return.
---

**ESTABLISHED.**  Let

```text
G_CZ=P semidirect <t>
```

be the order-`64` controlled two-qubit Pauli group from
`controlled-pauli-corner-has-clifford-groupification`.  The extraspecial
Pauli group `P` has one irreducible marked spin representation `S` of
dimension four.  Since the controlled automorphism is implemented by the
rank-one reflection `C`, `S` has exactly two extensions to `G_CZ`,

```text
pi_+(p)=S(p),       pi_+(t)= C,
pi_-(p)=S(p),       pi_-(t)=-C.                        (PCT1)
```

Let `z_+,z_-` be the corresponding primitive central projections in
`C[G_CZ]`.  On the `z_+`-range of **every** unitary representation of
`G_CZ`, finite-dimensional representation theory gives

```text
rho(p)=S(p) tensor I_M,       rho(t)=C tensor I_M.      (PCT2)
```

Thus primitive finite-type selection really does remove the arbitrary
multiplicity involution `V` from the controller.  Likewise `z_-` fixes the
opposite orientation.  In the regular trace,

```text
tau(z_+)=tau(z_-)=4^2/64=1/4.                          (PCT3)
```

So the selection has fixed positive density and is robust after the usual
finite-group normalized-HS exactification; it is not a microscopic choice.

This does not produce the missing Leavitt return.  On `P_+=z_+`, the coarse
Pauli atom `e` and fine rank-one atom `f` have

```text
tau(eP_+)=tau(P_+)/2,       tau(fP_+)=tau(P_+)/4.       (PCT4)
```

Consequently every unitary `W` satisfies

```text
||W(eP_+)W^*-fP_+||_2^2 >= tau(P_+)/4.                 (PCT5)
```

In particular, no ordinary exact relation can both keep this same primitive
carrier and identify the coarse and fine selectors: it would contradict
finite trace already in the regular representation.  An ambient Whitehead
word may instead move mass out of `z_+`, because `z_+` is central only in the
finite subgroup, not in the full scale-changing group.  Controlling that
off-type mass is exactly the boundary term still requested by
`paired-same-reservoir-boundary-lemma`.

Therefore the local multiplicity orientation and the global same-reservoir
return are strictly separate issues.  Enlarging to the full finite
controlled-Clifford packet and cutting a primitive type solves the former
completely, but it converts the latter into the explicit leakage

```text
||(1-z_+)W e z_+||_2^2
```

(together with the wrong fine-type component).  No additional local
Clifford representation theory can bound that leakage; the required input
must come from the nonnormal affine-Leavitt/Steinberg coupling or from a
finite-matrix coordinate extraction.
