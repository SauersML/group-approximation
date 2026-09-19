# Tree gluing reduces the common transport-law gate

Date: 2026-08-13

## 1. Outcome

The robust paired-quotient argument uses three transport contexts:

```text
(R0,L0),   (R0,L1),   (R1,L1).                       (TGC1)
```

Their context graph is the path

```text
L0 -- R0 -- L1 -- R1.                                (TGC2)
```

Therefore a four-way classical law need not be extracted at once.  It is
enough to construct three probability laws on pairs of **whole maps**

```text
mu00 on Map(V,V) x Map(W,W),
mu01 on Map(V,V) x Map(W,W),
mu11 on Map(V,V) x Map(W,W),                          (TGC3)
```

such that

1. the `R0` marginals of `mu00` and `mu01` agree;
2. the `L1` marginals of `mu01` and `mu11` agree;
3. each observed normalized-HS context error is bounded below by, or differs
   by `o(1)` from, the corresponding averaged deterministic table error.

Under (1)--(2), the three laws glue to one law on `(R0,R1,L0,L1)`.  Applying
`robust_floor_of_common_latent_maps` then gives the fixed error floor.

## 2. Finite tree-gluing lemma

The only probability fact needed is the following elementary lemma.

> Let `muAB` be a probability measure on `A x B` and `muAC` one on
> `A x C`.  If their `A` marginals agree, there is a probability measure
> `muABC` on `A x B x C` with these two marginals.

Write the common marginal as `alpha`.  On fibers with `alpha(a)>0`, set

```text
muABC(a,b,c) = muAB(a,b) muAC(a,c) / alpha(a).        (TGC4)
```

If `alpha(a)=0`, nonnegativity forces both incident rows to vanish, so put
the right side equal to zero.  Summing `(TGC4)` over `b` or `c` recovers the
two prescribed laws.

Apply this first to `mu00` and `mu01` over their common `R0` marginal.  The
result has the same `L1` marginal as `mu01`.  Glue it to `mu11` over `L1`.
This produces the required law on the path `(TGC2)`, with all three edge
marginals unchanged.

The one-edge gluing step, including nonnegativity, normalization, both
recovered marginals, and zero-marginal fibers, is formalized in
`GroupApproximation/Leavitt/FiniteTreeCoupling.lean`.  Its one-junction
existence theorem is `FiniteTreeCoupling.exists_gluing`.  The explicit
four-variable construction is `FiniteTreeCoupling.glueTransportPath`, and
`sum_glueTransportPath_00`, `sum_glueTransportPath_01`, and
`sum_glueTransportPath_11` state the three preserved edge marginals.  This
removes “apply the gluing lemma twice” as an informal step.

These declarations were added source-first and have not been compiled in
this iteration, following the explicit no-compilation instruction.  Their
mathematical content is the elementary conditional-product identity; kernel
checking remains a later verification task, not evidence for the research
claim.

This is the finite form of the standard fact that compatible marginals on an
acyclic context hypergraph have a global distribution.  No Birkhoff choices
have to be synchronized after the pair-laws have been obtained.

## 3. Why labelwise pair distributions are still insufficient

The word **whole** in “whole maps” is load-bearing.  A four-index table

```text
Qij(v,w,x,y)                                           (TGC5)
```

gives a joint output distribution separately for every source pair `(v,w)`.
It need not be a mixture of deterministic response maps

```text
x=Ri(v),  y=Lj(w).                                    (TGC6)
```

The source-setting graph contains many cycles even though the context-type
graph `(TGC2)` is a tree.  Thus ordinary no-signaling consistency of the
one-label marginals does not imply a law on whole maps.  This is exactly the
local-hidden-variable versus nonlocal-correlation distinction.

Consequently tree gluing removes only the **cross-context compatibility**
part of the common-law gate.  The remaining hard theorem is pairwise
classicalization:

> For each of the three contexts, turn the normalized-HS four-index
> correlation into a probability law on a pair of whole maps, with consistent
> shared-map marginals and without increasing the relevant pairing error by
> more than `o(1)`.

General quantum correlations do not have this property; Pauli and linear
constraint-system strategies are the standard obstruction.  A proof here
must use the special atlas multiplication, Kazhdan pinning, or a recovered
common finite-multiplicity Cartan.  Tree gluing itself cannot supply
classicality.

There is also an exact countermodel internal to the present finite-pairing
setup.  Uniformly sample a nonzero output pair with whichever pairing value
the context requires.  In every perfect binary pairing of size at least
four, the output marginals are uniform on the nonzero vectors independently
of the required value.  Thus all three contexts win perfectly and have
matching no-signaling marginals, but the choices vary jointly with the
source pair and do not define whole maps.  See
`FALSE_NONSIGNALING_PAIRED_QUOTIENT_SHORTCUT.md`.

## 4. Sharpened endpoint

The hierarchy of sufficient extraction statements is now:

```text
common finite-multiplicity Cartan normalization
        => compatible pair-laws on whole maps
        => tree-glued common latent-map law
        => averaged robust floor
        => contradiction.                             (TGC7)
```

The middle implication is elementary and exact.  The first implication is
the live matrix-specific step.  This formulation is narrower than a general
commutant-lifting theorem: only three pair contexts and two shared marginals
must be recovered.

An exact operator-algebraic sufficient condition for those pair-laws is given
in `TRUE_EDGE_PVM_LOCALITY_CRITERION.md`: projection-valued measurements
indexed by whole maps, commuting only along the three tree edges, produce the
compatible laws by taking traces of projection products.
