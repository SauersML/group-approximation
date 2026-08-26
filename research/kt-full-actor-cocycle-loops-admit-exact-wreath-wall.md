---
rg: 2
id: kt-full-actor-cocycle-loops-admit-exact-wreath-wall
kind: claim
title: Every full Kun--Thom cocycle loop closes in an exact tracial wall model
distinct_from:
  bare-relative-wall-exists: That asks for a wall inside a Connes-embeddable finite tracial algebra; this gives the canonical exact wreath von Neumann algebra wall and explicitly does not assert that this algebra is Connes embeddable.
  kt-ab-normalizer-row-forces-wall-gauge-propagation: That proves the first quantitative normalizer-row law and forces the B gauge to propagate into A; this constructs the coherent full-actor coboundary which carries that propagated gauge through every cyclic and Steinberg relation.
  kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath: That gives finite canonical models only for the external A,B orbit, omitting the mixed Gamma stabilizer; this uses the full generalized wreath and its root lamp, hence includes every mixed Gamma--actor relation exactly but makes no matricial-approximability claim.
  kt-full-actor-extension-is-locally-hs-unstable: That constructs finite-dimensional approximate full-actor tuples and extends them only with a central lamp which collapses the marked pair; this is an exact infinite tracial model with the maximal marked-pair gap.
  relative-wall-commutant-growth: That characterizes a wall by strict relative-commutant growth in an arbitrary target; this writes the associated two-copy nonabelian cocycle, audits all relator holonomies, and gives the canonical wreath coboundary countermodel to a relation-only energy identity.
---

**ESTABLISHED TRACIAL FIREWALL; CONNES EMBEDDABILITY IS NOT CLAIMED.**
Let

```text
W=(direct_sum_(G/Gamma) C_2) rtimes G                  (KCL1)
```

be the canonical binary Kun--Thom generalized wreath, let `M=L(W)`, write
`u_g` for the actor unitary, and let `v=a_Gamma` be the root lamp.  Define
two representations of the **whole** actor by

```text
rho_1(g)=u_g,                 rho_0(g)=v u_g v.          (KCL2)
```

Then:

1. `rho_0|Gamma=rho_1|Gamma`, because the root lamp is fixed by `Gamma`;
2. both maps satisfy every actor relation, including `C^3=1`, all Steinberg
   relations, and every semidirect `Gamma` covariance row, exactly;
3. both actor characters are the canonical regular character; and
4. for every `h` with `h Gamma!=Gamma`,

   ```text
   ||rho_0(h)-rho_1(h)||_2^2=2.                          (KCL3)
   ```

Thus the exact nonabelian two-copy cocycle

```text
z_g=rho_1(g)^*rho_0(g)=u_g^*v u_g v                   (KCL4)
```

is coherent over the full nonamenable pair `A=CB,B` and retains the maximal
marked fold.  In particular `C^3`, the finite Steinberg presentation, and
`Gamma` covariance yield only closed **holonomy products**, not a positive
tracial cocycle energy.  No universal finite-tracial inequality whose
right-hand side vanishes with those relation defects can force `(KCL3)` to
vanish.

This does not construct a matrix-ultraproduct countermodel.  Connes
embeddability of the canonical wreath algebra is the open hyperlinearity
problem.  The theorem proves that the next positive statement must use a
genuinely matricial/Connes-embeddability feature; it cannot be obtained by a
formal rearrangement, trace inequality, or sum-of-squares consequence of the
full actor relations alone.

Proof: `kt-full-actor-cocycle-loop-wall-proof`.
