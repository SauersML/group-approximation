---
rg: 2
id: p3-full-parahoric-interlock-enforces-inverse-mackey-cocycle
kind: claim
title: A full p-three parahoric packet enforces the inverse Mackey cocycle on multiplicity
distinct_from:
  commuting-automorphism-cocycle-forces-multiplicity: that proves the abstract divisibility law for one commuting automorphism square; this applies the full Clifford little-group multiplication table to the p-three oscillator band and shows that the proposed extra parahoric interlock enforces, rather than forbids, cocycle cancellation.
  p3-minus-flux-is-cancelled-by-pauli-multiplicity: that writes the rank-one Pauli cancellation while leaving open whether it extends to the full parahoric packet; this proves that every honest full extension has exactly that inverse-cocycle multiplicity structure and constructs one by twisted regular representation.
---

Let `N_a` be the finite Heisenberg radical of a level-`3^a` parahoric, let
`pi_a` be an irreducible oscillator type, and let `L_a` be its finite little
group.  Choose Stone--von Neumann intertwiners `W_g` on the oscillator space:

```text
W_g pi_a(n) W_g^* = pi_a(gng^(-1)),
W_g W_h = alpha_a(g,h) W_(gh).                         (PIC1)
```

On every honest finite-dimensional parahoric representation, the
`pi_a`-isotypic space is `H_(pi_a) tensor M`.  Schur's lemma factors the
little-group operators uniquely up to scalar as

```text
rho(g)=W_g tensor V_g.                                  (PIC2)
```

The exact multiplication relation `rho(g)rho(h)=rho(gh)` then gives

```text
V_g V_h = alpha_a(g,h)^(-1) V_(gh).                     (PIC3)
```

Thus the multiplicity coordinate is not forced to have trivial holonomy.
It is forced to carry the **inverse Mackey cocycle**.  In particular, if two
commuting coweight routes have oscillator commutator `-1`, their
multiplicity operators also have projective commutator `-1`, and the tensor
product routes commute exactly.  The smallest Weyl/opposite-root
multiplication square already enforces cancellation; adding the remaining
finite parahoric multiplication table cannot change its sign.

This is not merely a necessary condition.  The finite twisted regular
representation of `L_a` with multiplier `alpha_a^(-1)` supplies operators
`V_g` satisfying `(PIC3)`.  Hence `W_g tensor V_g`, together with
`pi_a(N_a) tensor I`, is an honest representation of the type stabilizer.
Inducing over the finite orbit of `pi_a` gives an honest finite-dimensional
representation of the whole finite parahoric packet.  Therefore a
higher-dimensional exact multiplicity gauge survives every relation in one
full finite packet.

The conclusion is exact and hence also rules out a dimension-independent HS
gap derived solely from that packet: the alleged forbidden configuration has
zero defect.  A surviving obstruction must add data not contained in one
Clifford extension, for example:

```text
(i)  a capacity bound excluding the required twisted multiplicity;
(ii) two packet charts imposing incompatible cocycles on the SAME
     authenticated multiplicity reservoir; or
(iii) an unbounded family whose projective commutator rank outruns that
      reservoir.
```

At fixed finite level none of these follows from Weyl, opposite-root, or
parahoric multiplication relations alone.  This is the p-primary
specialization of the standard Clifford--Mackey factor-set identity, and it
closes the proposed `+1` interlock route negatively.
