---
rg: 2
id: finite-weyl-root-moments-do-not-authenticate-toeplitz-square
kind: claim
title: Finite Weyl/root moments cannot authenticate the Toeplitz square reservoir
distinct_from:
  positive-toeplitz-head-is-square-defect-or-rectangular-escape: that gives the square trace-cyclicity floor and the bare rectangular inclusion/projection; this shows that adjoining finite Weyl packets, root conjugacies, and their canonical moments does not remove the rectangular branch.
  mixed-steinberg-loops-admit-morita-rectangular-model: that treats typed Steinberg multiplication diagrams abstractly; this adds the Toeplitz head and isolates the canonical-moment versus literal-return dichotomy.
  finite-router-fine-prefix-return-collapses-mark: that gives the coarse/fine Pauli trace firewall for one proposed router; this applies the same principle to arbitrary finite typed Toeplitz--Weyl/root completions.
---

**ESTABLISHED LANGUAGE NO-GO.**  Consider a finite coefficient decoder built
only from the following cells:

1. a Toeplitz inclusion/projection pair between named source and target
   objects;
2. finite Weyl multiplication and conjugacy tables on label factors at
   those objects;
3. Steinberg root multiplication triangles for composable typed
   coefficients, together with finite Weyl permutations of root indices;
4. canonical scalar trace moments of words in the resulting finite packet
   and block groups.

As long as no cell identifies two unequal object identities, this language
does not authenticate one square coefficient reservoir.  Indeed choose

```text
F=E direct_sum H,             H!=0,
S:E->F,                       T=S^*:F->E.               (FWM1)
```

Then

```text
TS=1_E,                       ST=1_F-P_H.               (FWM2)
```

Put every finite Weyl packet on a tensor label factor and enlarge the
spectator multiplicities at the typed objects as necessary.  Equal-rank
packet atoms are transported by block permutations.  Interpret every root
coefficient as a rectangular block map between its named objects.  Direct
block multiplication gives all Steinberg triangles, and associativity gives
every finite pasted root loop.  Thus the positive Toeplitz head `P_H` and
all the cells in (1)--(3) coexist with zero defect.

Canonical moments do not change this conclusion.  The finite Weyl and block
groups have left regular representations.  Passing to those representations
makes the trace of every nonidentity word of the finite local group zero;
on a prescribed central phase it merely fixes the Plancherel weight of each
Weyl type.  It does not identify the spectator multiplicity spaces attached
to different typed objects.  This is exactly the multiplicity trade measured
by `weyl-commutant-superrank-detects-rectangular-return`: the source and
target commutant superranks are both correctly recovered, but on different
reservoirs.

There is a sharp obstruction to repairing this by one more literal finite
Weyl/root conjugacy.  If projections `e,f` are authenticated by the packet
moments and a unitary word `U` is required to transport them, then

```text
||UeU^*-f||_2^2 >= |tau(e)-tau(f)|.                    (FWM3)
```

Equivalently, for `R_e=1-2e` and `R_f=1-2f`,

```text
||R_f U R_e U^*-1||_2^2
   =4||UeU^*-f||_2^2
   >=4|tau(e)-tau(f)|.                                 (FWM4)
```

For a one-to-two refinement the right side is a fixed positive multiple of
the marked carrier trace.  Hence a literal return relation has only two
possibilities:

```text
typed return       => exact rectangular model with positive head;
untyped return     => canonical trace floor, so the marked regular witness
                      is collapsed.                    (FWM5)
```

This proves that finite Weyl/root conjugacy plus canonical moments cannot be
the missing same-square authentication.  A successful Toeplitz decoder must
use a genuinely finite-matrix coordinate statement which is unavailable in
the regular representation (for example a multiplicity PI/commutant-return
selection), and then the trace-cyclicity estimate in
`toeplitz-defect-needs-square-decoding` is already terminal.  Adding further
typed Weyl permutations, root triangles, or local canonical moment tests
cannot charge the reservoir change.

The scope is deliberately local: the regular construction authenticates
canonical moments of the finite packet/block groups represented by these
cells.  It does not assert that an arbitrary ambient presentation has a
finite quotient injective on every prescribed word window.
