---
rg: 2
id: selected-odd-heisenberg-corner-is-native-matrix-amalgam
kind: claim
title: The selected odd Heisenberg corner is exactly a matrix packet amalgamated over the native root
distinct_from:
  affine-leavitt-p-heisenberg-graft-kills-fd-four-cap-corner: that proves the selected character corner is nonzero and invisible in finite-dimensional representations; this computes the complete algebraic corner and its canonical trace.
  amenable-edge-graph-corners-cannot-groupify-a-nonce-game: that gives the general hyperlinearity permanence fence; this identifies the affine-Leavitt Heisenberg graft as an exact instance and shows that a successful atlas there already proves the native vertex nonhyperlinear.
  finite-normal-signed-bcs-quotient-collapses-to-twisted-factor: that treats an invariant finite normal type in a quotient; here the finite Heisenberg packet is one vertex of an amalgam and the selected corner remains a free product over the native cyclic root.
---

Use the notation of `(PHG1)--(PHG3)` and fix a nontrivial character `chi` of
the central subgroup `<c>` of the finite Heisenberg group.  Then `e_chi` is
central in `C[Lambda_p]`, and there is a canonical algebraic star isomorphism

```text
e_chi C[Lambda_p] e_chi
  isomorphic to
C[Gamma_A] *_(C[<w>]) M_p(C).                          (OHM1)
```

The two embeddings of `C[<w>]` in `(OHM1)` are the native root copy in
`C[Gamma_A]` and the order-`p` Weyl generator in the unique
`p`-dimensional Heisenberg representation with central character `chi`.

After normalizing the canonical trace by `tau(e_chi)=1/p`, its restrictions
in `(OHM1)` are exactly

```text
tau_(Gamma_A)                 on C[Gamma_A],
tr_p                          on M_p(C),                 (OHM2)
```

and both restrict to the canonical trace on `C[<w>]`.

Consequently the odd Heisenberg graft supplies no independent
canonical-trace groupification shortcut around the native affine-Leavitt
vertex.  If a no-CE BCS star algebra admits a nonzero unital algebraic
corner map into `(OHM1)`, then `Lambda_p` is nonhyperlinear.  But

```text
Lambda_p=(Gamma_A x C_p) *_(C_p^2) H_p                 (OHM3)
```

is an amalgam of `Gamma_A x C_p` with a finite group over a finite subgroup.
Amenable-edge hyperlinearity permanence therefore gives

```text
Gamma_A hyperlinear  => Lambda_p hyperlinear.           (OHM4)
```

In fact the graft is analytically neutral in both directions:

```text
Gamma_A is hyperlinear
  iff Lambda_p is hyperlinear
  iff e_chi L(Lambda_p) e_chi is Connes embeddable.      (OHM5)
```

For the reverse implication, the normalized selected corner contains the
trace-preserving copy `lambda(g) |-> e_chi lambda(g)` of `L(Gamma_A)`.
Thus Connes embeddability of the corner passes back to the native group
factor; no stability or finite-dimensional lifting theorem is used.

Thus such a BCS corner map already implies that `Gamma_A` is
nonhyperlinear.  The finite matrix vertex in `(OHM1)` can provide the local
context packet and `e_chi` provides the necessary finite-dimensional
invisibility, but the load-bearing global atlas must use the native
`C[Gamma_A]` coefficient side strongly enough to prove the same unresolved
canonical-HS obstruction as the affine-Leavitt route.

This is a reduction, not a no-go for `(OHM1)`.  A successful atlas there
would be a proof of nonhyperlinearity.  It shows that merely attaching the
finite Heisenberg packet, or tensoring an already chosen finite atlas by
`e_chi`, cannot avoid the native analytic gate.

There is also no literal-conjugate atlas shortcut inside this normal form.
`native-conjugate-heisenberg-charts-share-only-edge-coefficients` proves that
two distinct packet charts transported by native-vertex group words can
share only coefficients supported on the cyclic amalgamating algebra.  Any
live projection atlas must therefore use alternating multi-piece Hecke
coefficients, rather than only conjugates of the finite `M_p` block.
