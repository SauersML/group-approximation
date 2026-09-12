---
rg: 2
id: finite-tags-do-not-atomize-heisenberg-schrodinger-tower
kind: claim
title: Fixed finite tags do not atomize the diffuse Heisenberg Schrödinger tower
distinct_from:
  leavitt-character-mass-escapes-to-finer-characters: that identifies the general finite-window marginal loophole and a diffuse CAR limit; this gives an explicit coherent finite Heisenberg tower, computes every polarized atom exactly, and proves that tensoring any fixed finite selector packet does not change the decay.
  hs-finite-heisenberg-windows-have-compatible-density-measures: that constructs the compatible irreducible density vectors available from every HS microstate; this exhibits compatible vectors with full marked central mass but no bounded-menu positive-density polarized atom.
  plancherel-root-shears-have-no-compression-pressure: that proves stationary mass for automorphism shears on one fixed Fourier window; this treats strictly growing nondegenerate Heisenberg windows and the failure of fixed finite tags to stop their coordinate refinement.
  agent-free-compressor-chart-edge-has-multiplicity-gauge: that computes the abstract commutant gauge for one simple finite chart; this identifies its exponentially growing size on the concrete nested Heisenberg windows.
---

**ESTABLISHED CALIBRATION.** Fix a prime `p` and, for `N>=1`, let

```text
H_N=H(F_p^N)=<X(v),Y(w),Z : [X(v),Y(w)]=Z^(<v,w>)>
```

be the finite Heisenberg group with its standard nondegenerate pairing.  Fix
a nontrivial `p`th root `zeta`, and let `pi_N` be the Schrödinger
representation on

```text
K_N=l2(F_p^N),                 dim K_N=p^N,
```

with `pi_N(Z)=zeta I`.  Under the coordinate inclusion
`H_N<=H_M`, `M>=N`, one has

```text
pi_M restricted to H_N = p^(M-N) pi_N.                 (FTH1)
```

Consequently these representations give an exact compatible system of all
finite Heisenberg multiplicity densities, and the nontrivial central-root
carrier has normalized trace one at every level.

On the other hand, the Fourier projections for the maximal abelian root
group `X(F_p^N)` are the `p^N` rank-one coordinate projections.  In `pi_M`,
each such level-`N` projection has rank `p^(M-N)` and therefore normalized
trace

```text
p^(-N).                                                (FTH2)
```

Let `sigma:K->U(D)` be **any fixed finite-dimensional packet**, and tensor
the whole tower by `sigma`.  Formula `(FTH2)` is unchanged.  More generally,
if `f_1,...,f_C` is any fixed menu of packet projections, every projection
subordinate to a union of at most `C` joint atoms

```text
(one X(F_p^N)-character) tensor (one f_j-sector)
```

has normalized trace at most

```text
C p^(-N).                                              (FTH3)
```

In particular, a union of level-`N` polarized atoms with normalized trace at
least `alpha>0` must contain at least

```text
alpha p^N                                               (FTH4)
```

distinct `X(F_p^N)` characters.  The required aggregation width is therefore
exponential in the Heisenberg rank.

There is a matching operator-level obstruction.  In the restriction
`(FTH1)`, the complete finite Heisenberg table determines only

```text
pi_N(H_N) tensor I_(p^(M-N)).
```

Its exact commutant contains the full gauge group

```text
I_(p^N) tensor U(p^(M-N)).                              (FTH5)
```

After tensoring a fixed packet, this same gauge survives with an additional
identity on the packet factor.  Thus the density vectors and every fixed tag
moment leave an exponentially growing relative unitary holonomy between
window exactifications.  A decoder must control that holonomy by a mixed
same-reservoir relation; scalar branching compatibility cannot do so.

Thus no bounded finite tag, finite selector, or fixed `S3` packet can turn a
bounded number of refined Heisenberg coordinate types into a uniformly
positive-density carrier.  A coherent Heisenberg decoder must instead
aggregate an unbounded family of fine characters with controlled
cross-character coefficient maps, or use a genuinely growing/matrix-only
return.  Merely adjoining a fixed packet to the compatible scalar density
system cannot close the decoder.

This separates two notions that can otherwise be conflated.  In the Leavitt
prefix packet all finite Heisenberg groups have the **same** central root.
Its nontrivial spectral projection is consequently one literal common
carrier, and in the model above it is the identity.  What disappears is not
the common central carrier but every bounded collection of polarized
coordinate atoms inside it.  The unresolved decoder is thus a coherent
exponential-width aggregation theorem, not merely an intersection theorem
for the central-root projections.

The calibration does **not** refute a decoder using the full group
presentation: it isolates exactly what extra information that decoder must
use beyond compatible finite-window densities and a bounded tag menu.
