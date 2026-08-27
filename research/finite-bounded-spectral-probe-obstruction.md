---
rg: 2
id: finite-bounded-spectral-probe-obstruction
kind: claim
title: Finite bounded diagonal probes cannot resolve an infinite character transport table
distinct_from:
  finite-covariance-energy-sees-only-character-restrictions: that computes the kernel for probes which are evaluations at finitely many module elements; this treats arbitrary bounded diagonal operator probes and gives an if-and-only-if coercivity criterion.
  orthogonal-checksum-controls-only-mass-weighted-syndromes: that studies a word already decomposed over orthogonal first-hit domains; this shows that no finite bounded diagonal probe family can produce the fine-domain decomposition in the first place.
  rectangular-escape: that changes the label factor and multiplicity reservoir; this obstruction already holds for one source and one target PVM with no spectator-multiplicity exchange.
---

**ESTABLISHED.**  Let `Omega` be a set, let `sigma:Omega->Omega'` be a
bijection, and let

```text
F=(f_1,...,f_q):Omega -> C^q                            (BSP1)
```

be a finite family of bounded functions.  For finite-support PVMs
`(P_chi)` and `(Q_psi)` resolving the identity of the same matrix algebra,
and a unitary `C`, put

```text
A_j=sum_chi f_j(chi)P_chi,
B_j=sum_psi f_j(sigma^(-1)psi)Q_psi,
d_j=||C A_j C^*-B_j||_2,                               (BSP2)

E_sigma=sum_chi ||C P_chi C^*-Q_(sigma chi)||_2^2.     (BSP3)
```

Then a dimension-independent estimate

```text
E_sigma <= K sum_(j=1)^q d_j^2                         (BSP4)
```

holds for every such finite PVM pair and every `C` if and only if

```text
inf_(chi!=chi') ||F(chi)-F(chi')||_2^2 >= 2/K.          (BSP5)
```

In particular, if `Omega` is infinite, no finite family of bounded probes
can satisfy `(BSP4)` with any finite `K`.  More quantitatively, for every
`epsilon>0` there is a two-atom exact unitary model with

```text
E_sigma=2,             sum_j d_j^2<epsilon.             (BSP6)
```

This strictly extends the finite-restriction obstruction.  The probes may
be arbitrary bounded Borel functions of the character label, not just the
signs `chi(m)` at a finite list of module elements.  Consequently, replacing
that finite list by finitely many bounded Fourier series, heat filters,
resolvents, or other diagonal operator-space checks cannot create the
infinite-resolution energy interface.

The negative conclusion also survives a fixed finite-dimensional
operator-space packet.  Fix `k,q` and bounded matrix features

```text
F_j:Omega -> M_k(C).                                    (BSP7)
```

Put one copy of `C^k` over each of two selected atoms and let `C` exchange
the two whole blocks without rotating their internal coordinates.  Then the
fine atom-transport energy is again `2`, whereas the total packet defect is

```text
sum_j ||F_j(chi_0)-F_j(chi_1)||_(2,k)^2.                (BSP8)
```

The bounded image lies in the finite-dimensional space `M_k(C)^q`, hence
has arbitrarily close distinct points when `Omega` is infinite.  Thus a
finitely presented packet of fixed matrix size cannot evade `(BSP6)` by
replacing scalar Fourier features with matrix-valued ones.  The label
matrix size itself must grow, or the packet must authenticate genuinely
non-diagonal domains which are not functions of the character atom.

## Consequence for the affine--Leavitt route

After an active-module PVM has been decoded, every fixed bounded operator
formed inside its abelian algebra is a probe of the form `(BSP1)`.  Hence no
finite collection of such operators can turn its covariance defects into
the fine character transport energy required by
`infinite-character-actor-word-energy-interface`, even if each operator
packages infinitely many module coefficients.

Leavitt self-similarity therefore has only two genuinely different uses:

1. if its branch operators are used merely to synthesize finitely many
   bounded **diagonal** probes, including fixed-size matrix-valued probes,
   `(BSP6)--(BSP8)` give the same two-atom escape;
2. if they authenticate orthogonal non-diagonal domains on one common
   positive carrier, then they have crossed into a proper Leavitt/Cuntz
   corner, and `approximate-relative-leavitt-cell-kills-active-trace`
   already collapses that carrier with a dimension-free trace estimate.

The unresolved middle is thus not a more elaborate bounded spectral
function.  It is precisely the matrix-only authentication that prevents
the non-diagonal branch domains from changing reservoirs.  If the domains
are allowed to change reservoir, `rectangular-escape` remains exact.

This theorem concerns the marginal source/target PVM calculation.  It does
not rule out a joint non-diagonal word whose orthogonal blocks are themselves
authenticated by additional mixed relations, nor does it replace the
same-PVM actor-loop constraints.  Those are exactly the surviving gates.
