---
rg: 2
id: canonical-sign-corners-maximally-mix-the-tv-odd-spectrum
kind: claim
title: Canonical sign corners maximally mix the TV odd spectrum
artifacts:
  - research/canonical-tv-odd-mass-fourier-proof.md
distinct_from:
  tv-zero-noise-cell-is-an-abelian-torsor: that classifies all local representations; this computes the exact spectral law forced by a canonical group trace after any faithful group extension.
  conjugacy-actions-cannot-prune-the-odd-tv-spectrum: that constructs finite-dimensional bad sectors for split extensions; this applies to arbitrary group extensions and identifies a trace-selection obstruction rather than a representation-existence obstruction.
  locally-affine-support-bcs-is-exactly-the-lcs-boundary: that gives an existential support criterion for extracting an LCS from a chosen non-CE trace; this proves that the canonical sign-corner trace fails that criterion maximally on the zero-noise TV torsor.
---

Let \(G\) contain a faithful copy of

$$
H=(C_2)^P,
\qquad n=|P|,
$$

and suppose the constant-minus-one element \(z\in H\) is central in \(G\).
Let \(\tau_G\) be the canonical group trace and put

$$
p_-=\frac{1-z}{2}.
$$

For every character \(\chi_\beta\in\widehat H\), indexed by
\(\beta\subseteq P\), let \(E_\beta\) be its minimal Fourier projection.
Then

$$
\tau_G(E_\beta)=2^{-n}                                 \tag{1}
$$

for every \(\beta\).  In the normalized central corner trace

$$
\tau_-(x)=\frac{\tau_G(p_-xp_-)}{\tau_G(p_-)},
$$

one has

$$
\tau_-(E_\beta)
 =\begin{cases}
   2^{1-n},&|\beta|\text{ odd},\\
   0,&|\beta|\text{ even}.
  \end{cases}                                          \tag{2}
$$

Thus the canonical \(J=-1\) corner is uniform on the entire odd affine
hyperplane.  The total mass on honest singleton dictators is

$$
\frac{n}{2^{n-1}},
$$

and the mass on odd nondictators is

$$
1-\frac{n}{2^{n-1}}.                                   \tag{3}
$$

For \(n=3\), the bad triple character already has mass \(1/4\).

More generally, quotienting \(H\) inside \(G\) only restricts the spectrum
to an affine character packet.  If every singleton dictator is still
present, the quotient kernel is trivial, so (1)--(3) return unchanged.

Therefore no source-dependent cyclic group extension can obtain the
dictator selector from the canonical central-sign corner alone.  A
trace-selected construction must add another reducing projection which
kills the bad \(E_\beta\)'s, or abandon faithful retention of the honest
torsor.  That extra projection is exactly the non-group BCS data missing
from an LCS presentation.

This is a no-go for the canonical sign corner, not for arbitrary signed
Hecke corners or noncanonical traces.  It does not construct a
nonhyperlinear group.
