# Amenable near representations do not trigger hyperfinite HS stability

## 1. The apparent shortcut

Kahl--Schneider prove that a group is hyperlinear if and only if it admits an
essentially free amenable near representation.  Independently, the stability
theorem used in this repository proves hyperfinite Hilbert--Schmidt stability
for the relevant character-rigid higher-rank lattices.

If the two occurrences of “amenable” denoted the same hypothesis, a
hyperlinear approximation could be corrected to genuine finite-dimensional
representations.  For a non-residually-finite Kazhdan central extension, or
for a suitable known nonsofic quotient, that would give the desired
contradiction.

They are not the same hypothesis.

## 2. The two notions

An amenable unitary representation in the sense of Bekka is a representation

\[
\pi:G\longrightarrow U(H)
\]

for which there is a \(\pi(G)\)-invariant state on \(B(H)\).  Kahl--Schneider
characterize this by an orthonormal basis supporting an invariant finitely
additive probability charge.  Their amenable **near** representations retain
such a charge while requiring the multiplication law only almost everywhere
for that charge.

Hyperfinite HS stability has a different input.  It starts with a sequence of
finite-dimensional asymptotic representations, uses normalized matrix trace,
and assumes that the resulting tracial GNS von Neumann algebra is amenable
(injective/hyperfinite).  This is a countably additive tracial condition on
the normalized-rank limit.

An invariant probability charge may concentrate on sets of zero normalized
matrix density.  It therefore does not imply that the normalized-trace GNS
algebra of the extracted matrix microstates is amenable.  Conversely,
amenability of that GNS algebra does not provide the particular basis charge
required in the near-representation definition.

## 3. Why property (T) does not bridge the gap

For an **honest** Bekka-amenable representation of a property-(T) group,
almost invariant vectors in \(\pi\otimes\bar\pi\) produce an invariant vector,
and hence a finite-dimensional subrepresentation.  This is also why
factorization property plus property (T) leads to residual finiteness.

A near representation is not an honest representation.  Property (T) cannot
be applied before its multiplicative defect is repaired, and hyperfinite HS
stability repairs only when the normalized-trace limit algebra is amenable.
The invariant charge does not supply that missing premise.  The distinction
is load bearing: the Kahl--Schneider theorem characterizes all hyperlinear
groups, including hyperlinear property-(T) groups without factorization
property.

## 4. Consequence

The implication

\[
\text{hyperlinear}
\Longrightarrow
\text{amenable near representation}
\]

cannot be composed with hyperfinite HS stability.  It neither proves weak
ucp-stability nor makes Dogon's central-extension obstruction unconditional.
The negative-side target remains a genuinely tracial statement: either a
weak-ucp correction theorem for all hyperlinear approximations, or a direct
proof that one required twisted regular algebra is not Connes embeddable.

Primary source: P. Kahl and F. M. Schneider, *Hyperlinearity via amenable
near representations*, arXiv:2504.10988v2, especially the use of Bekka
amenability and finitely additive probability charges.
