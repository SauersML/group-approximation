---
rg: 2
id: authenticated-core-union-basin-is-relative-liftability
kind: claim
title: Retraction to the union of endpoint fibers is exactly relative ultraproduct liftability
distinct_from:
  regular-iwahori-relative-congruence-exactification: that is the open arithmetic correction theorem; this gives its exact authenticated-core ultraproduct normal form and separates what Selberg does after a lift from the lift itself.
  congruence-endpoint-orbits-are-restriction-ring-fibers: that classifies and metrizes the exact zero set at every finite level; this proves that retraction to the union of those zero sets is an additional lifting property.
  bs14-thresholded-newton-needs-coordinate-basin: that states the mixed-norm local Newton theorem and its missing coordinate basin; this identifies that global basin with a relative lift of an ultraproduct homomorphism.
  exact-torsion-frame-has-rank-one-strict-counterpackets: that refutes same-dimensional lifting with a concrete boundary compression; this incorporates that example and leaves precisely the flexible lift.
  one-core-endpoint-union-is-one-finite-restriction-fiber: that collapses the exact endpoint union over each coordinate core to one finite restriction fiber; this identifies the remaining uniform moving-level lift rather than the coordinatewise exact type space.
---

Let `Q_n` be moving odd congruence quotients, let

```text
beta_n:K -> U(d_n)                                       (AUL1)
```

be exact authenticated BS-core representations, and let `X_n` have all
four square-free relative defects tending to zero.  In the tracial matrix
ultraproduct, the classes of `(X_n,beta_n)` define an exact homomorphism

```text
Pi:A=PSL_2(Z[1/2]) -> product_omega M_(d_n)              (AUL2)
```

extending the prescribed core embedding `[beta_n]`.

Retraction of `X_n` to the **union** of all exact endpoint orbits over
`beta_n`, with `o(d_n)` flexible padding allowed, is equivalent to the
following relative liftability statement for `(AUL2)`:

> after passing to the representing sequence, there are exact
> finite-dimensional congruence representations `pi_n` on dimensions
> `D_n=d_n+o(d_n)` and almost-full isometries whose compressed generator
> tuples converge in normalized HS to `(X_n,beta_n)`.

At a fixed level and dimension, the possible lift types are exactly the
nonnegative restriction-ring fiber

```text
F_(beta_n)={m>=0:res_(Q_n)^K(m)=[beta_n]},              (AUL3)
```

by `congruence-endpoint-orbits-are-restriction-ring-fibers`.  Once a type
`m_n` and a lift have been produced, the uniform Selberg gap controls the
normal distance to its core-commutant orbit.  It does **not** produce
`m_n` or the coordinate lift from the exact ultraproduct homomorphism.

In fact the ambient finite quotient need not be guessed separately after
the core is fixed.  If `N_n=ord(beta_n(s))`, then
`one-core-endpoint-union-is-one-finite-restriction-fiber` puts **every**
same-dimensional exact endpoint over `beta_n` in the finite quotient
`A/<<s^(N_n)>>` and in one finite restriction fiber there.  The obstruction
is therefore not an infinite choice at one coordinate; it is the lack of a
uniform lift while `N_n` and the finite fibers move.

This distinction is sharp.  Cuspidal restriction-kernel moves show that no
preferred fiber point can be selected from the core or the limiting
character.  Compressed even-Weil packets show that a lift can require an
extra boundary dimension even when every residual tends to zero; hence the
same-dimensional version is false.  Their one-line completion is compatible
with the flexible formulation and does not refute it.

Therefore uniform Selberg normal coercivity plus compactness of each finite
fiber does not prove the global union-basin theorem.  A failed flexible
union-basin sequence is precisely a non-liftable relative ultraproduct
extension `(AUL2)`.  Excluding such extensions, or reconstructing their
energy-controlled boundary carriers, is the remaining arithmetic theorem.

The literal central-idempotent shortcut is now fenced by
`raw-core-central-reynolds-authentication-is-circular`.  The exact core does
canonically reveal the finite level `N_n`, but not the point of the
restriction fiber: exact cuspidal redistributions have the same core and
different positive-density endpoint central profiles.  Evaluating the full
central idempotents on the approximate tuple first requires a word-section
multiplication table; the cyclic core character proves that every frozen-core
section has nonuniform RMS filling cost.  Once a lift supplies such a table,
uniform Reynolds/polar repair is already available.  Thus central averaging
does not insert an intermediate theorem between `(AUL2)` and its coordinate
lift.

The intrinsic metric here must quotient the entire exact core-commutant
fiber, not a preselected cyclic-packet splitting.
`exact-cuspidal-hadamard-mixing-has-macroscopic-cross-blocks` gives exact
zero-energy extenders with fixed positive off-diagonal packet mass, produced
by a core-commuting Hadamard between duplicate restrictions.  After this
quotient, `core-commutant-quotient-normal-gap-is-relative-liftability`
records the quantitative remainder.  Property `(tau)` repairs the normal
part only after a coordinate endpoint lift is selected; before selection
there is no genuine second representation on which to apply its bimodule
gap.  Even qualitative liftability still needs a legal core-preserving
truncation of operator-hard, rank-paid normal tails to yield a uniform
linear modulus.

The finite-dilation boundary is now exact.
`tfd-finite-corner-collapse-and-rfd-firewall` proves that **any**
finite-dimensional exact corner dilation of `(AUL2)`, even in an
arbitrarily larger ambient dimension, automatically reduces by property
`(T;FD)` to a congruence endpoint on `d_n+o(d_n)` dimensions.  Thus
padding control is not an extra gate after a finite corner is found.
However the LLP/RFD very-flexible theorem cannot find that corner:
`C^*(SL_2(Z[1/2]))` is not RFD, because RFD plus `(T;FD)` would imply
full property `(T)`.  LLP alone yields only a possibly
infinite-dimensional Stinespring corner, and current MF amalgam theorems
produce existential norm embeddings rather than coordinate lifts of this
prescribed tracial homomorphism.  The surviving gate is exactly
finite-dimensional relative lift production.


The finite-corner target has an exact finite-window certificate.
\`finite-positive-definite-window-is-a-relative-corner-selector\` shows that
a positive operator-valued Toeplitz matrix on the finite one-power quotient,
agreeing unitarily with the core and approximating the prescribed marked
tuple, has a finite-dimensional Stinespring representation; property
\((T;FD)\) then completes the flexible lift.  Equivalently, one may control
the RMS multiplication table of a complete finite quotient window.

This formulation also makes the LLP/local-reflexivity gap literal.
\`exact-core-multiplicative-domain-does-not-descend-to-normal-quotient\`
gives a two-dimensional minimal Stinespring representation which is exactly
multiplicative on a cyclic core but detects a conjugate of the killed core
relation.  Thus \(\Theta(t^N)=1\) controls only the vacuum row; quotient
descent needs all translated normal-closure rows.  Finite-dimensional core
expectations, scalar quasidiagonal trace models, and restriction-ring
separation do not supply those operator-valued rows.


There is also a sharp complete-order firewall before the translated rows can
be lifted.  `finite-nuclear-quotient-does-not-complete-partial-toeplitz-data`
puts anticommuting Pauli involutions on the two edges of the square
(C_2	imes C_2).  The data are positive on every allowed local face, but
remain at normalized-HS distance at least ((3-sqrt5)/4) from every full
positive-definite group table.  The target algebra is finite-dimensional,
nuclear, LP/LLP, locally reflexive, quasidiagonal, RFD, and MF.  Consequently
none of those ambient properties turns facewise positivity into the complete
finite quotient window: LLP can lift a ucp map on the *concrete* Fourier
operator system only after arithmetic compatibility with all cross-difference
rows has been proved.


At a fixed one-power level the relative ucp search now has a universal
finite host.  By
\`every-relative-ucp-window-lives-in-one-induced-representation\`, every
positive kernel exact on \(\beta_n\) is a compression of the single
representation

\[
\operatorname{Ind}_{B_{N_n}}^{A_{N_n}}\beta_n .
\]

Thus finite-corner production is equivalent to finding a
\(B_{N_n}\)-intertwining isometry whose compressed extender approaches
\(X_n\).  The explicit unitary-fibre subfamily in
\`right-core-cayley-average-gives-toeplitz-window\`
reduces this to a double-coset synchronization energy.  Its zero set is
exactly the endpoint set, but no uniform moving-level estimate is known.
