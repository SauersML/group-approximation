---
rg: 2
id: fanizza-one-sided-pulse-decoder-proof
kind: route
title: Sum the oriented rank jumps through affine returns and first-hit exits
target: fanizza-one-sided-pulse-ladders-give-computable-decoder
requires:
  - fanizza-final-bcs-has-fixed-nonlinear-menu
  - fanizza-fixed-nonlinear-menu-has-small-rank-gates
  - every-forbidden-atom-has-fixed-schur-pauli-words
  - relative-pauli-child-split-gives-one-exit-copy
  - schur-atom-central-product-has-s3-endpoint-split
  - fanizza-c18-residual-factors-through-three-tiny-rank-gates
  - oriented-c18-rank-gates-give-branch-balance
  - c18-source-cut-has-sparse-relator-certificate
  - finite-schur-clifford-packet-flexible-hs-exactification
  - fixed-bcs-context-rounding-gives-commuting-strategy
  - s3-active-complement-is-three-equal-scale-affine-atoms
  - two-bit-tag-routing-splits-s3-exit-and-survivor
  - tagged-s3-survivor-installs-next-recurrent-carrier
  - mixed-cnot-allowed-active-return
  - branching-plus-first-hit-exits-forces-hs-floor
  - thompson-free-occurrence-amalgam-preserves-contextuality
  - context-local-schur-packet-marked-extension
  - gauge-doubling-gives-selector-flip-symmetries
---

The finite-presentation assertion is obtained role by role.  A free Thompson
occurrence orbit is finitely presented by `(TFO2)`.  One two-bit endpoint/tag
bridge prototype, one tag-to-successor commutator prototype per shared
generator, and finitely many point-stabilizer and off-diagonal relations
generate their whole level families.  The prefix-table proof gives polynomial
area for the level-`n` instances.  There are
only finitely many roles at fixed `m`, so their central product and the
finite amalgamations over the original shared BCS involutions are finitely
presented.  Different contexts share exactly their retained logical words;
their private occurrence groups have no cross-context commutators.

Fix a matrix tuple and write `E` for its total squared named-relator energy.
Exactify each fixed finite packet.  The number and size of packets used at a
fixed level are bounded independently of the level, while transporting them
to level `n` costs polynomial relator area.  The pointwise oriented
identities `(OCB2)` give the first two lines of `(FPL2)` for C18.  For every
bad atom of C13/C14 and C17, `(PCS4)` and `(SCP3)` give the same two-child
identity with one active and one exit copy; the finite menu makes the sum
uniform at fixed `m`.  The two-bit tag table gives a genuine local partition:
its distinguished atom is the exit and the other three atoms are the
survivor.  The still-separate incidence theorem
`tagged-s3-survivor-installs-next-recurrent-carrier` is exactly what places
that survivor in the next reducing occurrence and proves the third and
fourth lines.  Telescoping its polynomial-area estimates proves `(FPL3)`.

Apply `(BFE6)`.  For each role there is a computable polynomial `K_r(N)` with

```text
eta_r N q_(r,0)<=1+K_r(N)sqrt(E).                      (1)
```

Choose computable `C,d>=1` so that every `K_r(N)<=C(1+N)^d`.  For
`0<E<1`, take

```text
N(E)=floor(E^(-1/(4d))).                               (2)
```

After harmless enlargement for small `N`, `(1)--(2)` give

```text
q_(r,0)
 <= C'_r(E^(1/(4d))+E^(1/2-(d-1)/(4d))).              (3)
```

The sparse C18 source certificate and the two other fixed truth-table cuts
bound the base forbidden mass by a fixed sum of `(3)` and packet-rounding
terms.  Summing over the computable finite role set produces the effective
modulus `omega_m(E)->0`.

Apply `fixed-bcs-context-rounding-gives-commuting-strategy`.  It rounds each
original BCS involution once for Bob, exactifies each elementary-abelian
context for Alice, and realizes the two tables by left and right multiplication
on the tracial Hilbert--Schmidt GNS space.  Thus the measurements commute
exactly even though the two rounded tables need not commute in the original
matrix algebra.  Its consistency loss and the forbidden mass above construct
`S_E`.  Spectral rounding of `U(d_m)` gives `X_(D,m)` and
`nu_m(E)=O(sqrt(E))`, proving `(FPL1)`.

For exact completeness, conditional on that same incidence theorem, start
from the perfect marked BCS GNS model.  Apply gauge-orbit covariantization
and one common countable amplification.  The
context-local packet extension realizes every base occurrence.  Fold the
free occurrence copies onto those base models.  Represent every tag pair by
the corresponding packet endpoint pair and every endpoint/tag bridge by the
identity.  This retains all allowed endpoint characters, including the
formerly missing `K=+1,b=-1` atom.  All exit carriers vanish in the perfect
model.  The resulting representation
of `Gamma_m` agrees with the original representation on every retained BCS
word.

The former proof using an affine HNN return and an *independent* binary pulse
is not used here.  It is false even at zero defect by
`free-occurrence-hnn-return-does-not-preserve-first-hit-prefix`: free
amalgamation lets the returned active summand and the pulse sign be chosen
independently.  The two-bit tag repairs the local nonlinear split, and
`tag-centralized-successor-corner` attaches its survivor to the next full
occurrence.  This still does not prove the route: the resulting zero-error
ledger is valid in the regular trace and is invalidated by
`exact-first-hit-ladder-kills-regular-carrier`.  A matrix-only multiplicity
decoder remains missing.
