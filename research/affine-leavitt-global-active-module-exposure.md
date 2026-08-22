---
rg: 2
id: affine-leavitt-global-active-module-exposure
kind: claim
title: Decode the whole affine-Leavitt last-column module with uniform actor energy
distinct_from:
  affine-leavitt-steinberg-hs-coefficient-decoder: that asks for one approximate relative Leavitt cell; this asks for a global additive root-module PVM and actor covariance instead.
  affine-leavitt-boundary-shear-payment: that asks for fixed-depth scalar estimates and allows constants to grow with depth; this asks for one uniform whole-module quasirepresentation.
  finite-presentation-must-expose-whole-module-with-uniform-defect: that is the abstract augmentation-module interface; this instantiates it in the active last-column root subgroup of the affine-Leavitt Steinberg presentation.
---

OPEN.  From every sufficiently accurate matrix tuple for the fixed finite
presentation of

```text
St_6(L_A(k[C_aff]))
```

construct a whole-module map

```text
phi:(A R)^5 -> U(d)
```

with a dimension-independent uniform all-pairs additive defect, preserving
`x_16(A)`, and with uniform transport energy under a fixed Kazhdan generating
set of the first-five-coordinate Steinberg actor.

Uniform abelian HS stability would round `phi` to one same-dimensional
finite-support PVM.  Then
`affine-leavitt-global-root-pvm-collapses-active-mark` finishes.

## Attempts

- **Add the same-root actor table and the full mixed multiplication
  triangles to the right-ratio model.**  This closes algebraically.
  `mixed-steinberg-triangles-transfer-actor-additivity` applies
  `[xy,c]=x[y,c]x^{-1}[x,c]` to

  ```text
  X(a)=x_ij(a),  C=x_j6(A),  Y(a)=x_i6(a).
  ```

  Uniform defects `epsilon` for actor-root addition, the mixed triangle and
  its centralizing row give active-root addition defect at most
  `6 epsilon`.  After the ten cross-coordinate swaps, the ordered
  five-coordinate section has whole-module defect at most
  `30 epsilon+10 eta`.  Hence no exact nonlinear partial graph-product model
  can retain a missing pair while satisfying all those rows.  The result is
  not yet a decoder from the finite presentation: its premise is the uniform
  all-coefficient additive table of the actor root itself.  Finite relators
  give this only pointwise with address-dependent area.  Mixed triangles
  therefore move the same uniform-exposure problem from the active column
  into an actor root at constant loss; they do not terminate it.

- **Use high transitivity to transport finitely many commutator rows.**
  `steinberg-actor-preserves-right-ratio-orbitals` gives an exact obstruction.
  The actor action is right-`AR`-linear, so the stabilizer of
  `v=(A,0,0,0,0)` fixes the whole right line `v(AR)` pointwise.  Every actor
  pair orbital therefore meets `{(v,vb):b in AR}` at most once (at most
  twice after forgetting order).  There are infinitely many such orbitals.
  For any finite family of prototype commutator rows, the graph product on
  the active vectors with precisely their actor-translated edges gives an
  exact semidirect-product model in which an unchecked pair remains
  noncommuting.  Thus neither rank-five elementary transitivity nor property
  `(T)` supplies the multiplication decoder.  The graph-product escape omits
  the additive and mixed Steinberg triangles, so those moving nonlinear
  loops are now the only possible source of uniform exposure.

- **Close one finite root Fourier window.**  It turns the coefficient shears
  into permutations of Plancherel atoms and erases the expanding boundary.
- **Increase the window depth.**  Word/area constants grow with the remote
  coefficient addresses, so no uniform all-pairs defect follows.
- **Use deterministic equivariant child maps.**  `rectangular-escape`
  enlarges the recovered label quotient while shrinking multiplicity in the
  same ambient matrix dimension.  Such finite-depth data do not assemble to
  one global covariant PVM.
- **Use the property-`(T)` character gap at fixed radius.**
  `finite-radius-active-character-packets-do-not-collapse-the-mark` gives an
  exact regular-PVM countermodel: every finite collection of additive tables
  and partial actor transports is compatible with canonical trace and a
  fully separated mark.  The failure moves into actor/mixed loops leaving
  the window.  Thus finite-radius orbit expansion yields no shrinking scalar
  remainder unless those loop words are charged by an additional boundary
  theorem.
- **Pass only to an exact qualitative ultraproduct representation.**
  `diffuse-active-spectrum-blocks-qualitative-collapse`
  shows why this loses the matrix-coordinate input.  The exact regular trace
  of the whole semidirect product has a diffuse Haar spectral measure, zero
  actor-covariance defect, and a fully separated active mark.  The discrete
  character-orbit gap acts on counting measure, not on this invariant Haar
  measure.  Thus the decoder must retain finite atomic coordinate PVMs and
  their boundary energy before taking the limit.
- **Close only one source/two-child Weyl cell.**
  `first-leavitt-weyl-cell-has-exact-rectangular-model` realizes the source
  pair as `M_p tensor 1`, the two children as the full `M_(p^2)`, and the
  second branch by tensor swap, all on one Hilbert space with exact returns
  and canonical Pauli traces.  It also gives the sharp next certificate: a
  fixed `s_(2p)` evaluation detects the factor growth independently of
  spectator multiplicity.  What is missing is a matrix-only mixed return
  placing that same target tuple back in the source factor.  Literal
  word-level confinement would also kill the regular representation and is
  therefore impossible.
- **Replace all virtual module words by finitely many bounded spectral
  probes.**
  `finite-bounded-spectral-probe-obstruction`
  proves that arbitrary bounded diagonal probes have a dimension-independent
  transport estimate exactly when their feature vectors are uniformly
  separated.  No finite bounded family separates an infinite character set.
  Leavitt self-similarity helps only if its branch words authenticate
  genuinely non-diagonal orthogonal domains; on one common carrier that is
  already the relative-Leavitt trace-collapse endpoint, while changing the
  carrier restores `rectangular-escape`.
- **Wordize the nonlinear fine-prefix atom with a finite balanced router.**
  `finite-router-fine-prefix-return-collapses-mark` shows that this succeeds
  locally but cannot be welded functorially to the existing prefix partial
  swap.  Such a weld would conjugate a marked Pauli half-projection of
  canonical trace `1/4` to a marked joint atom of trace `1/8`, contradicting
  the regular trace.  The router therefore does not supply the missing
  non-diagonal-domain authentication; the weld itself must use finite matrix
  coordinates or be charged as boundary leakage.

Accordingly the character-orbit backend does not prove the old
affine-Leavitt decoder.  It replaces the post-decoding Leavitt trace cell by
a cleaner property-`(T)` PVM endpoint.  The global exposure assertion is
stronger than the fixed-depth boundary estimate and is not known to be
equivalent to it; the rectangular model explains why every current local
extraction attempt fails at the same boundary/multiplicity interface.
