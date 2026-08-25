---
rg: 2
id: corona-coefficient-module-decoder
kind: claim
title: Decode compatible finite root multiplicities into one finite projective corona module
---

OPEN.  Let `R` be a countable ring with a binary Leavitt family and let
`rho:E_n(R)->U(Q_d)` be a norm-corona representation in which a specified
finite-order root `rho(x_ij(r_0))` survives.  By
`torsion-normal-generator-has-full-support-corona-core`, one may assume that
the active spectral projection of this root has normalized coordinate rank
bounded below by one positive constant.

Construct a nonzero finitely generated projective `Q_d`-module `P_rho` and a
unital ring homomorphism

```text
R -> End_(Q_d)(P_rho).
```

The finite additive and Heisenberg multiplicity germs already provide exact
finite restrictions of the desired action.  The missing content is a
finite-projective coherence theorem assembling the compatible restrictions
on one common module of positive rank density.  Sparse escape of the marked
root is no longer part of the problem.  Moreover the active corner is a
uniform Morita generator: every finite packet projection embeds into one
fixed finite amplification of it.  Growth of the stabilization size is no
longer part of the problem either.

## Structural reductions

- **Take the inverse limit of rank germs.**  Compatible scalar ranks do not
  determine compatible projection representatives or coefficient
  intertwiners.  The resulting inverse-limit object can be countably
  generated while the cancellation theorem requires one nonzero finitely
  generated projective corona module.
- **Diagonalize coordinate exactifications.**  Each finite window can be
  exactified on a tail, but the conjugating corrections depend on the window.
  Their selected projections can move through the matrix coordinates and
  have zero common rank germ despite compatible restriction multiplicities.
- **Use the full active spectral corner as the carrier.**  Full-support
  reblocking makes this corner macroscopically large, but general coefficient
  roots move it.  The required theorem must coherently align finitely many
  moved copies or construct an equivalent invariant projective carrier.

## Remaining failed shortcuts

- **Use only the additive Fourier projections.**  This cannot recover the
  Leavitt arrows: one additive character can remain nontrivial on every
  prefix idempotent, so binary prefix projections do not split the active
  mass into two equivalent copies.
- **Exactify each finite Heisenberg window separately.**  This recovers each
  finite multiplication table, but the correcting unitaries and isotypic
  corners may depend on the window.  Branching compatibility of rank germs
  does not by itself produce nested coordinate projections in one fixed
  matrix amplification.
- **Take an inverse limit of multiplicity vectors.**  The inverse limit gives
  a coherent type measure, not a finitely generated projective `Q_d`-module.
  It does not control a uniform stabilization size or provide bounded
  operators realizing the four Leavitt coefficients on a common carrier.
- **Compress to the active spectral projection of the surviving root.**  Its
  relative rank is now uniformly positive, but general coefficient roots
  move it.  Repeated compression introduces boundary terms, and positive
  density alone does not make the two inverse relations exact in the corona.

- **Choose one nonzero irreducible summand at each growing finite window.**
  A rank-one projection on infinitely many coordinates already defines a
  nonzero finitely generated projective `Q_d`-module, so vanishing normalized
  density is not the obstruction here.  The obstruction is algebraic: an
  irreducible representation of one finite Heisenberg window supplies root
  unitaries and their multiplicity, but it does not canonically supply a
  unital map `R -> End_(Q_d)(P)` on the selected summand.  The exactifying
  conjugator and the selected summand may change with the window, and the
  coefficient arrows need not preserve their diagonal selection.

- **Use both branch character labels to remove the marginal ambiguity.**
  `binary-leavitt-two-branch-character-restriction-is-faithful` proves that
  the pair of global restrictions `(F_0 chi,F_1 chi)` determines `chi`
  exactly: additively `R=Rt_0 directSum Rt_1`.  This removes label ambiguity
  but not projection coupling.  The two branch conjugators carry the selected
  atom into projections which need not lie in one common abelian spectral
  algebra, and the group relations give no controlled nonzero meet or common
  intertwiner.  The missing decoder can therefore be stated more sharply as
  a joint-coupling theorem for the two uniquely labelled branch projections,
  not as another character-separation lemma.

- **Iterate the branch until multiplicity outruns the matrix dimension.**
  At every fixed depth `N`, the transverse shear gives a rank inequality of
  the form

  ```text
  2^N rank(P_n) <= d_n
  ```

  on sufficiently late coordinates.  Letting `N` tend to infinity only after
  the corona-coordinate limit forces normalized character mass to zero; it
  does not make the operator norm of a surviving rank-one projection small.
  Choosing `N=N(n)` after seeing `d_n` is not justified by pointwise corona
  relations: the relator defect can converge arbitrarily slowly compared with
  `d_n`, and simultaneous exactification constants grow with the moving
  window.  Such a moving-depth argument would need the same bounded-cost
  prototype or return-row control isolated in
  `binary-leavitt-three-row-atomic-compiler` and
  `opnorm-leavitt-coarse-fine-return-row`.

The unresolved statement is an intertwiner-coherence theorem: compatible
finite Heisenberg multiplicities, already aligned inside one fixed Morita
carrier, must admit a common summand on which the coefficient products act
coherently.
