---
rg: 2
id: leavitt-character-mass-escapes-to-finer-characters
kind: claim
title: Leavitt character mass escapes to finer characters as the matrix dimension grows
distinct_from:
  bare-self-copy-mf-calibration: that exhibits one torsion-free finitely presented operator-MF group in which a nontrivial compression defect survives a norm corona, calibrating the phase boundary by example; this identifies the mechanism by which one specific finite-dimensional argument, the Leavitt branch multiplicity doubling, fails to transfer, and does so without exhibiting a group.
  character-diracization-limit: that drives every character to the regular character of its scalar-kernel quotient using conjugate tensor powers; this is about where the multiplicity mass of the branch-doubling argument goes as the matrix dimension grows, and its compatibility with a diffuse CAR/UHF limit, with no tensor power taken.
  compression-defect-dies-in-finite-dimensions: that is a theorem about honest finite-dimensional representations; this is a negative statement about approximate finite-dimensional microstates, saying that this particular mechanism has no microstate analogue.
  atomic-morita-return-kills-finite-order-mf-mark: that is the conditional collapse theorem which does succeed at the microstate level, given a coefficient return on a prescribed spectral atom; this explains why such a return has to be assumed rather than derived from the finite-dimensional mechanism.
artifacts:
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
  - GroupApproximation/Criterion/FiniteDimensionalKill.lean
---

**ESTABLISHED OBSTRUCTION.**  The recurrence `(MD)` of
`leavitt-heisenberg-branch-doubles-character-multiplicity` does **not** pass to
matrix microstates, and the reason is sharper than "the support refines".

`(MD)` needs a multiplicity function `m` on ONE common global character space,
together with a global endomorphism pullback `F` of the dual of `(R,+)`.  A
fixed finite root packet supplies neither.  Keep only a finite source subgroup
`A` and its branch image `A t_0`.  An approximate model can be exactified on the
finite abelian group they generate, and its spectral data are **joint
characters** of that finite group.  Conjugacy of source and branch then forces
equality only of two **marginal** multiplicity distributions.  The transverse
shear still pairs characters inside fibers of the branch marginal — but a
uniform, or otherwise spread, coupling satisfies both marginal constraints
without any doubling.  The invalid step is writing

```text
m(psi) = sum_(F chi = psi) m(chi)
```

for a single `m` when the finite window only exposes two marginals of a joint
distribution.  That is the **finite-window marginal loophole**, and it is where
the finite-dimensional recurrence disappears on truncation.

The corresponding diffuse limit is realized: an infinite CAR/UHF-type model of
the Leavitt relations has exactly this behaviour, `(MD)` holds there, and it is
vacuous.

There are two exact refinements of this diagnosis.

* `finite-branch-closure-erases-transverse-character` proves that a finite
  coefficient packet which is literally closed under the injective branch
  cannot retain the nonzero dual-kernel direction used by the shear.  Thus
  making one fixed window branch-invariant destroys the doubling input.
* `norm-corona-sparse-global-character-atom` shows that operator norm can
  nevertheless select a nonzero global character projection from a surviving
  elementary-abelian involution.  The obstruction is therefore not mere
  absence of atoms: the selected sparse atom need not be the whole returned
  multiplicity sector, so the two branch copies can escape into a larger
  reservoir.

Two consequences worth stating separately.

1. **Full orthogonal self-copy, elementary commutator calculus, and normal
   generation are jointly insufficient** at the microstate level.  This is not a
   failure of algebra -- every relation still holds; see
   `orthogonal-root-self-copy-is-mf-compatible` for a group where all three hold
   and MF survives.

2. **Replacing property (T) by spectral-gap language on the character side does
   not solve it.**  Such a hypothesis is exactly an assumption that the window
   does not truncate the reservoir, i.e. it reintroduces the missing global
   `m` by fiat rather than proving it.

What is needed is a **finite-coordinate return** that puts branch and shear in
the SAME multiplicity reservoir -- the role played by
`binary-leavitt-atomic-morita-return`, still open, and why
`atomic-morita-return-kills-finite-order-mf-mark` takes that return as a
hypothesis instead of deriving it.

## Attempts

- Uniformizing `(MD)` over the model sequence: the doubling constant is
  already uniform, so this changes nothing; the failure is in the index set,
  not the constant.
- Coarsening the character space to a fixed finite quotient before applying
  `(MD)`: the translation `tau` is not constant on the coarsening, so the
  companion character can collapse onto the original and the doubling is
  lost.
- Selecting a sparse global operator-norm atom: this succeeds, but branch and
  shear return equivalent copies only inside a larger character sector and do
  not prove that the selected atom is properly infinite.
