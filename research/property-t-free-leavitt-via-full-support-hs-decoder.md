---
rg: 2
id: property-t-free-leavitt-via-full-support-hs-decoder
kind: route
title: Reblock a surviving torsion root and invoke the positive-density coefficient decoder
target: property-t-free-leavitt-full-mf-radical
requires:
  - torsion-normal-generator-has-full-support-corona-core
  - full-leavitt-idempotent-defect-saturation
  - coherent-heisenberg-multiplicity-decoder
  - tracial-projective-hilbert-hotel-cancellation
---

Suppose a norm-corona representation of the binary-Leavitt elementary group
keeps the distinguished involutory root nontrivial.  The root normally
generates the finitely generated elementary group, so the active-core theorem
reblocks the representation as an operator-norm asymptotic representation
on matrices `M_(k_n)` for which the root's nontrivial spectral projection has
normalized rank bounded below.

Operator-norm multiplicative defects also vanish in normalized
Hilbert--Schmidt norm.  The reblocked sequence is therefore a positive-density
Hilbert--Schmidt microstate sequence of exactly the kind consumed by the
coherent Heisenberg multiplicity decoder.  That decoder supplies a
positive-density matrix corner carrying an asymptotic binary Leavitt module.
Tracial projective Hilbert-hotel cancellation, equivalently the finite-matrix
Leavitt trace floor, makes such a corner impossible.

Thus every norm-corona representation kills the distinguished root.  Normal
generation then kills the whole elementary group, proving that its MF
radical is the entire group.
