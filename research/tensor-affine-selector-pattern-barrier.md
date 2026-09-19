---
rg: 2
id: tensor-affine-selector-pattern-barrier
kind: claim
title: Scalar selector patterns realized with a fixed phase form an affine set under tensor products
distinct_from:
  fixed-central-phase-scalar-profiles-form-coset-subgroup: that is the arbitrary order-m theorem; this is its Boolean sign specialization and records the one-hot selector consequence in the BCS vocabulary.
  one-hot-selector-parity-barrier: that is a syntax theorem for affine equations; this is a representation-theoretic theorem and allows arbitrary payload relations.
  finite-group-selector-induction-barrier: that realizes every character of a commuting selector subgroup inside a finite gadget; this theorem instead applies to any group or compiled presentation and only assumes several scalar selector patterns are already realizable.
  zpc-readable-control-freezing-to-lcs: freezing does not supply scalar branch representations, because remote unreadable operators may move global readable atoms; this theorem explains why that missing invariance is not a cosmetic issue.
---

Let `Gamma` be any group with a distinguished element `J` and distinguished
elements `z_1,...,z_m`.  Let `Sigma_fd subset {+1,-1}^m` be the set of scalar
selector patterns for which there is a nonzero finite-dimensional unitary
representation

```text
pi:Gamma -> U(V)
```

such that

```text
pi(J)=-I,
pi(z_i)=epsilon_i I               for every i.
```

Then either `Sigma_fd` is empty or, after identifying signs with `F_2`, it is
an affine subset of `F_2^m`.

This is the `m=2` instance of
`fixed-central-phase-scalar-profiles-form-coset-subgroup`; the direct ternary
proof is retained because it is the form consumed by the Boolean selector
nodes.

The same conclusion holds if "finite-dimensional unitary representation" is
replaced by a representation in any tensor-closed class for which the scalar
phase `-1` is preserved by an odd tensor power, for example tracial
representations on finite von Neumann algebras.

Consequently, for `m>=3`, no presentation can have **exactly** the one-hot
family

```text
{e_1,...,e_m}
```

as its finitely realizable scalar `J=-1` selector sectors.  More generally, if
all one-hot sectors are finitely realizable, their affine hull contains
additional spurious sectors which are finitely realizable as well.

This is independent of how nonlinear or noncommutative the payload relations
are.  Payload coupling can evade the theorem only by ensuring that the desired
perfect tracial model does not split into individually realizable scalar
selector sectors.  That is exactly the subtle regime of the ZPC-IRS witness:
the global readable spectral atoms need not be invariant under remote
unreadable generators.
