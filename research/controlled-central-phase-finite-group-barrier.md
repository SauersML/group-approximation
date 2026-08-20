---
rg: 2
id: controlled-central-phase-finite-group-barrier
kind: claim
title: Universally sound finite groupification of a controlled central phase is necessarily affine
distinct_from:
  finite-selector-gadget-induction-barrier: that says every compatible selector character occurs after induction; this derives the precise consequence for a proposed selector-controlled central commutator and shows that uniqueness forces an affine character.
  schur-complement-controls-relative-pauli-module: that constructs the nonlinear phase exactly inside the distinguished finite packet algebra; this explains why naming that algebra element inside a finite overgroup cannot preserve the phase law in all representations.
---

Let `H` be a finite group, let `D=<z_1,...,z_k><=Z(H)` be a Boolean selector
subgroup, and let `c in Z(H)` be a central involution.  Suppose that for every
selector character `x in D^` there are representations of `H` above `x`, and
that **every** irreducible representation of `H` above `x` has

```text
c=(-1)^(f(x)) I.                                                    (NCG1)
```

Then `c in D`, and `f` is affine-linear over `F_2` (up to the harmless
constant determined by the convention for selector signs).

In particular, for nonlinear `f` the controlled phase `F_f` of `(SCP2)` can
exist in a distinguished semisimple packet representation, but no finite
group extension can make it a universally sound central group-element law.
Some irreducible representations of the extension necessarily have the same
selector character and the wrong value of the proposed phase.  Thus the
three-coefficient relative-Pauli frame is a valid additive/Wedderburn
coefficient compiler, while its sound return must use an infinite compressor,
a trace/corner condition, or another mechanism outside finite selector
groupification.

The bad sectors cannot be made Plancherel-negligible.  By
`regular-finite-controlled-phase-has-half-wrong-mass`, restriction of the
finite regular representation to `<D,c>` is uniform: unless `c` is an affine
selector word, exactly half of every selector sector has the wrong phase.
