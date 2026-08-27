---
rg: 2
id: finite-clifford-couplings-cannot-prune-a-forbidden-atom
kind: claim
title: No finite Clifford coupling can delete a forbidden selector atom from the marked face
distinct_from:
  finite-selector-gadget-induction-barrier: that states the general character-induction obstruction for a finite overgroup; this applies it to the C direct-sum M2 Fourier router, tracks the forbidden projection in the two router summands, and includes the selector-collapse alternative.
  balanced-fourier-routers-retain-every-assignment-sector: that treats the uncoupled tensor attachment and constructs all bad sectors explicitly; this permits arbitrary additional ordinary group-word relations inside one finite coupled gadget and proves induction recreates a forbidden sector anyway.
  controlled-central-phase-finite-group-barrier: that proves a universally prescribed central phase function must be affine; this treats the stronger desired support equation P_forbidden=0 and shows exactly where the forbidden projection survives.
  bcs-projective-kernel-phase-compilation: that remains open to infinite/state-dependent payload couplings; this rules out every fixed finite-group controlled-Clifford or partial-swap predicate gate.
---

Let `D=<J,z_1,...,z_k>` be the finite abelian selector group for one predicate,
with `J` the central marked involution.  For a Boolean assignment `a`, let

```text
P_a=product_i (1+a_i z_i)/2 in C[D]                  (FCC1)
```

after the harmless sign-convention choice, and suppose `a` is forbidden.
Attach the corrected Fourier router on some shared selector `S in D`, and
then impose **arbitrary additional ordinary group-word relations**, with the
resulting coupled gadget still a finite group `G` containing `D` and with
`J` central and nontrivial.

Let `chi_a` be the character of `D` selected by `a` and `chi_a(J)=-1`.
Consider the finite-dimensional induced representation

```text
Pi_a=Ind_D^G(chi_a).                                    (FCC2)
```

Centrality of `J` gives

```text
Pi_a(J)=-I,                                             (FCC3)
```

while the canonical inducing subspace is a nonzero `chi_a`-weight space.
Therefore

```text
Pi_a(P_a)!=0.                                           (FCC4)
```

Equivalently, some irreducible constituent of `(FCC2)` is a marked
finite-dimensional representation in which the forbidden projection is
nonzero.  Thus no relation table of a fixed finite coupled group can force

```text
J=-1  implies  P_a=0.                                  (FCC5)
```

Controlled Clifford automorphisms, CNOT/CZ words, finite Heisenberg packets,
and finite partial-swap completions do not affect the argument: they merely
change the finite overgroup `G` from which `(FCC2)` is induced.

The surviving representation lies in the precise router sector found in
`balanced-fourier-routers-retain-every-assignment-sector`.  Since `S in D`
acts by the scalar `chi_a(S)` on the forbidden weight space:

- if `chi_a(S)=-1`, the NAND router relations force `A=B=1`, so `(FCC4)`
  survives in the scalar `C` summand;
- if `chi_a(S)=+1`, the router relation forces anticommuting `A,B`, so the
  generated orbit of that weight contains the Pauli `M_2(C)` summand.

Hence a predicate with forbidden assignments in either selector fiber cannot
be pruned in that fiber; if it has forbidden assignments in both, neither
router summand can be made sound.

There is only one way for a finite presentation to evade induction: make the
map `D->G` noninjective, so `chi_a` is no longer a character of the selector
image.  But the characters surviving a quotient of the elementary abelian
selector group are the annihilator of its kernel, an affine-linear Boolean
subspace.  A finite group relation among selector words can therefore impose
only affine parity restrictions; it cannot retain an arbitrary nonlinear
predicate truth set.  Collapsing `J` also destroys the marked tracial model.

The same no-go holds for a residually finite coupled group in which `D`
embeds.  Residual finiteness supplies one finite quotient injective on the
finite set `D`; induce `chi_a` in that quotient and pull the representation
back.  Consequently the first locally sound predicate gate, if it exists,
must use an infinite non-residually-finite/state-dependent coupling, a
trace/corner condition not expressible by universal group words, or an
approximation-rigidity mechanism.  No fixed finite-group Fourier/Clifford
cell can close projective-kernel phase compilation.

