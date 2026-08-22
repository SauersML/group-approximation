---
rg: 2
id: central-selector-spectra-cannot-prune-a-nonlinear-predicate
kind: claim
title: Infinite central-selector gates cannot prune a nonlinear predicate sector
distinct_from:
  regular-trace-blocks-exact-local-predicate-return: that computes positive canonical mass for every marked atom and rules out trace-functorial exact returns; this adds the complete finite-dimensional central-character classification and explicitly covers infinite non-residually-finite central extensions.
  finite-clifford-couplings-cannot-prune-a-forbidden-atom: that induces forbidden characters through finite or residually finite overgroups; this requires neither finiteness nor residual finiteness and uses tensor closure of finite-dimensional central characters.
  controlled-central-phase-finite-group-barrier: that proves affinity for a universally scalar phase word in a finite group; this treats arbitrary infinite groups and the set of selector characters for which any finite-dimensional marked representation exists.
  deligne-maslov-sector-traces-are-central-regular: that classifies traces for one particular Deligne extension; this is an elementary theorem for every central extension and shows what Deligne-type finite-dimensional invisibility can and cannot select.
---

Let `Gamma` be an arbitrary discrete group, finite or infinite and with no
residual-finiteness assumption.  Let `J in Z(Gamma)` be a nontrivial central
involution and let

```text
D=<J,z_1,...,z_k> <= Gamma                               (CSP1)
```

be a finite elementary abelian selector subgroup; the `z_i` need only
commute for the tracial obstruction below.

## Every marked selector atom occurs in a tracial representation

Put `q_-=(1-J)/2`, a nonzero central projection of `L(Gamma)`, and normalize
the canonical trace on the finite corner:

```text
tau_-(x)=tau_Gamma(x)/tau_Gamma(q_-)=2 tau_Gamma(x).
```

For every character `chi in hat D` with `chi(J)=-1`, its Fourier projection

```text
p_chi=|D|^(-1) sum_(d in D) overline(chi(d)) d          (CSP2)
```

satisfies `q_- p_chi=p_chi` and

```text
tau_-(p_chi)=2/|D|>0.                                   (CSP3)
```

The corner representation `g |-> q_- g` is a unital group representation
into the finite tracial von Neumann algebra `q_-L(Gamma)`.  Thus no group
presentation which retains `D` and central `J` can make a forbidden marked
selector character absent from **every tracial representation**.  This is
true for non-residually-finite and Deligne-type central extensions just as it
is for finite groups.

If relations collapse `D` to an image `D'`, the same calculation gives every
character of `D'` positive marked regular-corner mass.  Hence the exact set
of selector characters which can remain is the annihilator of
`ker(D->D')`, intersected with the `J=-1` hyperplane: an affine Boolean
subspace.  Universal group words cannot cut a proper nonlinear subset out of
that marked slice.

## Finite-dimensional central characters also form an affine slice

Assume now that `D<=Z(Gamma)`, as in a central-word predicate compiler, and
define

```text
Sigma_fd={chi in hat D : some nonzero finite-dimensional unitary
          representation pi of Gamma has pi(d)=chi(d)I for d in D}.
                                                                  (CSP4)
```

Then `Sigma_fd` is a subgroup of `hat D`.  The trivial representation gives
the identity character; tensor products multiply central characters; and
contragredient representations invert them.  Consequently

```text
Sigma_fd^-={chi in Sigma_fd:chi(J)=-1}                  (CSP5)
```

is either empty or a coset of the subgroup
`{chi in Sigma_fd:chi(J)=+1}`.  For Boolean selectors it is therefore an
affine subspace of the assignment cube.

This completely describes what an infinite non-residually-finite central
extension can accomplish at the exact finite-dimensional level.  It may make
`Sigma_fd^-` empty (finite-dimensional invisibility of `J`) or restrict it to
an affine coset, as Deligne-type examples do.  It cannot keep all satisfying
characters of a predicate whose truth set is not an affine coset while
deleting all forbidden characters.  In particular it cannot implement NAND
or the general nonlinear context supports needed by the fixed non-RU BCS.

The theorem does not rule out a **matrix-only approximation gap** which
allows the regular marked trace `(CSP3)` but proves it nonapproximable by
matrices.  That is a different, genuinely global stability/nonhyperlinearity
mechanism.  It does decisively fence the requested exact local gate: neither
tracial character absence nor exact finite-dimensional nonlinear pruning can
come from any central-selector group extension alone.

