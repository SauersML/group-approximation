---
rg: 2
id: row-glued-magic-squares-absorb-noncommuting-ports
kind: claim
title: Row-glued Magic Squares absorb arbitrarily many noncommuting source ports in one Pauli ancilla
artifacts:
  - research/common-interface-controlled-gadget-absorption-proof.md
distinct_from:
  magic-square-one-port-is-a-universal-phase-absorber: that treats one port and commuting central profiles; this allows arbitrarily many mutually noncommuting ports in a connected gadget whose squares share an entire context.
  join-tree-overlap-gadgets-have-no-contextual-escape: that rules out acyclic contextual incidence; this is cyclic and connected, but constructs an exact finite-dimensional absorber from a port-independent shared frame.
  finite-k-commuting-face-universal-completion: that seeks a noncentral growing-code coupling; this proves that a common finite Pauli face alone remains inert even when every attached port is noncommuting.
---

A general common-interface lemma holds.  Let a finite gadget have a binary
port sign `epsilon in {+1,-1}` and suppose it has two same-dimensional exact
operator solutions `pi_+` and `pi_-` for the two signs.  If the solutions
agree exactly on a designated interface tuple `Q`, then any family of copies
of the gadget, glued along `Q` and attached to arbitrary source involutions
`z_1,...,z_k`, has an exact operator solution after one fixed finite
amplification.  The `z_t` need not commute.

Indeed, in copy `t` use the spectral projections of `z_t` to control
`pi_+` and `pi_-`.  On the interface the two blocks are identical, so every
copy gives the same operators `I tensor Q` even though the different spectral
projections need not commute.

The Magic Square satisfies this hypothesis with a full three-cell row as
interface in dimension four.  There are two commuting-grid solutions
`A^+` and `A^-` such that

```text
all six line products of A^+ are +I,
five line products of A^- are +I and its last column is -I,
A^+_(1j)=A^-_(1j) for j=1,2,3.                          (RGM1)
```

Therefore form `k` Magic Squares, identify all their first-row variables,
and set the exceptional column product in copy `t` equal to `z_t`.  Every
representation `rho` of the source extends on `H tensor C^4`, with dimension
multiplied by four independently of `k`.  Restriction gives the converse.

This is already a connected cyclic incidence gadget with an entire shared
commuting context and arbitrarily many noncommuting source ports.  It cannot
remove a finite-dimensional long-code cheat or create a
finite-versus-commuting perfectness separation.

Hence `two noncommuting ports in one connected network` is not yet the right
escape criterion.  A live coupling must have a port-dependent shared
interface: the positive- and negative-port solutions must fail to admit any
common finite-dimensional interface frame, even after amplification and
unitary alignment.  The smallest unaudited cases are a single Magic Square
with ports on two distinct line contexts, or two contextual cycles sharing
transverse cells whose relative Pauli frame is forced.
