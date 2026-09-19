---
rg: 2
id: fixed-group-algebra-polynomials-cannot-supply-atomic-return
kind: claim
title: Fixed group-algebra polynomials cannot supply the three Atomic Morita Return rows
distinct_from:
  universal-block-return-violates-the-regular-firewall: that rules out a fixed proper-corner conjugacy and its two cyclic products; this applies the full three-row Atomic Leavitt Gap directly to arbitrary compressed group-algebra polynomials on the marked involution atom.
  binary-leavitt-atomic-morita-return: that permits coordinate-dependent operators selected from the finite matrix coordinate; this rules out only representation-functorial formulas in fixed group-algebra polynomials and finite Fourier or Pauli packet projections.
  group-algebra-coefficient-trace-separates-leavitt-corners: that uses the coefficient-of-identity trace over F_2 to distinguish two modular group-algebra idempotents; this uses the canonical complex finite trace and the prescribed spectral projection of an involution.
---

**ESTABLISHED SHARP GROUP-ALGEBRA FIREWALL.**  Let `Gamma` be any group,
let `z!=1` be an involution, and put

```text
p=(1-z)/2 in C[Gamma].                                 (FGP1)
```

For every `k>=1`, write `P=p tensor I_k`.  If

```text
s_0,s_1,t_0,t_1 in P M_k(C[Gamma]) P                  (FGP2)
```

are arbitrary fixed finite group-algebra polynomials -- in particular,
arbitrary finite linear combinations of actual Steinberg root words -- then
their images in the left regular finite von Neumann algebra satisfy

```text
1 <= ||t_0s_0-P||_op
    +||t_1s_1-P||_op
    +||s_0t_0+s_1t_1-P||_op.                          (FGP3)
```

Consequently at least one of the three binary Atomic Morita Return defects
is at least `1/3`.  This remains true if each displayed polynomial is first
compressed by `P`, and it remains true after any common matrix
amplification.

For the literal target group, take

```text
Gamma=St_20(L_(F_2)(1,2)),             z=x_13(s_1t_1).
```

The root relation in characteristic two makes `z` an involution, and its
nontriviality is already established.  Therefore `(FGP3)` applies to every
finite polynomial in the actual Steinberg root words, with no abstraction
or change of presentation.

The conclusion applies verbatim to finite Fourier and Pauli decoders.
Fourier projections of a finite root-word packet are finite group-algebra
polynomials, and every polynomial made from them and the packet root words
still lies in the corner `(FGP2)`.  Thus neither root Fourier projections
nor recovered Pauli matrix units can directly manufacture the four binary
Leavitt arrows on the prescribed marked atom.

There is also an exact finite-packet form.  In **any** exact
finite-dimensional representation of a finite relation packet for which
the `(-1)` spectral projection `P_U` of the represented mark is nonzero,
arbitrary operators in `P_U M_d(C)P_U` obey the same bound `(FGP3)`.  In
particular the eight-dimensional marked three-qubit model of
`tagged-whitehead-two-branch-loop-has-a-three-qubit-marked-model` has
`z=-I`, so `P_U=I`, while the twelve-dimensional three-character model of
`payload-range-sum-whitehead-has-three-character-model` has `P_U!=0`.
Every finite group-algebra/Fourier/Pauli polynomial in either exact packet
still misses at least one AMR row by `1/3`.  Hence the relations of either
packet cannot imply those rows, even after arbitrary analytic polynomial
recombination inside its recovered matrix algebra.

This fences a bypass, not Atomic Morita Return itself.  A viable decoder
must use a genuinely finite-coordinate, representation-dependent choice
which is unavailable in the regular finite trace, or must first prove a
uniform marked presentation gap.  Allowing coordinate-dependent addresses
without such a gap is exactly the interface already isolated by
`atomic-three-row-compiler-is-prototype-gap-equivalent`.

No Property `(T)`, Kazhdan input, stability theorem, literature theorem,
local computation, or Lean compilation is used.

DERIVATION
fixed-group-algebra-atomic-return-firewall-proof
