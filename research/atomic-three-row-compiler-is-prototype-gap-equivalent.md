---
rg: 2
id: atomic-three-row-compiler-is-prototype-gap-equivalent
kind: claim
title: A prescribed-atom three-row compiler is exactly a finite prototype gap
invalidates:
  - binary-leavitt-atomic-return-via-three-row-compiler
distinct_from:
  bounded-prototype-rows-imply-atomic-morita-return: that proves a prototype-controlled three-row construction collapses the marked atom; this proves the construction hypothesis itself is quantitatively equivalent to a direct lower bound on one prototype discrepancy whenever that atom survives.
  affine-leavitt-decoder-interface-is-mark-collapse-equivalent: that audits an existential normalized-Hilbert--Schmidt carrier which can be chosen zero; this concerns a prescribed nonzero operator-norm spectral atom and uses the zero coefficient tuple only after a prototype gap is already known.
artifacts:
  - research/atomic-three-row-prototype-gap-equivalence-proof.md
---

**ESTABLISHED INTERFACE EQUIVALENCE.**  Let `p_U` be a projection selected
from a finite-dimensional unitary tuple `U`, and let

```text
epsilon(U)=max_(1<=j<=N) ||q_j(U)-1||_op
```

for a fixed finite list of discrepancy words.  Restrict attention to the
tuples for which `p_U!=0`.  The following assertions are quantitatively
equivalent.

1. There is a constant `C` such that every such tuple admits
   `s_0,s_1,t_0,t_1 in p_U M_d(C) p_U` satisfying

   ```text
   ||t_0s_0-p_U||_op <= C epsilon(U),
   ||t_1s_1-p_U||_op <= C epsilon(U),
   ||s_0t_0+s_1t_1-p_U||_op <= C epsilon(U).           (ATG1)
   ```

2. There is a constant `gamma>0` such that

   ```text
   epsilon(U)>=gamma                                  (ATG2)
   ```

   for every tuple with `p_U!=0`.

More precisely, `(ATG1)` with `C` gives `(ATG2)` with
`gamma=1/(3C)`.  Conversely, `(ATG2)` with `gamma` gives `(ATG1)` with
`C=1/gamma` by taking all four coefficient operators equal to zero.

For a finite presentation `Gamma=<S|R>`, suppose every `q_j` belongs to the
normal closure of `R`.  Choose fixed fillings and let `A` be the largest
resulting relator-area constant.  Then

```text
epsilon(U)<=A Def_R(U).                                (ATG3)
```

Consequently either form above implies the direct marked-sector gap

```text
p_U!=0  ==>  Def_R(U)>=gamma/A.                        (ATG4)
```

Conversely, a direct gap `(ATG4)` gives `(ATG2)` by taking the prototypes to
be the defining relators themselves.  Thus allowing a coordinate-dependent
address, a coordinate-dependent coefficient window, and arbitrary selected
corner operators does not weaken the logical burden of the compiler: after
the atom has been prescribed, the compiler exists exactly when a fixed
finite discrepancy menu already has a uniform gap on every surviving
marked coordinate.

Applied to `binary-leavitt-three-row-atomic-compiler`, this isolates the
missing input.  The open task is not merely to choose the returned four
operators.  It is to prove a uniform positive lower bound for at least one
fixed prototype discrepancy on every matrix tuple whose prescribed
`x_13(s_1t_1)` atom is nonzero.  The moving selection rule supplies no
additional compactness beyond that gap.

For an involutive mark `w` which normally generates the finitely presented
group, `(ATG4)` is also equivalent to total norm-corona MF-radical collapse.
If `(ATG4)` failed, a sequence with presentation defect tending to zero and
nonzero rounded `w`-atom would diagonalize to a norm-matrix-corona
homomorphism retaining `w`.  Conversely, a corona homomorphism retaining
`w` has unitary generator lifts whose relator defects tend to zero; the
order-two spectral gap and rounding produce nonzero `w`-atoms arbitrarily
far out, contradicting `(ATG4)`.  Killing the normally generating mark kills
the whole image.  Hence the corrected binary-Leavitt compiler is not a
strictly smaller intermediate statement: quantitatively, it is the desired
full-radical conclusion expressed through a finite discrepancy menu.
