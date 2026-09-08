---
rg: 2
id: rational-heisenberg-fd-radical-is-commutator-and-mf
kind: claim
title: The rational Heisenberg group is torsion-free and MF while every exact finite-dimensional representation of it is abelian
distinct_from:
  bare-self-copy-mf-calibration: that torsion-free finitely presented MF group has a single finite-dimensionally invisible mark, and its finite-dimensional theory is otherwise rich because BS(1,2) is residually finite; this group's finite-dimensional radical is the whole commutator subgroup, which is the shape a full-MF-radical cover produces, and that total collapse is what the calibration needs to match.
  abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center: that is finitely presented, its invisible mark is central of order p, and its positive conclusion is soficity in normalized Hilbert-Schmidt norm; this group is torsion-free, its invisible subgroup is the whole commutator subgroup and torsion-free, and its positive conclusion is operator MF.
  exact-fd-invisibility-has-no-general-hs-robustification: that refutes a uniform quantitative robustification of exact invisibility, using a finitely presented sofic group with a central involution; this refutes the qualitative inference from total exact collapse to non-MF, and needs the collapse to be total rather than at one mark.
  two-tier-matricial-invisibility: that constructs one finitely presented non-MF group displaying three levels of invisibility at once and computes its MF radical; this is a single MF group whose finite-dimensional radical is maximal subject to a free abelian quotient, and it makes no non-MF assertion at all.
artifacts:
  - research/artifacts/torsion-free-cover-fd-radical-and-heisenberg-2026-09-08.md
---

**ESTABLISHED.**  Let `H = UT_3(Q)` be the group of upper unitriangular
three-by-three matrices over the rationals, written on `Q^3` as

```text
(a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab').                            (RH1)
```

Put `x(a) = (a,0,0)`, `y(b) = (0,b,0)`, `z(c) = (0,0,c)`, and `Z = z(Q)`.
Then

```text
H is torsion-free,
[H,H] = Z = Z(H),        H/Z = Q^2,
Rad_fd(H) = [H,H] != 1,                                                (RH2)
H is operator MF.                                                      (RH3)
```

In particular every exact finite-dimensional unitary representation of `H` has
abelian image, and `H` is nevertheless MF: `Rad_MF(H) = 1` while
`Rad_fd(H) != 1`.

**What this refutes.**  The inference

```text
K torsion-free countable and Rad_fd(K) = [K,K] != 1   ==>   K is not MF
```

is false, and `H` is a counterexample.  This matters because
`free-abelianized-cover-fd-radical-is-commutator` delivers exactly the
hypothesis of that inference for the canonical torsion-free cover of a group
with full MF radical.  Reading that computation as a proof that the cover is
non-MF -- and hence as a closure of `torsion-free-countable-non-mf` with no
Property (T) input -- is therefore invalid.  The open implication a
torsion-free transfer needs remains `free-abelianized-cover-reflects-mf`.

`H` is not a counterexample to that implication and is not claimed to arise as
a cover of a group with full MF radical; it refutes the intermediate inference
only.

**Why the collapse is compatible with MF.**  The exact argument for `(RH2)`
takes determinants on a block of dimension `m` and evaluates the central
character at `c/m`, an element of `Q` that moves with the representation
dimension.  Pointwise asymptotic multiplicativity constrains no such moving
element, so an MF model is under no obligation to reproduce the identity.  The
same wall is what `fd-mark-stability-forces-mf-invisibility` isolates: passing
from `Rad_fd` to `Rad_MF` needs point-norm stability at the mark, and total
exact collapse supplies none.

**On the positive side, `(RH3)` is a citation, not a new analytic result.**
Every finitely generated subgroup of `H` has all coordinates in some
`Z[1/N]`, and `UT_3(Z[1/N])` is residually finite, so `H` is locally
residually finite, hence LEF, hence operator MF by `lef-implies-operator-mf`.
The route through amenability is deliberately not used:
`permutation-norm-models-certify-exactly-lef` records that no amenable group
outside the LEF class is certified MF in this archive.
