---
rg: 2
id: affine-leavitt-tracial-square-function-firewall
kind: claim
title: Dimension-free tracial square functions cannot pay the affine-Leavitt boundary
distinct_from:
  atlas-radius-nine-packet-gram-sos-is-tracial: that fences a fixed A4 atlas packet Gram/SOS calculus; this fences the nested native odd-characteristic affine-Leavitt boundary, including spectral coarea and conditional expectations at arbitrary fixed depth.
  canonical-trace-forbids-literal-pi-return: that computes maximal L2 distance from an outside packet word to one literal finite packet algebra; this rules out an entire proof calculus even when the decoded subalgebras and spectral cuts are not literal word spans.
  affine-leavitt-boundary-shear-payment: that is the still-open matrix-coordinate estimate; this proves that its payment cannot come solely from dimension-free finite-tracial operations.
---

**ESTABLISHED.**  Fix the affine-Leavitt Steinberg group and mark

```text
Gamma_A=St_5(L_A(k[C_aff])),       1!=w_A=x_12(A),       (ABS1)
```

over the repository's finite splitting field of odd characteristic.  Fix a
depth `N` and finitely many group words.  Consider a proposed boundary
certificate built from the following operations:

1. evaluate fixed word `*`-polynomials and fixed matrix amplifications;
2. form finite packet Reynolds averages and trace-preserving conditional
   expectations onto the fixed-point algebras of finite packet actions;
3. form positive operator-valued Gram matrices and finite sums of squares;
4. take spectral projections or spectral coarea cuts of positive square
   functions, with the cut selected by integrating a dimension-free finite
   tracial inequality; and
5. use only inequalities valid in every finite tracial von Neumann algebra,
   including cyclicity, Cauchy--Schwarz, contractivity of conditional
   expectation, Pythagoras for orthogonal projections, and cosine--sine
   block estimates.

No such certificate can prove, for any `b<2` and finite `C`, an estimate

```text
||w_A(U)-1||_2^2
 <= b+C(def_R(U)+sep_F(U))                             (ABS2)
```

for all matrix tuples `U`.  Here `F` is any finite canonical trace window.
The conclusion remains true if the certificate uses a finite nested family
of source/target boundary square functions, chooses a different coarea cut
at every level, or first exactifies fixed finite packet groups by their
Reynolds expectations.

Indeed every operation in the listed calculus is defined, with the same
inequality and the same constants, in the finite tracial von Neumann algebra
`L(Gamma_A)`.  Substitute the left regular unitaries.  All defining relator
defects vanish.  Every nonidentity word in `F` has canonical trace zero, so
`sep_F=0`.  Since `w_A!=1`,

```text
||lambda(w_A)-1||_2^2=2.                               (ABS3)
```

Thus `(ABS2)` would give `2<=b`, a contradiction.

The same substitution also rules out hiding the contradiction in the
choice of a spectral threshold.  A coarea argument proves the existence of
a threshold from an integral identity valid in the ambient finite tracial
algebra.  Applying that identity in `L(Gamma_A)` supplies a threshold there
as well, so every subsequent dimension-free block estimate still reaches
the impossible conclusion `(ABS2)`.

Consequently the boundary payment required by
`affine-leavitt-boundary-shear-payment` must contain an operation which is
genuinely special to finite matrix coordinates and has no functorial finite
tracial analogue.  The presently isolated examples are:

- finite atomic multiplicity or normalized superrank together with a proof
  that the **same** multiplicity reservoir returns;
- a matrix polynomial-identity comparison after authenticating one common
  returned factor; or
- another finite-coordinate selector whose amplification remainder is paid
  at positive normalized density.

The established commutant-superrank gap and standard-polynomial floor are
therefore legitimate endpoints, but a tracial square function cannot by
itself supply their missing same-reservoir authentication.  In particular,
the abstract multiscale checksum inequality is usable here only after one
finite-matrix step has produced orthogonal scale domains unavailable in the
regular representation.
