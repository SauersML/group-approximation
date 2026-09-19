---
rg: 2
id: congruence-regular-padding-is-conductor-not-low-rank
kind: claim
title: Congruence-regular padding is a fixed-support conductor but not a low-rank absorber
distinct_from:
  three-way-cell-semigroups-have-conductor-but-unbounded-charge: that proves the abstract affine-semigroup conductor and moving-charge firewall; this identifies when a congruence regular representation supplies the conductor and audits its actual dimension cost.
  bs14-native-cell-padding-preserves-lattice-charge: that rules out arbitrary same-support padding on a wrong lattice coset; this observes that regular congruence padding is itself same-support lattice-zero padding and then treats the correct-lattice case.
  congruence-induction-cannot-reconstruct-a-low-rank-bs14-boundary: that computes the linear index blowup from inducing one boundary representation; this computes the larger regular-block blowup and separates algebraic absorption from flexible normalized-dimension repair.
  bs14-native-cells-cross-every-length-cutoff: that gives the rank-one even-Weil cell crossing a packet cutoff; this uses the same family to show that bounded source period does not bound the congruence-regular absorber level.
---

**ESTABLISHED; LEVEL-AGNOSTIC ABSORPTION REFUTED AT THE FLEXIBLE SCALE.**
Let `E` be a finite support of native source/first-exit/second-exit cells at
one finite congruence quotient `Q`, with incidence matrix `A_E`, semigroup
`S_E=A_E N^E`, lattice `L_E=A_E Z^E`, and saturation
`Sbar_E=A_E R_+^E intersect L_E`.

Suppose the restriction of `Reg(Q)` has a cell multiplicity vector
`u_Q in N^E` with every coordinate positive.  Then some multiple of its
margin vector is a conductor:

```text
N_E A_Eu_Q+Sbar_E subset S_E.                          (CRP1)
```

Indeed choose a conductor `c_E=A_Ez_E` from
`three-way-cell-semigroups-have-conductor-but-unbounded-charge`.  Since
`u_Q` is coordinatewise positive, choose `N_E` with
`N_Eu_Q-z_E in N^E`.  Then

```text
N_EA_Eu_Q+b
 =A_E(N_Eu_Q-z_E)+(c_E+b) in S_E
```

for every `b in Sbar_E`.  Passing to a common congruence quotient gives the
same statement for any fixed finite family of native congruence cells.

There are two load-bearing limitations.

First, regular padding cannot change lattice charge.  Its margin lies in
`L_E`, so

```text
b notin L_E  =>  b+k A_Eu_Q notin L_E                 (CRP2)
```

for every `k`.  Thus `(CRP1)` starts only after the residual polar/Gram cell
has been authenticated in the endpoint restriction lattice.  It cannot
supply that authentication.

Second, `(CRP1)` has no normalized low-rank cost.  Let `p=1 mod 4` tend to
infinity, put `Q_p=PSL_2(F_p)`, and take the full even-Weil endpoint
`pi_p`.  Its BS restriction has one trivial fixed line and an orthogonal
core `beta_p` of dimension

```text
d_p=(p-1)/2.                                            (CRP3)
```

Deleting the fixed line leaves a rank-one active boundary, so
`1/d_p->0`.  One regular block does absorb it algebraically because

```text
beta_p+res(Reg(Q_p))
 =res(pi_p+(Reg(Q_p)-1_Q)).                            (CRP4)
```

But

```text
dim Reg(Q_p)=|PSL_2(F_p)|=p(p^2-1)/2,
dim Reg(Q_p)/d_p=p(p+1).                               (CRP5)
```

Thus the first nonzero regular padding costs order `p^3` dimensions to
repair a rank-one boundary in dimension order `p`.  Any congruence quotient
compatible with the primitive order-`p` unipotent spectrum has level
divisible by `p` and regular dimension at least this order, so choosing a
different compatible level does not repair `(CRP5)`.

If “number of regular copies” is counted without their dimensions, the
example needs only one copy.  That count is irrelevant to flexible HS
stability: the metric cost is the added Hilbert-space dimension.  In the
required sense `dim(padding)=o(d)`, the level-agnostic regular-absorption
lemma is false.

Along a subsequence on which `ord_p(4)->infinity`, the same example blocks a
short-source diagonal shortcut.  Its active source has period one, while
its exact native cell couples to nonzero BS packets of that unbounded
period.  Hence deleting all long **source**
mass and bounding the short source hull by `Mr` does not bound the quotient
level or the regular-conductor constant: the exit payload still remembers
`p`.  A choice `M=M(e)` can close the source-frequency ledger but cannot, by
itself, turn regular congruence padding into `o(d)` endpoint repair.

Therefore regular blocks are useful only as a qualitative fixed-level
integralization device after zero charge and level authentication.  The
moving-level low-rank construction must recover the efficient ambient atom
(the one-line Weil completion in this test) or use the block-free Gram
surgery; it cannot replace that atom by congruence regular representations.
