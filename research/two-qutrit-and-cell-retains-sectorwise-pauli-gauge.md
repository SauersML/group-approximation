---
rg: 2
id: two-qutrit-and-cell-retains-sectorwise-pauli-gauge
kind: claim
title: The two-qutrit AND cell still retains an exact sectorwise Pauli gauge
artifacts:
  - research/two-qutrit-and-sectorwise-gauge-countermodel-proof.md
distinct_from:
  controlled-pauli-commutator-is-and-times-multiplicity-commutator: that computes the abstract AND phase and its external commutator; this realizes both selector cuts and their conjunction inside the concrete two-qutrit multipath packet and tests the shared D8 label there.
  leavitt-crossed-gram-pauli-charge-has-sectorwise-escape: that gives an abstract four-sector Clifford absorber; this proves the absorber survives when the four sectors come from one explicit finite-type/multipath incidence cell.
  two-qutrit-controlled-bases-give-proper-multipath-marginal: that constructs the proper multipath projection; this uses it as one input of a controlled AND and identifies exactly what it does not authenticate.
---

Use the nine atoms `p_(a,b)` and the multipath projection `P` from
`two-qutrit-controlled-bases-give-proper-multipath-marginal`. Inside its
marked corner `q`, define

```text
S=sum_(b in F_3) p_(0,b),
T=sum_(a in F_3) p_(a,0)=P.                             (TAG1)
```

Then `S,T` are commuting proper projections and

```text
ST=p_(0,0).                                              (TAG2)
```

Here `S` is itself the marked character projection of
`<J,Z_1>`, `T` is the proper noncentral three-path marginal, and their
conjunction is one marked finite-type atom. Thus the two selector cuts and
their Boolean AND all have exact finite-type/multipath formulas in one
packet.

All four joint sectors are nonzero. With

```text
E_st=S^s(1-S)^(1-s) T^t(1-T)^(1-t),
```

their ranks in the nine-dimensional marked block are

```text
rank(E_00)=4,       rank(E_10)=2,
rank(E_01)=2,       rank(E_11)=1.                       (TAG3)
```

Now tensor with one shared D8 label pair `X_l,Z_l` and one external gauge
pair `X_g,Z_g`, each having central commutator `-1`. Define exact
involutions

```text
U=sum_(s,t) E_st tensor X_l^s tensor X_g^(st),
V=sum_(s,t) E_st tensor Z_l^t tensor Z_g^(st).          (TAG4)
```

They use the same D8 label on every selector sector and implement the
correct controlled label actions. Nevertheless,

```text
[U,V]=1.                                                (TAG5)
```

On `E_11`, the label commutator and gauge commutator are both `-1` and
cancel. On the other three sectors at least one exponent is zero. The
multiplicity commutator on the active AND sector is still

```text
[X_g,Z_g]=-1,                                           (TAG6)
```

and that sector has positive rank.

Consequently the two-qutrit multipath packet supplies an exact local
controlled-AND/marginal gadget, but merely sharing the D8/Pauli subgroup
does not prove the HS shared-gauge lock
`zpc-controlled-pauli-and-hs-shared-gauge-lock`. Any successful extension
must add a mixed occurrence which identifies the active actors with
identity-label actors on the same multiplicity reservoir. Selector
incidence, the conjunction projection, and one common label group leave the
sectorwise Clifford escape intact.

The scope is local and exact. Additional relations authenticating `U,V`
as one irreducible whole-packet occurrence could exclude `(TAG4)`, but
that is precisely the missing same-reservoir input; it is not a consequence
of the displayed finite-type/multipath cuts or the shared D8 subgroup.
