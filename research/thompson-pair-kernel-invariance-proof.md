---
rg: 2
id: thompson-pair-kernel-invariance-proof
kind: route
title: Involution dichotomy, finite class set, and absence of finite quotients
target: thompson-pair-kernel-invariance-kills-even-lamps
requires: []
---

## Direct proof

**Step 1 (dichotomy).**  Let `W` be a unitary with `W^2=I`.  Its spectrum lies
in `{+1,-1}`, so `W=I` or `-1` is an eigenvalue and `||W-I||_op=2`.  More
generally, for an exact unitary of order dividing `p` the nonidentity values
are at least

```text
gap_p = min{ |zeta-1| : zeta^p=1, zeta != 1 }
```

from `I`; for `p=2` this is `gap_2=2`.  Since `rho` is a homomorphism of an
elementary abelian `2`-group, every `rho(m)` is such a `W`, so hypothesis
`(PKI1)` upgrades to the exact implication

```text
rho(b_(x,y))=I  =>  rho(b_(s x,s y))=I.                       (P1)
```

**Step 2 (equivalence relation, finitely many classes).**  Reflexivity and
symmetry are immediate.  For transitivity use

```text
b_(x,z)=b_(x,y)+b_(y,z)
```

in `I_X` and multiplicativity of `rho`.  The image `rho(I_X)` is an abelian
group of exponent two in `U(d)`; commuting involutions are simultaneously
diagonalizable, so after one change of basis `rho(I_X) <= {+1,-1}^d` and
`|rho(I_X)| <= 2^d`.  Fixing `x_0`, the map `[x] |-> rho(b_(x,x_0))` is
injective on classes, so

```text
|X/~| <= 2^d < infinity.                                      (P2)
```

**Step 3 (finite action).**  By `(P1)` each `s in S` sends `~`-classes into
`~`-classes; applying the same to `s^(-1) in S` shows the induced map is a
bijection of `X/~`.  Since `S` generates `A`, this defines an action of `A`
on the finite set `X/~`, i.e. a homomorphism into a finite symmetric group.
`A` has no nontrivial finite quotient, so the action is trivial.

**Step 4 (transitivity).**  Fix `x_0`.  For `x in X` choose `g in A` with
`g x_0=x`.  Triviality of the induced action gives

```text
[x]=[g x_0]=g[x_0]=[x_0],
```

so `~` has one class and `rho(b_(x,y))=I` for all `x,y`.  Pair lamps generate
`I_X`: any `m` with `supp(m)={x_1,...,x_(2k)}` is
`b_(x_1,x_2)+...+b_(x_(2k-1),x_(2k))`.  Hence `rho=1`.

For Thompson `V` the hypotheses hold: the action on the countable Cantor
orbit is transitive (indeed highly transitive) and `V` is infinite simple, so
its only finite quotient is trivial.  Simplicity is used only through the
absence of nontrivial finite quotients, so the lemma applies verbatim to any
transitive actor with that property.
