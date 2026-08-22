---
rg: 2
id: first-root-parahoric-target-has-a-distinct-double-coset-type
kind: claim
title: The first root-parahoric target has a distinct double-coset type and no integral second return
distinct_from:
  first-root-parahoric-incidence-has-a-two-to-four-morita-lift: That constructs the exact rectangular edge from the source two-cycle to a parity pair of a four-cycle; this proves that no additional integral root or Weyl word can return that target pair to the source pair.
  raw-denominator-incidence-kills-off-diagonal-shell-orbit: That compares two section words already known to address the same Hecke vertex; this proves that the proposed source and target address different double-coset orbitals.
  two-path-holonomy-is-paid-by-corner-leakage: That gives a general analytic payment for nontrivial same-corner holonomy; this computes the shortest native A2 two-path holonomy and shows that it lies in the parahoric, hence is trivial on the authenticated atom.
---

# The two carriers have different orbital types

Keep the notation

```text
D=C cap hCh^(-1),       u=x_12(1),       s=s_23
```

from `first-root-parahoric-incidence-has-a-two-to-four-morita-lift`.  The
source and target ordered pairs are

```text
R_pair=(D,uD),
Q_pair=(sD,u^2sD).                                     (DCT1)
```

For an ordered pair `(aD,bD)` in `(C/D)^2`, diagonal left translation by
any word in `C` preserves its orbital invariant

```text
D a^(-1)b D.                                           (DCT2)
```

The two invariants in `(DCT1)` are

```text
type(R_pair)=D u D,
type(Q_pair)=D z D,       z=s^(-1)u^2s=x_13(plusOrMinus 2).  (DCT3)
```

They are distinct.  Reduce modulo two.  The image `Dbar` of `D` is a
subgroup (indeed the appropriate lower triangular parabolic), and

```text
zbar=1,                  ubar=x_12(1) notin Dbar.       (DCT4)
```

Therefore

```text
bar(D z D)=Dbar,
bar(D u D)=Dbar ubar Dbar,
Dbar intersect Dbar ubar Dbar=empty.                   (DCT5)
```

The same argument applies after reversing either ordered pair, since
`zbar^(-1)=1` and `ubar^(-1)=ubar`.  Consequently no single diagonal actor
word in `C` maps `Q_pair` to `R_pair`, even as an unordered pair.  This
includes every one-root or Weyl-conjugate-root candidate and every bounded
product of such integral words.  The obstruction is a finite typed-graph
obstruction, not a failure to search a sufficiently long word.

# The shortest A2 path closes with trivial parahoric holonomy

The target type does have a shortest path of length two in the `u`-edge
Hecke graph.  Put

```text
d=x_23(2) in D.                                        (DCT6)
```

The Chevalley commutator identity gives

```text
z=[u,d]=u d u^(-1)d^(-1),
u d u^(-1)=z d.                                        (DCT7)
```

Thus the two literal section paths

```text
a=u d u^(-1),             b=z                           (DCT8)
```

end at the same coset `zD` and differ by the exact correction word

```text
b^(-1)a=d in D.                                        (DCT9)
```

The path cannot have length one by `(DCT5)`, so `(DCT7)` is minimal.

Let `P` be the authenticated base projection commuting with `D`.  Then

```text
aPa^*=bPb^*,                                           (DCT10)
```

but the relative two-path holonomy on `P` is

```text
V=(bP)^*(aP)=P rho(d)P=rho(d)P.                        (DCT11)
```

It need not be the identity merely because `P` commutes with `D`.  On the
canonical regular lamp corner, `d` and the lamp translate `cd` are both
nontrivial, so

```text
tau_P(V)=0,
||P-V||_(2,P)^2=2.                                     (DCT12)
```

Thus this shortest A2 triangle does expose a maximally nontrivial
same-corner holonomy.  The positive-Gram identity in
`two-path-holonomy-is-paid-by-corner-leakage` says that any global unitary
whose compression is close to the average of the two path transports must
pay at least `1/2` normalized source leakage.

The section identity alone does not supply that compression-to-average
equation: it equates the endpoint projections in `(DCT10)`, while retaining
the internal factor `rho(d)` in `(DCT11)`.  An ordinary group word selects
one path rather than their linear average.  Consequently `(DCT12)` is a
concrete holonomy charger waiting for one same-corner Gram/authentication
identity, not by itself a contradiction.

The native section row does not secretly contain that identity.
`native-a2-two-path-average-is-not-an-ordinary-word-compression` proves by
group-basis support that no ordinary group word has compression
`(A+B)/2`: a word compression occupies one lamp double coset, whereas this
average occupies the two distinct cosets `<c>` and `d<c>`.  The missing
cross term must therefore be genuinely wordized by an additional
noncentral selector/corner gadget.

The alternative second-denominator search is also now exact.
`shortest-second-denominator-return-has-coweight-holonomy` finds the two
shortest returns among the six Weyl-conjugate denominators.  Their relative
word is `diag(2,2,1/4)`: it closes the root type but shifts the actual carrier
by an amenable coweight translation, so the finite-torus Folner cuts absorb
its ordinary product-word energy.

The conclusion is exact.  A second return made only of integral root/Weyl
words cannot identify the rectangular target with the source, and the
shortest commutator multipath authenticates the target within its own type
and leaves the explicit holonomy `x_23(2)`.  The next possible incidence
must either authenticate the average of these two target paths on a full
corner, or use a second denominator edge which changes the double-coset type
and returns to the identical source atom.  More diagonal relations internal
to `C` cannot perform the latter.
