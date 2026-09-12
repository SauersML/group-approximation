---
rg: 2
id: agent-fournier-not-torsion-partial-conjugacy-detector-no-go
kind: claim
title: The full torsion detector cannot erase a nontrivial partial conjugacy
artifacts:
  - research/agent-fournier-not-torsion-partial-conjugacy-proof.md
distinct_from:
  agent-leavitt-not-torsion-corner-noce-forces-mf-radical: that theorem turns a no-CE algebra in the full nontrivial torsion corner into MF-radical membership; this proves that the same full corner cannot identify two genuinely distinct literal group marginals by making the torsion conjugator scalar.
  agent-groupfactor-bcs-reynolds-free-holonomy-trichotomy: that computes free, finite-action, and HNN Reynolds carriers and leaves finite-order partial conjugacy open; this closes the literal-single-group-element version of that remaining case.
  unitary-corner-compressions-force-reduction: that says a compressed group unitary must stabilize the corner; this specializes the stabilizer for the complete nontrivial cyclic spectral projection and computes the partial-conjugacy equality exactly.
---

**ESTABLISHED NO-GO.**  Let `G` be a group and let `z in G` have exact
finite order `m>=2`.  Put

```text
e_z=(1/m) sum_(j=0)^(m-1) z^j,
q_z=1-e_z in C[G].                                      (TPC1)
```

Let `g in G` and `a in Z`.  Suppose that

```text
U=q_z g q_z
```

is a unitary in the corner `q_z C[G] q_z`.  If the torsion conjugacy is
invisible on that corner,

```text
q_z (z^a g z^(-a)) q_z = q_z g q_z,                    (TPC2)
```

then it was already trivial in the group:

```text
z^a g z^(-a)=g.                                        (TPC3)
```

Consequently the full torsion projection used by
`agent-leavitt-not-torsion-corner-noce-forces-mf-radical` cannot turn
covariance between two distinct literal group marginals into equality.  A
finite-order partial-conjugacy BCS compiler with corner unit `q_z` therefore
cannot glue shared variables if each marginal has the form `q_z g q_z`.

## Proof

Corner unitarity gives `g q_z g^(-1)=q_z` by the unitary-compression lemma.
The support of `q_z` is exactly the cyclic subgroup `H=<z>`: its coefficient
at `1` is `(m-1)/m` and its coefficient at every other element of `H` is
`-1/m`, all nonzero.  Equality of group-ring supports therefore gives

```text
g H g^(-1)=H.
```

Thus for a unique `r in (Z/mZ)^times`,

```text
g z g^(-1)=z^r.                                        (TPC4)
```

The projection `q_z` is invariant under every automorphism of `H`, so it
commutes with `g`.  Using `(TPC4)`, equation `(TPC2)` becomes

```text
q_z z^(a(1-r)) g = q_z g,
```

and hence

```text
q_z (z^(a(1-r))-1)=0.                                  (TPC5)
```

Evaluate `(TPC5)` in the faithful character `chi(z)=exp(2 pi i/m)`, which
is one of the nontrivial character summands selected by `q_z`.  It gives

```text
exp(2 pi i a(1-r)/m)=1,
```

so `a(1-r)=0 mod m`.  Therefore

```text
z^a g z^(-a)=z^(a(1-r))g=g,
```

which proves `(TPC3)`.

## Why a primitive Reynolds character does not repair this

For a nontrivial character `chi` of `H`, the primitive projection

```text
p_chi=(1/m) sum_j conjugate(chi(z^j)) z^j              (TPC6)
```

does make `z` scalar.  Hence

```text
p_chi (z^a g z^(-a)) p_chi=p_chi g p_chi              (TPC7)
```

whenever the two compressions are defined on that reducing block.  This is
the tempting partial-conjugacy compiler.  But `p_chi` is not a universal
detector for `z`: a representation may send `z` to a different nontrivial
`m`-th root of unity, so that `z!=1` while the image of `p_chi` is zero.
Thus a no-CE algebra with unit `p_chi` does not imply `z in Rad_MF(G)`.

More generally, for a character subset `S` and
`p_S=sum_(chi in S) p_chi`, the implication

```text
theta(z)!=1  ==> theta(p_S)!=0                         (TPC8)
```

for every representation of `H` holds exactly when `S` contains every
nontrivial character, i.e. `p_S=q_z`.  The only spectral corner that
authenticates every possible surviving torsion sector is therefore precisely
the corner on which `(TPC2)` is faithful to the original group equality.

## Exact boundary

This rules out only **literal** compressed marginals `q_z g q_z`.  It does
not rule out a genuinely nonnormal signed-Hecke operator with two or more
double-coset terms.  Piecewise terms can be corner unitaries by cancellation
without any individual group element stabilizing `q_z`; that is exactly the
remaining escape in `TRUE_AUGMENTATION_ZERO_HECKE_GATE.md`.  Nor does the
argument rule out installing a copy of the no-CE algebra independently in
every primitive nontrivial character block and taking their direct sum.  But
that stronger construction is already a unital map into the full corner
`q_z C[G]q_z`; the partial-conjugacy scalarization itself supplies no
cross-block compatibility.

The finite-order alternative left open by the Reynolds trichotomy therefore
has a sharp dichotomy:

```text
primitive character corner: conjugacy can disappear, but the torsion mark
                            is not authenticated;
full nontrivial corner:     the torsion mark is authenticated, but equality
                            of literal marginals reflects group equality.
```

