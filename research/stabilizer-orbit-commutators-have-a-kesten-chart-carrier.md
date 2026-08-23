---
rg: 2
id: stabilizer-orbit-commutators-have-a-kesten-chart-carrier
kind: claim
title: The full stabilizer orbit of nonedge commutators has a Kesten chart carrier
distinct_from:
  nonedge-spectrum-cannot-descend-to-forty-two-chart: that proves every spectral cut of one commutator pays a fixed stabilizer defect; this passes to the full finite stabilizer orbit and constructs a nontrivial invariant spectral projection of exactly the chart-atom trace.
  no-native-arithmetic-relator-breaks-the-bernoulli-quotient: that isolates the first anti-relation but supplies no invariant projection; this uses all its stabilizer conjugates and free-product normal form to obtain one functorial nonlinear carrier.
  one-phase-chart-tag-pays-atomwise-leakage: that bounds EDA11 after a complete orthogonal chart PVM and its injective phase tag are available; this constructs one correctly stabilized candidate atom but leaves the mutual orthogonality of its forty-two chart translates as one explicit Gram scalar.
  fixed-commuting-lamps-have-robust-fourier-atoms: that obtains finite Boolean atoms from a commuting packet; this obtains a diffuse Kesten spectral carrier from a free packet of nonedge commutators.
---

ESTABLISHED. Retain

```text
C=SL_3(Z),       h=diag(2,1,1/2),
D=C cap h C h^(-1),       x=hC,       y=h^(-1)C.        (KCC1)
```

Let

```text
O=D.y,                 m=|O|.                           (KCC2)
```

Then `O` is finite because the relevant arithmetic lattices are
commensurable, and `m>=2` because `x_21(1) in D` moves `y`. Every `z in O`
is nonadjacent to `x`, since the native Hecke graph is actor invariant and
`x,y` are nonadjacent. Put

```text
kappa_z=[c_x,c_z]=(c_x c_z)^2.                          (KCC3)
```

The family `(kappa_z)_(z in O)` freely generates a free group `F_m` inside
the native graph-product lamp group. Consequently

```text
K=W^*(kappa_z:z in O) isomorphic to L(F_m).              (KCC4)
```

The stabilizer `D` permutes the free generators. Hence the Kesten operator

```text
S=sum_(z in O)(kappa_z+kappa_z^(-1))                    (KCC5)
```

is exactly `D`-invariant. Its canonical spectral measure is the continuous,
atomless Kesten measure of the `2m`-regular tree. There is therefore a real
number `r` for which

```text
E=1_(-infinity,r](S),        tau(E)=1/42,       dEd^(-1)=E
                                                    for every d in D. (KCC6)
```

Thus the single-word stabilizer firewall is sharp: full-orbit nonlinear
spectral calculus does produce a functorial positive base carrier of exactly
the required chart-atom mass.

Choose representatives `g_i` for `C/D` and put

```text
E_i=g_i E g_i^(-1),              i in C/D.              (KCC7)
```

These are well defined, have trace `1/42`, and obey exact `C`-covariance.
Their total trace is one. Hence they form the desired complete chart PVM if
and only if the single mixed Gram scalar

```text
G_K=sum_(i!=j) tau(E_iE_j)
   =||sum_i E_i-I||_2^2                                  (KCC8)
```

vanishes. Equation `(KCC8)` is exact because the `E_i` are projections and
`sum_i tau(E_i)=1`. This reduces the surviving nonlinear extraction from
construction of `42` atoms to one explicit raw-group-algebra overlap
calculation.

The construction excludes the exact Bernoulli quotient at the level of its
formula: there every `kappa_z=1`, so `S=2mI`, whereas the Kesten quantile
`r` lies strictly below `2m` and the same spectral cut is zero. It also
defeats the previous independent-label objection at the carrier stage,
because `E` is a functorial spectral function of the raw nonedge packet, not
an added tensor factor.

No orthogonality is claimed. Stabilizer invariance alone does not control
`(KCC8)`, and averaging the `E_i` cannot create it. The exact next target is
to calculate or bound the pair intersections of the conjugate free
subfactors `g_i K g_i^(-1)`. If their centered parts are pairwise
trace-orthogonal, then `(KCC8)=41/42`, reproducing the independent-refinement
floor and closing this route negatively. If the arithmetic orbital
intersections instead force `(KCC8)=0` (or make it payable by section/root
defect), `(KCC7)` supplies the missing chart PVM and can be fed directly to
the existing EDA11 phase-tag ledger.
