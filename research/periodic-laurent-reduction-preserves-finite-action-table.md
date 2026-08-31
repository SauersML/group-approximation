---
rg: 2
id: periodic-laurent-reduction-preserves-finite-action-table
kind: proof
title: Periodize every finite Laurent covariance table without wraparound
target: untwisted-bilateral-symbol-enrichment-is-lef
requires: []
---

Write basis vectors of `V` as `e_(i,k)`, with
`1<=i<=n` and `k in Z`. If `q in Q`, both `q` and `q^(-1)`
are Laurent matrices. Hence there is a finite number `b(q)` such
that their matrices only connect levels whose indices differ by at
most `b(q)`. If `l-1` has finite matrix support, then

```text
q(l-1)q^(-1)
```

also has finite support. Thus the displayed action `alpha` is
well-defined.

Let `F` be a finite subset of `H_bi). Enlarge the finite data only
for the proof so that it contains all factors, inverses, products and
conjugates which occur in multiplication statements

```text
g h = k,                     g,h,k in F.                (UBL3)
```

Write each selected element uniquely as `(l,q)`. There is a finite
interval `I subset Z` containing every row and column level appearing
in every selected matrix `l-1), its selected inverse, and every
finitary matrix produced in the calculations in `(UBL3)`. There is
also a common propagation bound `b` for the finitely many selected
Laurent matrices and their inverses.

Choose `N` larger than:

* the diameter of the interval obtained from `I` by adding all
  shifts between `-2b` and `2b`;
* every exponent diameter appearing in a nonzero Laurent entry of
  `q-q'` for distinct selected symbols `q,q'`; and
* twice every fixed finite safety margin used in the selected
  products.

Let

```text
A_N=A/(z^N-1),              V_N=A_N^n.
```

The quotient map gives a homomorphism

```text
rho_N:Q -> Q_N=EL_n(A_N).                               (UBL4)
```

The group `Q_N` is finite. The choice of `N` also makes
`rho_N` injective on the finite selected subset of `Q): a nonzero
Laurent polynomial whose exponent diameter is less than `N` cannot
vanish modulo `z^N-1`.

For a selected finitary matrix `l=1+a`, fold every level in the
support of `a` modulo `N), obtaining a matrix

```text
bar(l)=1+bar(a) in End_(F_2)(V_N).                      (UBL5)
```

No two inspected levels collide. Because the inverse `l^(-1)=1+b`
and its product calculation were included in the finite data, folding
the equality

```text
(1+a)(1+b)=1=(1+b)(1+a)
```

introduces no spurious intermediate index. Therefore `bar(l)` is
invertible. The same no-collision observation gives, for every
selected product and covariance row,

```text
bar(l_1 l_2)=bar(l_1)bar(l_2),
bar(q l q^(-1))
 =rho_N(q) bar(l) rho_N(q)^(-1).                        (UBL6)
```

The second identity can also be read coefficientwise: Laurent
multiplication only shifts the finite support by at most `b), and
the safety interval was chosen before reduction.

Now use the finite group

```text
P_N=GL_(F_2)(V_N) semidirect Q_N,                       (UBL7)
```

where `Q_N` acts on `GL_(F_2)(V_N)` by conjugation through its
natural linear action. Define on the selected table

```text
Phi_N(l,q)=(bar(l),rho_N(q)).                           (UBL8)
```

Equations `(UBL4)` and `(UBL6)` show that every multiplication
statement `(UBL3)` is preserved exactly.

The map is injective on `F`. If two selected elements have different
`Q` coordinates, their images have different second coordinates by
the choice of `N`. If their `Q` coordinates agree, their distinct
finitary matrices remain distinct because folding is injective on the
union of their supports. Thus `Phi_N` is a local embedding of `F`
into the finite group `P_N`.

Since `F` was arbitrary, `H_bi` is LEF. A specified nonidentity
finitary transvection remains nonidentity whenever its two matrix
coordinates are included in the safety interval. The conclusion
therefore gives marked finite local models, not merely unmarked local
multiplicativity.
