# Relation (2.10) forces the long-root Weyl quarter-turn

Use Kassel notation

```text
a=x_alpha, b=x_beta, c=x_(alpha+beta), d=x_(2alpha+beta),
B=x_(-beta),                 w=b B^(-1) b.
```

Assume the commuting-root relations (2.1)--(2.3), together with (2.4),
(2.5), and (2.10). The required commutations are

```text
[b,c]=[b,d]=[c,d]=[a,B]=[d,B]=[a,d]=1.
```

The noncommuting relations are

```text
[a,b]=cd,       [a,c]=d^2,       [c,B]=a d^(-1).       (R)
```

Put `h=a d^(-1)`. The last relation gives

```text
B c B^(-1)=h^(-1)c=d a^(-1)c.
```

Since conjugation by `B` fixes `a,d`, inversion of this triangular
automorphism gives

```text
B^(-1)cB=d^(-1)ac,
B^(-1)c^(-1)B=c^(-1)a^(-1)d.                           (1)
```

Also the first two relations in `(R)` give

```text
bab^(-1)=d^(-1)c^(-1)a,
c^(-1)ac=d^2a.                                         (2)
```

Now collect the two conjugations by `w`:

```text
waw^(-1)
 = b B^(-1)(bab^(-1))B b^(-1)
 = b B^(-1)(d^(-1)c^(-1)a)B b^(-1)
 = b c^(-1)b^(-1)
 = c^(-1),
```

where `(1)` and the commuting relations are used in the third equality.
Similarly,

```text
wcw^(-1)
 = b B^(-1)cB b^(-1)
 = b(d^(-1)ac)b^(-1)
 = d^(-2)c^(-1)ac
 = a,
```

using `(1)` and `(2)`. Finally `w` commutes with `d` because both `b` and
`B` do. Thus

```text
waw^(-1)=c^(-1),       wcw^(-1)=a,       wdw^(-1)=d.  (Q)
```

Applying `(Q)` four times proves

```text
[w^4,a]=[w^4,c]=[w^4,d]=1.                             (Z)
```

This recovers exactly the relevant three formulas in Kassel Lemma 2.3 and
locates their minimal mixed input: (2.10) supplies the missing conjugation of
`c` by the negative long root.

Because the derivation uses a fixed number of multiplications, every equality
has an immediate dimension-free normalized-HS perturbation form: the three
commutator defects in `(Z)` are bounded by a universal constant times the sum
of the defects of the displayed commuting relations and (2.4), (2.5),
(2.10). No determinant or dimension enters.

## What remains

The partial presentation does not force `w^4` to commute with `b` or `B` by
this argument. Indeed, after quotienting by the normal closure of `a,c,d`,
the displayed relations leave the two opposite long-root directions largely
free. Hence `(Z)` is a genuine representation-independent centralization
step, but not yet full scalar centrality. The later mixed relations must close
the rank-one `b,B` orbit or connect it to the centralized three-root set.

