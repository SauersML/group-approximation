# Exact support erasure with linear commutator leakage

2026-09-08. Elementary finite-dimensional proof. A supplied projection
can be made reducing at cost linear in its generator commutators.
Replacing that positive-central block by trivial representations then
controls the surviving residual by its original compression plus a
linear leakage term. The block replacement itself still pays a
square-root-rank movement cost. No projection selection, executable
verification, or endpoint construction is assumed or performed.

## 1. Conventions and the actual improvement

An exact modular vertex pair has four unitary generators
`U=(S_1,B_1,S_2,B_2)`, with

```text
S_i^2=B_i^3=Z,       Z^2=I.
```

Here the two vertices have one common central involution. Let `P`
be a supplied orthogonal projection with `ZP=P`, and put `Q=I-P`.
Use normalized matrix HS norms on the whole original dimension `n`,
and maximum norms for tuples. Define

```text
alpha=rank(P)/n,
kappa_2=max_g ||[U_g,P]||_2,
kappa_inf=max_g ||[U_g,P]||_op.                        (SE1)
```

The earlier route
`round-finite-subgroup-corners-and-apply-block-capture` already
rounds a positive torsion corner at linear HS leakage cost, then
uses a separate bounded-payload hypothesis for capture. We do not
claim that rounding ingredient as new. The conclusion developed
here is the direct erasure estimate

```text
||R(U_hat)-Q R(U) Q||_2 <= 4L kappa_2,                 (SE2)
```

for a difference `R` of words of total length at most `L`, with
an exact vertex pair `U_hat`, a trivial `P`-block, and the entire
negative central sector preserved. This keeps the smaller retained
residual `Q R(U)Q`, rather than replacing it by the original full
defect. It yields a precise conditional contraction without a
bounded-payload authentication or a supplied compatible endpoint.

## 2. Finite-order rounding on both sides of a fixed projection

First let `U` be any finite-dimensional unitary with `U^m=I`,
where `m>=2`, and let `P` be any orthogonal projection. Set

```text
A=PUP+QUQ,       O=U-A,       Q=I-P.
```

The diagonal and off-diagonal block spaces are orthogonal for the
HS inner product. The off-diagonal blocks of `O` equal those of
`[U,P]` up to one sign, which is implemented by a diagonal unitary.
Consequently

```text
||O||_2=||[U,P]||_2=:kappa,
||O||_op=||[U,P]||_op=:beta<=1.                       (SE3)
```

Unitarity of `U` also gives, block by block,

```text
I-A*A=O*O,
tr_n(I-A*A)=kappa^2,
||I-A*A||_op=beta^2.                                  (SE4)
```

In particular `A` is a contraction. Complete its polar partial
isometry separately in the two square diagonal blocks to a unitary
`W` commuting with `P`. Kernel and cokernel dimensions in each
block are equal, so such completions exist even when a compression
is singular. Writing `A=W|A|`, the scalar inequalities for
`0<=s<=1` show

```text
||W-A||_2^2=tr_n(I-|A|)^2
          <=tr_n(I-A*A)=kappa^2,
||W-A||_op=1-sqrt(1-beta^2) <= beta.                  (SE5)
```

Since `W-A` is block diagonal and `U-A` is off diagonal,

```text
||W-U||_2^2=||W-A||_2^2+||U-A||_2^2 <= 2kappa^2,
||W-U||_op <= 2beta.                                  (SE6)
```

Round every eigenvalue of `W` to a nearest `m`-th root of unity,
using one fixed choice at ties, and call the resulting unitary
`V`. Functional calculus gives `V^m=I` and `[V,P]=0`.
For `z=lambda exp(it)`, where `lambda` is the selected root and
`|t|<=pi/m`, the elementary bounds

```text
|z-lambda|<=|t|,
|z^m-1|=2sin(m|t|/2)>=2m|t|/pi
```

give `|z-lambda|<=pi|z^m-1|/(2m)`. Spectral calculus and unitary
telescoping therefore give, in either norm `p=2,infinity`,

```text
||V-W||_p <= (pi/(2m))||W^m-I||_p
          <= (pi/2)||W-U||_p.                         (SE7)
```

Combining `(SE6)` and `(SE7)` proves simultaneous bounds for the
same rounding:

```text
||V-U||_2 <= sqrt(2)(1+pi/2) kappa < 4kappa,
||V-U||_op <= (2+pi) beta < 6beta.                    (SE8)
```

No fixed generator multiplicities are asserted. No relative rank
lower bound on either block is needed: all HS estimates use the
whole-space trace.

There is also a rank-local choice of the same construction. Let

```text
W_U=Ran(P)+U Ran(P)+...+U^(m-1)Ran(P).
```

This is a reducing subspace for `U`, contains `Ran(P)`, and has
dimension at most `m rank(P)`. It reduces the pinched matrix `A`
as well. On `W_U^perp`, the pinching is simply the original unitary
`U`; choose the polar completion to be `U` there. Root rounding
fixes its exact root eigenvalues. Thus `V-U` is supported on
`W_U`, and

```text
rank(V-U)<=m rank(P).                                (SE9)
```

These choices preserve every estimate above.

## 3. Simultaneous modular rounding with the center kept exact

Let `E_+=(I+Z)/2` and `E_-=I-E_+`. The condition `ZP=P`
implies `P<=E_+`. Each original generator preserves the two
central sectors. Within `E_+`, apply Section 2 to `S_i` with
`m=2` and to `B_i` with `m=3`, using the same supplied `P`.
The constructions for the four generators may be independent.
Keep their original restrictions to `E_-` exactly unchanged.

Call the resulting generators `V_g`. Each commutes with `P`,
and their powers agree exactly:

```text
V_(s_i)^2=V_(b_i)^3=E_+-E_-=Z.                       (SE10)
```

They therefore form an exact modular vertex pair. The estimates
of Section 2 remain valid with whole-space normalization, since
the changes and commutators vanish in the negative sector:

```text
max_g ||V_g-U_g||_2 <=4kappa_2,
max_g ||V_g-U_g||_op <=6kappa_inf.                    (SE11)
```

The appropriate cyclic spans for each generator lie in `E_+`
and have dimension at most `2rank(P)` or `3rank(P)`. They need
not agree or reduce the other generators.

Notice that the retained subspace `Q C^n` may contain both central
signs. Applying a positive-sector order-two/order-three argument
to that whole subspace without its central decomposition would
be incorrect. The sectorwise construction above avoids that step.

## 4. Erase the supplied support and estimate the residual

Define

```text
U_hat_g=P+Q V_g Q.                                    (SE12)
```

This replaces the now-reducing `P`-block by the trivial
representation and leaves `V_g` on `Q`. Because `ZP=P`, it
preserves the common central involution and every vertex relation.
Its negative-central restriction is exactly that of the input.
Moreover, the whole change remains supported on the corresponding
cyclic span from Section 3. Consequently

```text
rank(U_hat_(s_i)-S_i)<=2rank(P),
rank(U_hat_(b_i)-B_i)<=3rank(P),
max_g ||U_hat_g-U_g||_2<=2sqrt(3alpha).               (SE13)
```

The last estimate uses that a difference of unitaries has operator
norm at most two. A separate estimate retains the commutator
budget:

```text
||U_hat_g-V_g||_2=||(I-V_g)P||_2<=2sqrt(alpha),
max_g ||U_hat_g-U_g||_2<=4kappa_2+2sqrt(alpha).        (SE14)
```

Both bounds hold for the same output.

For any word `w`, all the matrices in `(SE12)` are block diagonal,
and all its letters are identity on `P`. Thus

```text
w(U_hat)=P+Q w(V) Q.
```

For a residual `R=w_1-w_2`, the `P` terms cancel exactly:

```text
R(U_hat)=Q R(V)Q.                                    (SE15)
```

If the sum of the two word lengths is at most `L`, unitary
telescoping and `(SE11)` give

```text
||R(U_hat)-Q R(U)Q||_2
    <=||R(V)-R(U)||_2<=4L kappa_2,
||R(U_hat)-Q R(U)Q||_op
    <=||R(V)-R(U)||_op<=6L kappa_inf.                 (SE16)
```

Inverse letters obey the same bounds, since taking the adjoint
preserves both norms. A relator residual `w-I` is included by
taking one word to be empty. There is no uncontrolled product of
compressed original generators here: the telescoping uses the
whole-space unitary tuples `V` and `U`.

## 5. The explicit contraction budget

Let the residual tuple have finitely many rows, let `L` dominate
their total word lengths, and put

```text
e=max_a ||R_a(U)||_2,
h=max_a ||Q R_a(U)Q||_2.
```

Section 4 gives

```text
def(U_hat)<=h+4L kappa_2.                            (SE17)
```

Hence the single explicit condition

```text
h+4L kappa_2<=e/2                                    (SE18)
```

implies a same-dimensional half-contraction. If also
`alpha<=B e`, the movement from `(SE13)` is at most
`2sqrt(3B e)`. No corner renormalization or dimension padding
occurs. An analogous operator estimate is

```text
max_a ||R_a(U_hat)||_op
 <=max_a ||Q R_a(U)Q||_op+6L kappa_inf.               (SE19)
```

For instance, exact residual support on `P` implies `h=0`,
but this alone gives no useful commutator bound. It yields a
contraction only when `4L kappa_2<=e/2` as well. More generally,
one may budget `h<=e/4` and `kappa_2<=e/(16L)`.

The theorem constructs the erasure operation from a supplied cut.
It does not construct a spectral cut meeting these budgets or show
that small normalized-HS defect supplies one. A sequence of such
cuts with summable rank and leakage costs would be extra input,
not a consequence of the finite-order rounding proof.

## 6. Why the generator movement needs a rank term

Take a central-positive exact vertex representation with

```text
S=-I,       B=I,
```

and any nonzero projection `P`. This is a valid modular
representation: `S^2=B^3=I`. Every generator commutator with
`P` is zero. Yet any replacement making `S_hat P=P` has

```text
||(S_hat-S)P||_2=2sqrt(alpha).
```

Thus no bound by a constant times the commutators alone can hold
for the generator movement of block trivialization. This example
can be used at both vertices. It concerns the replacement cost,
not a failure of the finite-order reducing projection theorem:
when the original generators already commute with `P`, that
rounding can and does leave them unchanged.

Conversely the retained-residual leakage in `(SE16)` is exactly
zero when the commutators vanish. The distinction between full
generator movement and damage to the surviving residual is the
useful conclusion: the former may cost square-root rank while
the latter is controlled linearly by commutator leakage.

Nothing here trivializes an arbitrary negative-central block,
preserves generator multiplicities, proves universal cut selection,
or establishes strict or flexible Iwahori stability.
