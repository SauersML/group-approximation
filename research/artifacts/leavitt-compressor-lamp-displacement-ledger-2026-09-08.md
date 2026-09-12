# The native compressor supplies an exponential family of bounded displaced vectors

2026-09-08. Written ring identities and finite-dimensional Hilbert-space
estimates. No code, build, numerical search, or Lean verification was run.
This does not determine hyperlinearity of the binary Leavitt unit group.

Use the rank-four cell of
[the non-MF manuscript](../../non_mf_groups_exist.tex), with
`R=L_(F_2)(1,2)`, `ts=1`, `e=1-st`, and `L=EL_3(R)` in the first
three coordinates. Its compressor `u` and centralizing involution `z`
satisfy

```text
u L u^(-1) <= L,
z=diag(1,1,1,1+et) in C_H(L),
u z u^(-1)=x_12(e),
u x_ij(a) u^(-1)=x_ij(sat)  (1<=i!=j<=3).
```

Here `z` is the manuscript's centralizer element, not the marked
order-three native generator `c`. Put

```text
ell=x_23(1),       D=x_13(e),       z_j=u^j z u^(-j)  (j in Z).
```

Likewise `D` here is the compression defect, not a Thompson generator.
All these are units of the same `H=R^x`, using the rank-four prefix
identification. They can be represented by fixed native words; subsequent
products and conjugates below use literal concatenations of those words.

## 1. The actual bilateral lamp chain

For `j>=1`, the displayed compressor identities give

```text
z_j=x_12(e_(j-1)),       e_q=s^q e t^q.
```

The `e_q` are nonzero pairwise orthogonal idempotents. Nonvanishing follows
from `t^q e_q s^q=e!=0`; orthogonality follows from `es=te=0`. Also

```text
sum_(q=0)^(m-1) e_q=1-s^m t^m.
```

Thus the positive-index `z_j` are independent commuting involutions:
the product over a nonempty finite set is the nonidentity root with
coefficient the sum of its distinct orthogonal idempotents. Conjugating
any finite set of integer indices into the positive indices proves the
same assertion for the whole bilateral chain.

For `j<=0`, `z_j` centralizes `L`. Indeed,
`u^k L u^(-k)<=L` implies that `u^(-k) z u^k` centralizes `L`.
Consequently, for every integer `m>=2`,

```text
A_m=<z_(-m+1),...,z_0> <= C_H(L),       |A_m|=2^m.
```

Let `a_1,...,a_M`, with `M=2^(m-1)`, be the elements of the coset

```text
z_0 <z_(-m+1),...,z_(-1)>.
```

Put `y_i=u a_i u^(-1)=z_1 b_i`. The distinct `b_i` belong to
`<z_(-m+2),...,z_0>`, hence centralize `L`. Since

```text
[z_1,ell]=D,       D^2=1,
[D,z_1]=[D,ell]=1,
```

we have the exact identities

```text
ell y_i ell^(-1)=D y_i,
[y_i,ell]=D !=1.                                     (1)
```

This gives exponentially many operator-norm-one group unitaries that
centralize `L` before the same compressor is applied, and have the same
nontrivial displacement afterwards.

Their native word lengths grow only linearly with `m`. Ordering the
lamps by increasing index gives the spelling

```text
a=u^(-(m-1)) z^(epsilon_1) u z^(epsilon_2) ... u z^(epsilon_m),
epsilon_m=1,
```

whose expanded length is at most `2(m-1)|u|+m|z|`.

## 2. Exact orthogonal displacement in canonical trace

Let `lambda` be the regular representation and `tau` its canonical trace.
Write `Y_i=lambda(y_i)` and

```text
Z_i=lambda(ell) Y_i lambda(ell)^*-Y_i.
```

The original vectors `lambda(a_i)` are orthonormal. Equation (1), and the
fact that every `b_i` centralizes `D,z_1`, give

```text
Z_i=(lambda(D)-I)lambda(z_1 b_i),
<Z_i,Z_j>=2 tau(lambda(b_i^(-1)b_j))
          -2 tau(lambda(D b_i^(-1)b_j)).             (2)
```

For `i!=j`, both arguments on the right are nonidentity. The first is
nonidentity by lamp independence. For the second, note that
`b_i^(-1)b_j in C_H(L)`, whereas
`[D,x_32(1)]=x_12(e)!=1` shows directly that `D` does not centralize
`L`. Therefore

```text
<Z_i,Z_j>=2 delta_ij.
```

The operator `(Ad(lambda(ell))-I)Ad(lambda(u))` is thus exactly
`sqrt(2)` times an isometry on the `M`-dimensional span of the
`lambda(a_i)`. This statement concerns the canonical GNS Hilbert space;
it is not a finite-dimensional model of `H`.

## 3. A finite matrix ledger using literal word traces

Now evaluate the chosen native words on any unitary tuple in dimension
`n`. No exact representation of `H` is assumed. Denote evaluations by
`U,E,A_i`, and define, by literal matrix operations,

```text
Y_i=U A_i U^*,       Z_i=E Y_i E^*-Y_i.
```

In particular `||A_i||_op=||Y_i||_op=1` and `||Z_i||_op<=2`.
For each `i!=j`, require absolute normalized trace at most `xi` for
each of the following four *literal native words*:

```text
y_i^(-1)y_j,
(ell y_i ell^(-1))^(-1)y_j,
y_i^(-1)(ell y_j ell^(-1)),
(ell y_i ell^(-1))^(-1)(ell y_j ell^(-1)).             (3)
```

For each `i`, require the same bound for

```text
y_i^(-1)(ell y_i ell^(-1)).                          (4)
```

All words in (3)--(4) are nonidentity in the actual group. In (3) their
group values are respectively `b_i^(-1)b_j`,
`D b_i^(-1)b_j`, `D b_i^(-1)b_j`, and `b_i^(-1)b_j`; in (4) the
value is `D`. Their different spellings are retained in the trace
hypotheses. They are not silently identified when evaluated on an
approximate tuple.

Expanding the matrix inner products literally now gives, without any
additional multiplicativity error,

```text
2-2xi <= ||Z_i||_2^2 <= 2+2xi,
|<Z_i,Z_j>| <= 4xi  (i!=j).
```

For `0<=xi<1`, the Gram matrix `G_Z` therefore satisfies

```text
Tr(G_Z)>=2M(1-xi),
Tr(G_Z^2)<=4M(1+xi)^2+16M(M-1)xi^2.
```

The inequality `rank(G_Z)>=Tr(G_Z)^2/Tr(G_Z^2)` proves

```text
dim span{Z_i} >=
 M(1-xi)^2 / ((1+xi)^2+4(M-1)xi^2),
M=2^(m-1).                                         (5)
```

This is an ambient Hilbert-space rank bound in `HS(M_n)`, whose total
dimension is `n^2`.

The trace hypotheses can be supplied by the
[single-cycle finite trace certificate](leavitt-single-c-trace-certificate-2026-09-08.md):
apply it separately to every prescribed nonidentity spelling in
(3)--(4), and take the union of the resulting finite kernel lists.
Repeated group elements with different spellings cause no difficulty.
Alternatively, if only one representative per group element has trace
bound `delta`, include a true equality relator comparing each spelling
with that representative. If each such comparison has defect at most
`kappa`, unitary invariance and `|tr(X)|<=||X||_2` give the above
ledger with `xi=delta+kappa`. No other word errors are hidden in (5).

## 4. Low-energy location and the remaining dimension dependence

Fix a finite set `S` in `L` containing `ell`, and let `S_s` be its
evaluated unitaries. If the literal commutator rows `[s,a_i]` all have
defect at most `kappa`, then

```text
Delta=sum_(s in S)(Ad(S_s)-I)^*(Ad(S_s)-I),
<A_i,Delta A_i><=|S| kappa^2.
```

For `P_lambda=1_[0,lambda](Delta)`, `lambda>0`, spectral calculus gives

```text
||(I-P_lambda)A_i||_2 <= sqrt(|S|/lambda) kappa.      (6)
```

In contrast, because `ell in S` and `||Ad(E)-I||<=2`,

```text
||(I-P_lambda)Y_i||_2
 >= (sqrt(2-2xi)-sqrt(lambda))_+/2.                 (7)
```

Indeed `||(Ad(E)-I)P_lambda Y_i||_2<=sqrt(lambda)` and the remaining
piece contributes at most twice its norm. Thus the native compressor
moves every selected bounded vector a fixed distance out of the
low-energy space when the two displayed error parameters are small.

There is also a direct lower bound on the Hilbert-space trace of the
compressor's leakage. Set

```text
eta=sqrt(|S|/lambda) kappa,
gamma=(sqrt(2-2xi)-sqrt(lambda))_+/2,
P=P_lambda,       T=(I-P)Ad(U)P,
W=sum_i |A_i><A_i|.
```

Here `W,T` act on `HS(M_n)`, with its normalized matrix HS inner
product. Let `Tr_HS` denote the ordinary, unnormalized operator trace
on that `n^2`-dimensional Hilbert space. The first word in (3) already
controls `|<A_i,A_j>|`: its trace equals `tr(A_i^*A_j)` by exact
matrix conjugation with `U`. Hence

```text
Tr_HS(W^2)<=M+M(M-1)xi^2.                            (8)
```

Equations (6)--(7) and the triangle inequality give
`||T A_i||_2>=(gamma-eta)_+`. Since `T` is a contraction,

```text
Tr_HS(T^*T W)=sum_i ||T A_i||_2^2
             >=M(gamma-eta)_+^2,
Tr_HS((T^*T)^2)<=Tr_HS(T^*T).
```

Hilbert--Schmidt Cauchy--Schwarz for operators on `HS(M_n)`, followed
by (8), therefore proves

```text
Tr_HS(T^*T)>=
 M(gamma-eta)_+^4 / (1+(M-1)xi^2),

||(I-P_lambda)Ad(U)P_lambda||_(2,n^2)^2 >=
 M(gamma-eta)_+^4 / (n^2(1+(M-1)xi^2)).              (9)
```

The final norm is normalized by the Hilbert-space dimension `n^2`,
not by the original matrix dimension `n`. This quantifies actual
projection leakage for the native compressor without promoting
pointwise bounded-vector estimates to an operator-norm estimate.

Equations (5)--(9) still do not force positive density in all `n^2`
Hilbert-space dimensions. When `gamma-eta` stays positive, the rank
and unnormalized leakage bounds are of order `M/(1+M xi^2)`.
For these bounds to give a fixed positive fraction of
`n^2`, one needs `M` at least comparable to `n^2` and `xi=O(1/n)`.
Here that corresponds to depth `m` of order `2 log_2(n)`, with the
lamp words themselves of length `O(log n)`. The trace certificates
used to enforce (3)--(4) have no such asserted length bound.

Full-kernel asymptotic feasibility controls every fixed finite stage;
it supplies no relation between matrix dimension and the depth or
accuracy available at that stage. This dimension-adaptive coupling
remains unproved. The construction supplies actual native bounded
vectors, exact canonical orthogonal displacement, and the finite-error
rank ledger; it supplies neither a dimension-uniform gap nor a
hyperlinear model.
