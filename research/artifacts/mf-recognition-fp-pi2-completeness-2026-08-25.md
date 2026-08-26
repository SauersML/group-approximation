# MF recognition for finite presentations is Pi-zero-two complete

This note assembles the upper bound, the uniform FIN/INF switch, and the
MF-safe finite-presentation compiler into the claimed many-one completeness
theorem.  All group presentations below are effective and use finite alphabets
after the bridge step.

## Theorem

For the standard recursive coding of finite group presentations,

```text
MF_fp    is Pi^0_2-complete,
NONMF_fp is Sigma^0_2-complete.                              (T1)
```

## 1. Upper bounds

For a finite presentation `P` and a scale `n`, enumerate the words of length
at most `n`.  A finite certificate chooses a matrix dimension, labels each
word either trivial or separated, gives a finite normal-closure derivation for
every trivial label, and gives a unitary generator tuple with relator defect
at most the prescribed rational tolerance and displacement at least `1/2` on
every separated word.  Feasibility of the resulting finite system of
polynomial equalities and inequalities is decidable over the real closed
field.

The local normalization theorem therefore gives a recursive predicate `C`
with

```text
P presents an MF group  iff  forall n exists c C(P,n,c).       (T2)
```

Thus `MF_fp` is `Pi^0_2` and `NONMF_fp` is `Sigma^0_2`.  This is
`mf-recognition-has-a-pi2-upper-bound`.

## 2. The exact recursive switch

Fix the finitely presented non-MF group `E` from
`finitely-presented-sofic-non-mf`.  From a c.e. index `e`, the exact ray
switch produces a countably generated recursive group `C_e` with

```text
e in INF  => C_e=1,
e in FIN  => C_e=E.                                           (T3)
```

Apply the three-generator bidirectional bridge.  Uniformly obtain a
finite-rank recursive presentation

```text
Q_e=F/N_e
```

such that

```text
e in INF  => Q_e=H:=B3(1),
e in FIN  => E embeds in Q_e.                                 (T4)
```

Killing the `C_e` coordinate gives an epimorphism `Q_e->H` on every branch.
If `N_+` is the kernel of the positive presentation `F->H`, then

```text
N_e <= N_+                                                    (T5)
```

uniformly.

## 3. The positive bridge has effective finite CEP

The bridge embedding is

```text
H -> P=F(x_1,y) times F(x_2,t),
x |-> (x_1,x_2),   y |-> (y,1),   t |-> (1,t).                (T6)
```

Its image is exactly the kernel of the difference of the two `x`-exponent
maps, so `H` is finitely generated normal in `P` and `P/H=Z`.

For a finite-index normal `J` in `H`, intersect its orbit under the cyclic
quotient action.  Finitely generated groups have only finitely many subgroups
of a fixed finite index, so the intersection is a finite-index `P`-normal
subgroup `M<=J`.  The cyclic action on `H/M` has finite order; quotienting the
cyclic lift by that order gives a finite quotient `r:P->C` with

```text
ker(r|H)=M<=J.                                                (T7)
```

This construction is effective from the multiplication table of `H/J`.
It is `three-bridge-is-cyclic-fiber-product-with-finite-cep`.

## 4. Add the graph witness without changing the recursive kernel

Run the MF-safe benign construction for `N_e`, obtaining a finitely presented
overgroup `K_e^0`, an embedded `F`, and a finitely generated subgroup `L_e^0`
whose intersection with `F` is `N_e`.  The symmetric-double, amenable-edge,
and central-HNN refactor preserves a regular operator-MF realization on the
positive branch.

Independently, form the fixed graph witness for `N_+`:

```text
K^g=F times P,
L^g={(f,j(q_+(f))):f in F}.                                  (T8)
```

Take the direct-product/intersection witness

```text
K_e=K_e^0 times K^g,
L_e=L_e^0 times L^g,
F -> K_e diagonally.                                          (T9)
```

By `(T5)`, its intersection with `F` is

```text
N_e intersect N_+ = N_e.                                    (T10)
```

Thus `(T9)` is a uniform benign witness on both branches.  On `INF`, its
ambient group is regularly operator-MF realized because both factors are.
The first rope extension

```text
Gamma_e=<K_e,v | [v,L_e]=1>                                  (T11)
```

is regularly operator-MF by regular central-HNN closure.

## 5. Finite graph maps and tensor synchronization

Inside `(T11)` put

```text
S_e=<F,F^v>=F *_(N_e) F,
tau_e:S_e->Q_e,
tau_e|F_0=q_e,             tau_e|F_1=1.                       (T12)
```

On `INF`, let `beta_n:H->B_n` be cofinal finite quotients.  Use `(T7)` to
choose `r_n:P->C_n` with `ker(r_n j)<=ker(beta_n)`.  Map the ordinary witness
factor `K_e^0` trivially and map the graph factor by

```text
(f,p) |-> (r_n(j(q_+(f))),r_n(p)) in C_n times C_n.           (T13)
```

The subgroup `L_e` lands on the diagonal.  Therefore `(T13)` extends over
the first rope letter by sending `v` to the coordinate swap, giving a finite
homomorphism `lambda_n:Gamma_e->W_n`.  On `S_e`, first-coordinate projection
is `r_n j tau_e`; hence

```text
ker(lambda_n|S_e) <= ker(beta_n tau_e).                        (T14)
```

Represent `Gamma_e` by regular-MF matrices `U_n`.  Tensor `U_n` with the left
regular representation of the finite image of
`(lambda_n,beta_n):Gamma_e times H->W_n times B_n`.  Equality of the two edge
kernels supplied by `(T14)` makes the finite restrictions exactly unitarily
conjugate, while the common `U_n(s)` factor is unchanged.  Thus the two edge
C-star embeddings agree in one matrix corona.

Ueda's universal-HNN corner construction and Shulman's compatible-corona
criterion make the final HNN algebra MF.  The tensor trace is the regular
character: `U_n` kills every nonidentity `Gamma_e` element in trace, and the
cofinal `beta_n` kill every nonidentity element of `H` when the first
coordinate is trivial.  The reduced von Neumann HNN normal form then
separates every nonidentity Britton-reduced word.  Consequently

```text
R_e=<Gamma_e times Q_e,u |
     u(s,1)u^-1=(s,tau_e(s)), s in S_e>                        (T15)
```

is regularly operator-MF on `INF`.

On `FIN`, no approximation claim is needed.  The ordinary Higman rope proof
applied to `(T10)` embeds `Q_e` in the finitely presented group `R_e`, and
`Q_e` contains `E`.  Since MF is inherited by subgroups and `E` is not MF,
`R_e` is not MF.

The rope presentation is finite uniformly in `e`: `K_e` is finitely
presented, `L_e` and `F` are finitely generated, and the final rope relations
are imposed only on a fixed finite generating set of `F`.

We have therefore constructed a total computable map `e |-> code(R_e)` with

```text
e in INF  => R_e is MF,
e in FIN  => R_e is not MF.                                  (T16)
```

So `FIN <=_m NONMF_fp` and, by complements, `INF <=_m MF_fp`.  Since `FIN`
and `INF` are respectively `Sigma^0_2`- and `Pi^0_2`-complete, `(T1)` follows
from `(T2)`.
