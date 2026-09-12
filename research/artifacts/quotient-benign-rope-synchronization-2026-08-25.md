# Quotient-compatible benign witnesses give synchronized rope quotients

Fix a normal subgroup `N` of a finite-rank free group `F`, put `Q=F/N`, and
let `(K,e,L)` be a benign witness.  In addition to

```text
e:F->K injective,             e(F) intersect L=e(N),
```

assume a homomorphism `sigma:K->Q` with

```text
sigma(e(f))=q(f),             sigma(L)=1.                       (1)
```

This note proves that effective residual finiteness of `Q` and of the first
rope group

```text
Gamma=<K,v | [v,L]=1>
```

implies the finite-quotient synchronization needed by the final graph HNN.

## 1. The finite swap quotient

Let `beta:Q->B` be a surjection onto a finite group.  Let `C_2=<c>` act on
`B times B` by swapping coordinates and set

```text
W_B=(B times B) semidirect C_2.
```

Define a homomorphism on the base group by

```text
j_beta(k)=((beta(sigma(k)),1),0).
```

For `l in L`, equation `(1)` gives `j_beta(l)=1`.  Consequently the swap
involution `c` centralizes every `j_beta(l)`.  The universal property of the
central HNN extension therefore gives

```text
lambda_beta:Gamma->W_B,
lambda_beta(k)=j_beta(k),     lambda_beta(v)=c.                 (2)
```

The image is all of `W_B`: surjectivity of `beta q` supplies the first copy
of `B`, conjugation by `c` supplies the second, and `v` supplies `c`.
Surjectivity is not needed below, since one could replace `W_B` by the finite
image of `lambda_beta`.

## 2. Reading the asymmetric rope map from one coordinate

Inside `Gamma` put

```text
F_0=e(F),              F_1=v^-1 e(F)v,
S=<F_0,F_1>.
```

The two copies meet in `e(N)`, and the rope homomorphism is

```text
tau:S->Q,              tau(e(f))=q(f),
                       tau(v^-1 e(f)v)=1.
```

Because `c` is an involution, `(2)` gives

```text
lambda_beta(e(f))=((beta(q(f)),1),0),
lambda_beta(v^-1 e(f)v)=((1,beta(q(f))),0).                    (3)
```

Thus `lambda_beta(S)` lies in the normal base `B times B` of `W_B`.  Projection
onto its first coordinate is a homomorphism on that base, and `(3)` shows on
the two generating copies that

```text
pr_1 lambda_beta|S = beta tau.                                 (4)
```

It follows immediately that

```text
ker(lambda_beta|S) <= ker(beta tau).                           (5)
```

This is where the apparent asymmetry is useful: the coordinate swap occurs
only in the auxiliary finite quotient, while projection to the first
coordinate recovers the original map which kills `F_1`.

## 3. Cofinality and equality of graph-edge kernels

Choose effective cofinal finite quotient sequences

```text
delta_n:Gamma->D_n,             beta_n:Q->B_n.
```

For each `n`, form `lambda_n=lambda_(beta_n)` and

```text
alpha_n=(delta_n,lambda_n):Gamma->D_n times W_(B_n),
p_n=(alpha_n,beta_n):Gamma times Q
       ->(D_n times W_(B_n)) times B_n.                        (6)
```

Pass to the finite images if quotient maps are required to be surjective.
The `delta_n` factors eventually separate `Gamma`, and the `beta_n` factors
eventually separate `Q`, so `(p_n)` is cofinal on `Gamma times Q`.

For the edge maps

```text
theta_0(s)=(s,1),               theta_1(s)=(s,tau(s)),
```

one kernel inclusion is automatic:

```text
ker(p_n theta_1) <= ker(p_n theta_0).
```

Conversely, if `p_n theta_0(s)=1`, then in particular
`lambda_n(s)=1`; equation `(5)` gives `beta_n(tau(s))=1`, so every component
of `p_n theta_1(s)` is trivial.  Hence

```text
ker(p_n theta_0)=ker(p_n theta_1)                               (7)
```

for every `n`.

All operations in `(2)` and `(6)` are effective from multiplication tables
for `B_n,D_n` and the specified generator maps.  Therefore a uniform witness,
uniform finite quotient sequences, and a computable `sigma` give the uniform
profinite synchronization required by the MF compiler.

## 4. The quotient-compatible hypothesis forces a retract

The ordinary `BenignWitness` in the present Higman development records only
`e(F) intersect L=e(N)`.  It does not record `(1)`, and neither residual
finiteness assertion follows from benignness.  More importantly, `(1)` cannot
be added on the positive delayed branch.

Let

```text
P=K/normalClosure_K(L).
```

This is finitely presented because `K` is finitely presented and `L` is
finitely generated.  The assignment

```text
i(q(f)) = image of e(f) in P
```

is well-defined because `e(N)<=L`.  It is injective: if `e(f)` dies in `P`,
then `e(f)` belongs to `normalClosure(L)<=ker(sigma)`, so
`q(f)=sigma(e(f))=1`.  Since `sigma(L)=1`, `sigma` factors through a map
`r:P->Q`, and `r i=id_Q`.  Hence `Q` is a retract of `P`.

Retracts of finitely presented groups are finitely presented.  For an
elementary presentation proof, represent the idempotent `i r:P->P` by words
on a finite generating set of `P` and add the finitely many relations saying
that every generator equals its idempotent image; the resulting quotient is
the retract.  The positive FIN/INF limit `Q` is not finitely presented by the
finite-stage compactness argument already recorded in the profinite-route
audit.  Thus the finite swap theorem remains valid, but its hypothesis
cannot close the intended compiler.  The route through
`positive-scaffold-has-quotient-compatible-rf-witness` is refuted.
