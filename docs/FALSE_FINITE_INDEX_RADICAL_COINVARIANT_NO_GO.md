# Finite-index subgroups do not revive the double radical

Date: 2026-08-12

## 1. Outcome

Let `Gamma<G` be the explicit square-zero Laurent Kun--Thom pair, let

```text
N=normalClosure_G(Gamma),
D=G *_Gamma G,
D_N=G *_N G,
R=ker(D->D_N)=Rad_sof(D)=R_fin(D).
```

The preceding central-route calculation proved only

```text
R/[D,R]=0.
```

A tempting escape is to pass to a finite-index subgroup `L<=D`.  The
radical survives in `L`, while fewer conjugations might make
`R/[L,R]` nonzero.  This note rules out that escape completely:

```text
                    R/[L,R]=0                       (FIC1)
```

for **every** finite-index subgroup `L<=D`.  In fact

```text
Rad_sof(L)=R_fin(L)=R=[L,R].                         (FIC2)
```

Thus no finite-index subgroup of the banked nonsofic double has a nonzero
ordinary central coinvariant class.  Passing to a cover cannot revive the
canonical central-envelope certificate.  Any successful FALSE construction
from this double must still use the genuinely noncentral `H_2`/kernel-carry
mechanism.

The proof gives a reusable criterion.  Write

```text
A=ker(Z[D_N/Gamma] -> Z[D_N/N]).                     (FIC3)
```

Then

```text
A_H=0                                                (FIC4)
```

for every finite-index subgroup `H<=D_N`.

## 2. The three structural inputs

The explicit pair has the following properties.

1. `Gamma<G` is infranormal: the semigroup

   ```text
   S={s in G : s Gamma s^(-1)<=Gamma}
   ```

   generates `G`.

2. `N` is Kazhdan.  Indeed

   ```text
   N=E_r(R_laurent) semidirect SL_3(Z[1/q]),
   ```

   and the construction proves property `(T)` for both factors and their
   extension.  Hence every finite-index subgroup of `N` has finite
   abelianization.

3. The quotient double is split:

   ```text
   D_N ~= N semidirect (Q*Q),                        (FIC5)
   ```

   where `Q=G/N` and the action of `Q*Q` factors through the fold
   `Q*Q->Q`.

We first record the finite-quotient consequence of infranormality.

### Lemma 1 (finite images cannot distinguish `Gamma` from `N`)

For every homomorphism `theta:D_N->F` to a finite group,

```text
theta(Gamma)=theta(N).                               (FIC6)
```

#### Proof

Restrict `theta` to either vertex copy of `G`.  If `s in S`, then

```text
theta(s)theta(Gamma)theta(s)^(-1)<=theta(Gamma).
```

The two finite subgroups have the same cardinality, so the inclusion is an
equality.  Since `S` generates `G`, `theta(Gamma)` is normal in the image of
that vertex group.  The subgroup `N` is the normal closure of `Gamma` in
`G`; consequently `theta(N)=theta(Gamma)`.  The two copies of `N` and
`Gamma` are identified in the amalgam, so the conclusion is independent of
the chosen vertex.  \(\square\)

## 3. Stabilizer abelianizations

Let `H_0 normal D_N` have finite index and put

```text
K=H_0 intersect N.                                  (FIC7)
```

Then `K` is normal in `D_N` and has finite index in `N`.  Since property
`(T)` passes to finite-index subgroups,

```text
K_ab=K/[K,K]
```

is finite.  Also `N/K` is finite, and therefore

```text
N/[K,K]
```

is finite.

The splitting `(FIC5)` now matters.  Let `P=Q*Q`.  Conjugation gives a
finite-image action

```text
alpha:P -> Aut(N/[K,K]),
```

and hence a finite quotient

```text
Theta_K:D_N=N semidirect P
  -> (N/[K,K]) semidirect alpha(P).                  (FIC8)
```

### Lemma 2 (all Mackey stabilizer maps are onto in degree one)

For every `g in D_N`, inclusion induces a surjection

```text
(H_0 intersect g Gamma g^(-1))_ab -> K_ab.           (FIC9)
```

#### Proof

Apply Lemma 1 to the finite quotient `(FIC8)`.  It gives

```text
Theta_K(g Gamma g^(-1))=Theta_K(N).                  (FIC10)
```

Take `k in K`.  By `(FIC10)` there is

```text
x in g Gamma g^(-1)
```

with `Theta_K(x)=Theta_K(k)`.  Both elements lie in `N`, and the restriction
of `Theta_K` to `N` is the quotient map `N->N/[K,K]`.  Thus

```text
x k^(-1) in [K,K].
```

In particular `x in K<=H_0`, and `x` and `k` have the same class in
`K_ab`.  This proves `(FIC9)`.  \(\square\)

## 4. Mackey--Shapiro calculation

Restrict the exact sequence

```text
0 -> A -> Z[D_N/Gamma] -> Z[D_N/N] -> 0             (FIC11)
```

to `H_0`.  Mackey decomposition and Shapiro's lemma identify the relevant
part of its homology long exact sequence as

```text
directSum_(H_0\D_N/Gamma)
  (H_0 intersect g Gamma g^(-1))_ab
        ->
directSum_(H_0\D_N/N)
  (H_0 intersect g N g^(-1))_ab
        -> A_(H_0)
        -> Z[H_0\D_N/Gamma]
        -> Z[H_0\D_N/N].                            (FIC12)
```

Because `N` is normal in `D_N`, every stabilizer in the middle sum is
`K`.  The natural map

```text
H_0\D_N/Gamma -> H_0\D_N/N                          (FIC13)
```

is a bijection.  Indeed `H_0` is normal, so these double-coset sets are the
coset spaces of the images of `Gamma` and `N` in the finite quotient
`D_N/H_0`; Lemma 1 says those images agree.

Under the bijection `(FIC13)`, every degree-one component in `(FIC12)` is
the map `(FIC9)`, hence is surjective by Lemma 2.  The degree-zero map at
the right of `(FIC12)` is an isomorphism.  Exactness forces

```text
A_(H_0)=0.                                           (FIC14)
```

Now let `H<=D_N` be arbitrary of finite index and let

```text
H_0=core_(D_N)(H).
```

Then `H_0 normal D_N` is finite index and `(FIC14)` holds.  Coinvariants
are transitive, so

```text
A_H=(A_(H_0))_(H/H_0)=0.                             (FIC15)
```

This proves `(FIC4)`.

## 5. Return to the radical

Let `L<=D` have finite index.  Since `R=R_fin(D)`, it is contained in the
normal core of `L`, hence `R<=L`.  Put

```text
H=L/R<=D_N.
```

The abelianized-radical theorem gives the `D_N`-module isomorphism

```text
R_ab ~= A.                                           (FIC16)
```

Therefore

```text
R/[L,R]
 ~= (R_ab)_H
 ~= A_H
 =0,                                                 (FIC17)
```

which proves `(FIC1)`.

It remains to identify the radical of `L`.  Certainly

```text
R<=Rad_sof(L)<=R_fin(L).
```

The first inclusion is finite-index radical permanence.  Explicitly, if
`phi:L->S` has sofic target, induce it along a transversal for `D/L` to a
homomorphism

```text
Ind(phi):D -> S wr Sym(D/L).
```

The target is sofic.  Every element of `R=Rad_sof(D)` lies in the normal
core of `L`, and the coordinate of `Ind(phi)(r)` at the trivial coset is
`phi(r)`.  Hence `phi(r)=1` for every `r in R`.

If `x in L\R`, its image in the residually finite group `D_N=D/R` is
nontrivial.  A finite quotient of `D_N` separates that image, and its
restriction to `L` separates `x`.  Hence `x` lies in neither radical.  This
proves `(FIC2)`.

## 6. Consequence for the FALSE search

Every finite-index subgroup `L<=D` is finitely presented, has the same full
sofic and finite residual `R`, and satisfies

```text
R=[L,R].                                             (FIC18)
```

The directed-coefficient compactness theorem therefore gives zero ordinary
central-envelope obstruction for every word in the radical of every such
`L`.  In particular, one cannot rescue the exact Baumslag--Solitar clock
class by passing to a congruence cover, taking a nonnormal finite-index
subgroup, or changing the finite presentation after passage to a cover.

This closes a route not covered by the earlier equality `R=[D,R]`: fewer
ambient conjugations do not create a central radical quotient.  The live
negative-side target remains a genuinely noncentral, nonliftable covariance
class.
