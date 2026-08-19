# The factorized Iwahori gate is a cosystolic-angle problem

Date: 2026-08-14

## 1. Outcome

The factorized `BS(1,4)` reduction in
`TRUE_IWAHORI_MATCHING_REDUCES_TO_FACTORIZED_BS14_REPAIR.md` does not ask
for degree-two cohomology to vanish.  In fact, that stronger route is
impossible for

```text
G=SL_2(Z[1/2])=K *_(B_+ ~= B_-) K,       K=SL_2(Z).   (ICA1)
```

The rational Euler characteristic is

```text
chi(G)=1/12.                                           (ICA2)
```

Consequently every torsion-free finite-index subgroup `G_0` has positive
second `L^2`-Betti number.  Along residual finite towers, Lueck
approximation produces finite-dimensional unitary coefficient modules with
nonzero degree-two cohomology of positive normalized dimension.  These
modules occur inside adjoint modules of honest finite-quotient
representations.

Thus neither `2`-Kazhdan vanishing nor a degree-one **coboundary** expansion
theorem can close the Iwahori problem.  The correct linear invariant is the
smallest positive singular value after quotienting by the exact kernel: a
Hilbert-space **cosystolic angle**.  Nonzero harmonic degree-two modes are
allowed.

This gives a more precise endpoint for factorized `BS(1,4)` repair:

1. prove that the mismatch produced by two exact modular vertices has
   vanishing harmonic component after the `BS(1,4)` correction; and
2. prove a uniform upper-Laplacian gap on the orthogonal complement of the
   harmonic space for the finite congruence coefficient systems.

Those two statements support a dimension-free Newton iteration **inside a
uniform neighborhood of the compatible locus**.  They do not by themselves
put an arbitrary small-defect pair in that neighborhood.  A third statement
is required:

3. prove a uniform basin-capture theorem saying that sufficiently small
   Iwahori defect forces the pair into the Newton neighborhood of some
   compatible representation.

The first statement is an integrability assertion special to the
factorization `C=AB`; the second is a cosystolic spectral estimate; the third
is the global microstate-uniqueness input.  This separates the actual target
from both the false demand that all of `H^2` disappear and the false inference
from local rigidity to global stability.

## 2. The Euler characteristic forces degree-two harmonic mass

The modular group has the amalgam presentation

```text
K=C_4 *_(C_2) C_6.                                    (ICA3)
```

Therefore

```text
chi(K)=1/4+1/6-1/2=-1/12.                             (ICA4)
```

The Iwahori subgroup has index three, so

```text
chi(B_+)=3 chi(K)=-1/4.                               (ICA5)
```

Euler characteristic is additive for an amalgam of groups of finite
rational homological type.  Hence `(ICA1)` gives

```text
chi(G)=2 chi(K)-chi(B_+)
      =-1/6+1/4
      =1/12.                                          (ICA6)
```

Choose a torsion-free finite-index subgroup `G_0<G`.  It has a finite
two-dimensional classifying complex: pass to torsion-free finite-index free
subgroups in the finite graph of virtually-free groups `(ICA1)` and use the
standard graph-of-spaces model.  Thus

```text
chi(G_0)=[G:G_0]/12>0,
beta_q^(2)(G_0)=0                 (q>2),
beta_0^(2)(G_0)=0.                                (ICA7)
```

The `L^2` Euler formula now gives

```text
beta_2^(2)(G_0)
 =chi(G_0)+beta_1^(2)(G_0)
 >=chi(G_0)>0.                                      (ICA8)
```

This elementary computation agrees with the description of
`SL_2(Z[1/p])` as measure equivalent to a product of two nonabelian free
groups, but no measure-equivalence input is needed for positivity.

## 3. Finite-dimensional non-scalar `H^2` is unavoidable

Let

```text
G_0>G_1>G_2>...                                      (ICA9)
```

be a nested normal residual chain.  Lueck approximation applied to the
finite classifying complex of `G_0` gives

```text
dim_C H^2(G_n,C)/[G_0:G_n]
    -> beta_2^(2)(G_0)>0.                            (ICA10)
```

Put

```text
P_n=l2(G_0/G_n)=C 1 directSum P_n^0.                 (ICA11)
```

Shapiro's lemma and additivity in the coefficient module give

```text
H^2(G_0,P_n) ~= H^2(G_n,C),
H^2(G_0,P_n^0) directSum H^2(G_0,C)
    ~= H^2(G_n,C).                                   (ICA12)
```

The second summand on the left has fixed dimension, whereas the right side
has dimension linear in `[G_0:G_n]`.  Hence

```text
lim_(n->infinity)
 dim H^2(G_0,P_n^0)/dim(P_n^0)
 =beta_2^(2)(G_0)>0.                                 (ICA13)
```

The module `P_n^0` has no invariant vector.  Inducing it from `G_0` to `G`
and applying Shapiro again produces finite-dimensional unitary
`G`-modules `V_n` with

```text
V_n^G=0,
H^2(G,V_n)!=0,                                       (ICA14)
```

and the cohomology dimension remains a positive fraction of
`dim(V_n)` after accounting for the fixed index `[G:G_0]`.

These are not irrelevant coefficient systems.  If `rho_n` is the
finite-quotient permutation representation before removing constants, then

```text
Ad(rho_n) on End(l2(G_0/G_n))
    ~= P_n directSum ... directSum P_n               (ICA15)
```

with `[G_0:G_n]` copies: under left translation, matrix units are carried by

```text
(x,y) |-> (g x,g y),                                 (ICA16)
```

and the orbits are indexed by `x^(-1)y`.  Thus adjoint coefficient systems
at honest finite-quotient representations already contain extensive
degree-two harmonic cohomology.  Writing `m_n=[G_0:G_n]`, one gets the
quantitative identity

```text
dim H^2(G_0,Ad rho_n)/dim End(P_n)
 =m_n dim H^2(G_n,C)/m_n^2
 ->beta_2^(2)(G_0)>0.                                (ICA16a)
```

Passing between `G_0` and `G` by finite induction does not remove it.  More
explicitly, the diagonal block algebra inside
`End(Ind_(G_0)^G P_n)` is the `G`-module
`Ind_(G_0)^G End(P_n)`.  It is an orthogonally complemented adjoint
submodule, and Shapiro identifies its degree-two cohomology with the
cohomology in `(ICA16a)`.

This rules out the hoped-for statement

```text
H^2(G,Ad rho)=0 for every finite-dimensional rho.     (ICA17)
```

It also rules out trying to deduce factorized repair from a uniform theorem
whose conclusion includes `(ICA17)`.

## 4. Bass--Serre cohomology identifies the factor gate

Let `V` be a unitary `G`-module.  Both `K` and `B_+` are virtually free.
Over `C`, their cohomology vanishes above degree one.  The
Mayer--Vietoris sequence for `(ICA1)` therefore ends in

```text
H^1(K,V) directSum H^1(K,V)
  --R_V--> H^1(B_+,V)
  --> H^2(G,V)
  -->0.                                               (ICA18)
```

The second restriction in `R_V` is twisted by the Iwahori isomorphism
`sigma`.  Formula `(ICA18)` says exactly:

```text
H^2(G,V)=coker(R_V).                                  (ICA19)
```

At an honest compatible representation `rho:G->U(d)`, take

```text
V=u(d),                  action=Ad rho.               (ICA20)
```

Infinitesimal deformations of the two exact modular vertices are vertex
`1`-cocycles.  After quotienting the tangent spaces by infinitesimal unitary
conjugacy, they are represented by the two `H^1(K,V)` terms in `(ICA18)`.
The derivative of their edge mismatch is precisely `R_V`.  Consequently,
in these quotient tangent spaces:

- `ker(R_V)` is the tangent space to compatible vertex pairs;
- `coker(R_V)=H^2(G,V)` is the harmonic obstruction space normal to the
  vertex-generated mismatch directions; and
- the quantitative tangent-repair constant is

```text
kappa(rho)
 =inf { ||R_V xi|| : xi perpendicular ker(R_V),
                       ||xi||=1 }.                    (ICA21)
```

Here the cohomology groups carry the quotient Hilbert norms induced by any
fixed finite cellular model.  Changing that model only changes constants;
uniformity in `rho` and `d`, not the normalization choice, is the issue.

The relevant estimate is a uniform lower bound on the **positive** singular
values in `(ICA21)`.  Such a bound is compatible with an arbitrarily large
cokernel.  This is why cosystolic expansion, which measures distance to the
kernel, is the right analogy, whereas coboundary expansion or `H^2=0` is
not.

## 5. Where `BS(1,4)` stability enters

For an almost-compatible pair, write as before

```text
A=alpha(w),       B=beta(w),       X=beta(u),
C=AB.                                                 (ICA22)
```

The two noncentral edge defects imply

```text
||C X C^*-X^4||_2<=3 delta.                           (ICA23)
```

Hilbert--Schmidt stability of `BS(1,4)` repairs `(C,X)` to an exact
fourth-power pair.  What it does not remember is whether the correction of
`C` splits into corrections of `A` and `B` tangent to the two modular
representation varieties.

In the linear picture, this missing assertion is not `(ICA17)`.  It is:

> the corrected defect has zero component in `coker(R_V)`, and its
> component in `im(R_V)` admits a preimage with norm bounded uniformly by
> the defect.

The first clause is **harmonic orthogonality**.  The second is the uniform
cosystolic angle `(ICA21)`.  Together they are exactly what is needed to
factor the repaired `BS(1,4)` stable letter as `A'B'` while retaining both
modular vertices.

## 6. A dimension-free Newton endpoint

The remaining theorem can now be stated without asking for false
cohomology vanishing.

> **Iwahori cosystolic Newton theorem.**  There are constants
> `kappa,c,r>0`, independent of the matrix dimension and of the congruence
> type, and a function `b(delta)->0`, with the following properties.
>
> 0. Every exact modular vertex pair of Iwahori defect at most `delta` is,
>    after the permitted negligible padding, within `b(delta)` of some
>    compatible representation.
> 1. For every compatible representation `rho` and every pair of exact
>    modular vertex representations within `r` of `rho`, the positive
>    singular values of `R_(Ad rho)` are at least `kappa`.
> 2. After exact `BS(1,4)` repair in this neighborhood, the harmonic
>    component of the edge mismatch is at most `c delta^2`.
> 3. The modular representation strata admit local retractions with a
>    dimension-free quadratic remainder.

Choose `delta` small enough that `b(delta)<r`.  Item 0 supplies a compatible
base point in the Newton neighborhood.  Solve the image component using
`(ICA21)`, retract to the two exact vertex varieties, and use item 2 to
obtain

```text
delta_(next)<=C delta^2,
move_(next)<=C delta.                                 (ICA24)
```

For sufficiently small initial defect, Newton iteration converges and the
total movement is `O(delta)`.  The limit is an exactly compatible pair.
The standard negligible padding used for central-sign matching handles
changes of finite-order multiplicity strata.

Thus `(ICA24)` would answer Dogon--Vigdorovich Question 1.4 positively and
produce their explicit nonhyperlinear finite central extension.

## 7. What has and has not been proved

The following parts of this note are exact:

1. `chi(G)=1/12` and `beta_2^(2)>0` after passing to a torsion-free
   finite-index subgroup;
2. residual finite towers yield non-scalar finite-dimensional coefficient
   modules with extensive `H^2`;
3. these modules occur in adjoint finite-quotient coefficient systems;
4. the Bass--Serre sequence identifies `H^2` as the cokernel of the
   linearized Iwahori restriction-difference map; and
5. factorized repair needs a positive singular-value estimate modulo the
   kernel, not vanishing of the cokernel.

The Iwahori cosystolic Newton theorem in Section 6 is not proved here.  In
particular, item 0 is not a consequence of items 1--3.  Items 1--3 are local
statements at an honest finite-dimensional representation of `G`; item 0
rules out sequences of small-defect vertex pairs which remain a fixed
distance from every honest representation.  Such a sequence becomes an
exact representation only after passage to a tracial matrix ultraproduct,
so excluding it is precisely a matrix-coordinate lifting or microstate-
uniqueness assertion.

This corrects an earlier overstatement in this note: a dimension-free Newton
iteration cannot be started from small defect alone.  Its advantage remains
that it permits the harmonic mass which arithmetic topology forces, while
isolating the additional local claim that the special `BS(1,4)` correction
never enters that mass.  The global basin-capture claim is an independent,
load-bearing gate.

## References

- A. Dogon and I. Vigdorovich, *Hyperlinearity, stability and asymptotic
  spectral gap of higher rank lattices*,
  [arXiv:2506.20843v2](https://arxiv.org/abs/2506.20843v2).
- W. Lueck, *Approximating `L^2`-invariants by their finite-dimensional
  analogues*, Geom. Funct. Anal. 4 (1994), 455--481,
  [doi:10.1007/BF01896404](https://doi.org/10.1007/BF01896404).
- J.-P. Serre, *Trees*, for the Iwahori amalgam and Bass--Serre
  Mayer--Vietoris sequence.
- A. Levit and I. Vigdorovich, *Characters of solvable groups,
  Hilbert--Schmidt stability and dense periodic measures*,
  [arXiv:2206.02268](https://arxiv.org/abs/2206.02268), for the
  `BS(1,4)` stability input.
