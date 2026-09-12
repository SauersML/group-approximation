# ASH rank realization as uniform quadratic trace selection

Date checked: 2026-09-11. Lane: `operator_algebras`.

This proves an exact, quantitative reformulation of approximate rank
realization and turns the ASH question into a finite-stage matrix-field
selection problem. It does **not** prove the selection assertion, STW XXIV,
or the Toms--Winter conjecture. No computation is used.

The reduction is useful because the new objective involves only first and
second moments, is norm continuous at every fixed matrix size, and can be
tested on all irreducible fibres of an ASH building block. A proposed
counterexample must exhibit one fixed positive lower bound for this objective
at every later stage and every matrix size. A rank calculation at one stage
or a check of finitely many limit traces cannot supply that certificate.

## 1. Quantitative equivalence

Let `A` be a unital C*-algebra with nonempty `T(A)`, and let
`f:T(A)->R` be continuous. Extend every tracial state to `M_m(A)` by
`tau_m=tau tensor Tr_m`, with **unnormalized** `Tr_m`. All matrix sizes below
are finite but unrestricted. Define

```text
Delta_A(f) = inf_{m>=1, a in M_m(A)_+}
               sup_{tau in T(A)} |d_tau(a)-f(tau)|,

E_A(f) = inf_{m>=1, 0<=b<=1 in M_m(A)}
           max{ sup_tau |tau_m(b)-f(tau)|,
                sup_tau tau_m(b-b^2) }.
```

Both quantities are finite, since the zero element is allowed. Then

```text
Delta_A(f) <= 3 E_A(f),                 E_A(f) <= 2 Delta_A(f).       (1)
```

In particular, `Delta_A(f)=0` if and only if `E_A(f)=0`. Affineness,
simplicity, nuclearity, stable rank, and comparison are unnecessary in (1).

**Proof of the first inequality.** For `0<=t<=1`,

```text
|1_(1/2,1](t)-t| <= 2t(1-t).
```

For any candidate `b`, put `a=(b-1/2)_+`. The rank `d_tau(a)` is the trace of
the Borel spectral projection `1_(1/2,1](b)` in the tracial GNS von Neumann
algebra. Integrating the displayed scalar inequality gives

```text
|d_tau(a)-tau_m(b)| <= 2 tau_m(b-b^2).
```

The triangle inequality and then the infimum give the assertion. No spectral
projection is asserted to lie in `A`.

**Proof of the second inequality.** Fix `delta>Delta_A(f)` and a positive
`a in M_m(A)` with `sup_tau|d_tau(a)-f(tau)|<delta`. Put
`g_k(t)=min(1,kt)` for `t>=0`. For every `tau`,

```text
tau_m(g_k(a)^2) increases to d_tau(a) > f(tau)-delta.
```

For any `eta>0`, the open sets

```text
U_k={tau:tau_m(g_k(a)^2)>f(tau)-delta-eta}
```

increase and cover the compact set `T(A)`. Thus one `U_k` is all of `T(A)`.
With `b=g_k(a)`, simultaneously for all traces,

```text
f-delta-eta < tau_m(b^2) <= tau_m(b) <= d_tau(a) < f+delta.
```

Hence the first error is at most `delta+eta`, and
`tau_m(b-b^2)<2delta+eta`. Let `eta` tend to zero and then `delta` decrease
to `Delta_A(f)`.

Compactness is used on the continuous functions `tau_m(g_k(a)^2)`, not on
the generally discontinuous rank function. In particular, this argument
does not make the invalid claim that arbitrary ranks have uniform spectral
cutoffs.

## 2. Exact finite-stage criterion

Suppose

```text
A_1 -> A_2 -> ... -> A
```

is an injective unital inductive system of separable unital subhomogeneous
C*-algebras, with simple non-elementary limit `A` and nonempty `T(A)`.
Write `phi_nj:A_n->A_j` for the connecting maps. The following assertions
are equivalent.

1. All continuous strictly positive affine functions on `T(A)` are uniform
   limits of rank functions from `M_infty(A)_+`.
2. For every `n`, `h in (A_n)_+`, and `epsilon>0`, there are `j>=n`, `m>=1`,
   and `0<=b<=1` in `M_m(A_j)` such that for **every** irreducible
   representation `pi:A_j->M_d(C)`, writing
   `B=pi^(m)(b)` and `H=pi(phi_nj(h))`,

   ```text
   |Tr_(md)(B)-Tr_d(H)| < epsilon d,
   Tr_(md)(B-B^2)       < epsilon d.                             (2)
   ```

The denominator is `d`, not `md`: matrix stabilization creates additional
unnormalized rank and does not itself divide ranks.

### Removing traces which do not extend to the limit

We first prove the compactness fact needed for (1) => (2). For a fixed stage
`k`, put

```text
K_kj = {rho composed with phi_kj : rho in T(A_j)},
K_k  = {tau restricted to A_k : tau in T(A)}.
```

The sets `K_kj` are nonempty compact and decrease with `j`, and

```text
K_k = intersection_{j>=k} K_kj.                                  (3)
```

One inclusion is immediate. For the other, if `rho` belongs to every
`K_kj`, the conditions specifying compatible traces on finitely many stages
and prescribing `rho` at stage `k` are simultaneously satisfiable: choose
a trace at the largest involved stage extending `rho`, then restrict it.
Compactness of the product of the trace spaces gives a compatible family
at all stages. This defines a trace on `A`.

Consequently, if a continuous real function `F` on `T(A_k)` satisfies
`F<epsilon` on `K_k`, then `F<epsilon` on some `K_kj`. Otherwise the nested
nonempty compact sets `K_kj intersection {F>=epsilon}` would have a point
in their intersection, contradicting (3).

### Proof that rank density gives (2)

For `h=0`, take `b=0`. If `h!=0`, injectivity and simplicity imply that its
image in `A` has strictly positive value at every trace. Thus
`f(tau)=tau(h)` is continuous strictly positive affine. By Section 1 and
rank density, choose a positive contraction `c in M_m(A)` whose first-moment
error and quadratic defect are both less than `epsilon/4` on `T(A)`.

Approximate `c` in norm by a positive contraction `b in M_m(A_k)`, for some
`k>=n`. Positive contractions in the union of the stages are norm dense;
this follows by self-adjoint approximation and scalar clipping to `[0,1]`.
If `||b-c||<r`, then

```text
|tau_m(b)-tau_m(c)| <= mr,
|tau_m(b-b^2)-tau_m(c-c^2)| <= 3mr.                               (4)
```

The matrix size `m` is now fixed, so choose `r` sufficiently small. The two
errors for `b` are then less than `epsilon/2` on `K_k`. Both errors are
continuous functions of the trace on `A_k`. Applying (3) to their maximum
gives a later `j` where the pushed-forward `b` satisfies the two inequalities
with tolerance `epsilon` for every trace on `A_j`.

Extreme tracial states on a subhomogeneous algebra are exactly normalized
matrix traces of irreducible representations. The displayed inequalities
therefore imply (2).

### Proof that (2) gives rank density

First, (2) holds for every trace on `A_j`: the two signed first-moment
inequalities and the defect inequality are continuous affine inequalities,
and hold on all extreme traces. Restricting a trace of `A` to `A_j` then
shows `E_A(tau->tau(h))=0`. Section 1 gives
`Delta_A(tau->tau(h))=0` for every positive stage element `h`.

Continuous strictly positive affine functions on the trace space of a
simple unital inductive limit are uniformly approximable by functions
`tau->tau(h)` with positive `h` in a stage. This is Proposition 5.1 of
Brown--Perera--Toms, whose argument uses positive affine evaluation and
density of the union, not homogeneous building blocks. Applying it to the
chosen `f`, and then applying (2) with a smaller tolerance, gives
`Delta_A(f)=0` by the triangle inequality.

Every unital separable ASH algebra has an injective unital subhomogeneous
presentation: take the images of its stages in the limit and adjoin the
limit unit when necessary. Images, quotients, and unitizations of
subhomogeneous algebras are subhomogeneous. Therefore proving (2) for all
systems in this section is equivalent to STW XXIV.

## 3. The exact negative certificate

Failure of STW XXIV is equivalent to the existence of a system as above,
a stage `n`, `h in (A_n)_+`, and `epsilon_0>0` such that:

```text
for every j>=n, every m>=1, and every positive contraction b in M_m(A_j),
there is an irreducible pi:A_j->M_d(C) for which

max{ |Tr_(md)(pi^(m)(b))-Tr_d(pi(phi_nj(h)))|,
     Tr_(md)(pi^(m)(b)-pi^(m)(b)^2) } >= epsilon_0 d.              (5)
```

This is the literal negation of (2), with all quantifiers retained. The bad
fibre may depend on `b`, on the stage, and on its matrix size. A proof must
control the whole later system. The original topological attachment
constraints remain in the requirement that `b` is one element of the
subhomogeneous algebra, rather than an unrelated selection in each fibre.

For a strict-comparison candidate, (5) is necessary for a counterexample to
Toms--Winter within ASH: rank density plus strict comparison gives purity,
and Winter's locally-finite-nuclear-dimension theorem gives Z-stability.
Those implications are already in the established Cairn rank-density
claims. Formula (5) does not itself produce such a candidate.

## 4. Why finitely many extreme limit traces cannot certify the gap

Let `A` be simple, unital, infinite dimensional with nonempty trace space,
and choose distinct extremal traces `tau_1,...,tau_s`. For any nonnegative
numbers `r_1,...,r_s` and any `epsilon>0`, there is `m>=1` and a positive
contraction `b in M_m(A)` such that, for every `i`,

```text
|tau_i,m(b)-r_i| < epsilon,
tau_i,m(b-b^2)  < epsilon.                                      (6)
```

**Proof.** Each extremal GNS von Neumann algebra `M_i` is a finite factor.
It is diffuse: a type I finite factor would yield a faithful finite
dimensional representation of the simple infinite dimensional `A`.
Distinct extremal tracial GNS representations are disjoint, so their direct
sum generates `M_1 direct_sum ... direct_sum M_s`. To see the disjointness,
nonzero normal intertwining of factorial representations would make them
quasi-equivalent; their normal tracial states would then agree by uniqueness
of the normalized trace on a finite factor, contrary to distinctness.

Choose an integer `m>=max_i r_i`. The diffuse finite factor `M_m(M_i)` has a
projection `p_i` with unnormalized trace `r_i`. Let `p=(p_i)_i` in the finite
direct sum. Kaplansky density gives positive contractions from `M_m(A)`
converging strongly to `p`, hence in every `tau_i,m` 2-norm. Writing one such
contraction as `b`, Cauchy--Schwarz gives

```text
|tau_i,m(b)-r_i| <= sqrt(m) ||b-p_i||_(2,tau_i,m),
|tau_i,m(b^2)-r_i| <= 2 sqrt(m) ||b-p_i||_(2,tau_i,m).
```

Thus the defect is at most three times the latter 2-norm scale, proving
(6). Section 1's spectral cut then also approximates all `r_i` by one
rank function.

The simplicity and infinite-dimensional hypotheses are essential here:
on `M_d(C)`, stabilization retains normalized rank increments `1/d`.
No assertion about a fixed finite-dimensional trace atom is being made.
Also, (6) concerns a finite chosen set of **extreme limit traces**, not all
traces of a building block and not the full infinite extreme boundary.

## 5. Status, source, and novelty audit

Repository searches on 2026-09-11 covered ASH rank density, recursive
subhomogeneous attachments, rank/variance formulations, tracial idempotents,
and finite-trace interpolation. Existing Cairn nodes already establish AH
rank density and rank-density-plus-comparison purity. None found records
(1), (2), or (5).

The current primary STW survey still poses XXIV and identifies it as the
ASH obstruction to the remaining Toms--Winter direction:
[Schafhauser--Tikuisis--White, 99 problems](https://arxiv.org/abs/2506.10902)
and the [authors' current PDF](https://mysite.science.uottawa.ca/atikuisis/STW.pdf).
The source facts consumed above are:

- [Brown--Perera--Toms, Proposition 5.1](https://arxiv.org/pdf/math/0609182):
  approximation of strictly positive continuous affine trace functions by
  positive stage-element evaluations. Their homogeneous rank construction
  is not imported into ASH.
- [Fu, Divisibility and Real Rank Zero](https://arxiv.org/html/2605.21655v1),
  Proposition 3.9, Definition 4.3 and Theorem 1.1, was checked as nearby prior
  art. It treats tracial oscillation, hereditary rank density, and tracial
  divisibility. None of those stronger hereditary or central conditions is
  inferred merely from the scalar quadratic feasibility in (1).
- [Carrión et al., Tracially complete C*-algebras](https://arxiv.org/abs/2310.20594)
  is nearby prior art for trace restriction along inductive limits and
  uniform tracial structures. The compactness argument (3) is supplied in
  full; no CPoU hypothesis or conclusion is used.

The elementary functional-calculus and compactness arguments are fully
proved here. They are not advertised as a new solution of an external open
problem, nor is priority over all existing reformulations asserted. The
maintained contribution is the explicit two-sided error estimate and its
all-stage, all-fibre certificate (5), wired to the existing XXIV target.
