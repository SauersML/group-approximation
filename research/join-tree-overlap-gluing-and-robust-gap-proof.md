---
rg: 2
id: join-tree-overlap-gluing-and-robust-gap-proof
kind: route
title: Glue acyclic context laws and locate the first contextual escape
target: join-tree-overlap-gadgets-have-no-contextual-escape
requires:
  - lcs-parity-gadgets-preserve-odd-dictator-affine-hull
  - odd-subset-relaxation-needs-local-extendability
---

## 1. Join-tree notation

For an edge `e=cd` put `R_e=X_c intersect X_d` and write
`r_(c,e):{+1,-1}^{X_c}->{+1,-1}^{R_e}` for restriction.  The running
intersection property says that if a variable occurs in two contexts then
it occurs in every context on the unique path between them.  Therefore a
tuple of context assignments agreeing on every tree edge glues to one
well-defined assignment on `union_c X_c`.

## 2. Exact probability gluing

We induct on `|V(T)|`.  The one-node case is immediate.  Let `l` be a
leaf, let `d` be its neighbor, and let `R=X_l intersect X_d`.  Delete
`l`.  By induction, the remaining context laws glue to a distribution
`p'` on assignments `y` over the remaining variables.  Its `R` marginal
is the common separator law `q`.

For a leaf assignment `s` and a remaining assignment `y`, set

```text
p(y,s)=p'(y) p_l(s)/q(r)
if y|_R=s|_R=r and q(r)>0,
p(y,s)=0 otherwise.                                    (JTP1)
```

When `q(r)=0`, both relevant marginals give that fiber mass zero, so the
second line loses no mass.  Summing `(JTP1)` over `s` recovers `p'(y)`;
summing over `y` recovers `p_l(s)`.  Thus `p` is a probability
distribution with all prescribed context marginals.  Its support consists
of edge-compatible tuples, hence of global assignments by the running
intersection property.  This proves exact gluing.

Now suppose the `p_c` are supported on the allowed sets `S_c`.  The glued
law is supported on global assignments whose every context restriction is
allowed.  A nonempty probability law has a support point, proving `(JTG1)`.

For an exact commuting-operator LCS model, the involutions in one equation
context commute and hence have a joint spectral PVM.  Applying the strategy
state gives `p_c`.  The exact parity relation makes every forbidden joint
eigenspace have zero weight.  On an overlap, the joint spectral projections
are the same polynomials in the literally shared involutions, so their
marginal laws agree.  Exact gluing therefore produces a scalar solution.

## 3. Quantitative coupling

We next prove `(JTG3)` without dividing by small separator weights.  Root
`T`.  For every oriented edge `c->d` choose a maximal coupling
`kappa_cd` of the two separator marginals.  Its mismatch probability is

```text
Pr[r_(c,cd) != r_(d,cd)]=delta_cd.                      (JTP2)
```

Generate a random tuple of context assignments down the tree.  Sample the
root from `p_root`.  Given the parent assignment, use the conditional law
of `kappa_cd` to sample the child's separator value, then use the
conditional law of `p_d` to sample the full child assignment.  Zero-mass
conditional fibers may be defined arbitrarily because they are never
visited.  Continue independently down the child branches conditional on
their parent assignments.

Induction down the tree shows that the marginal of every sampled context is
exactly `p_c` and that `(JTP2)` holds on every edge.  Let `Bad_c` be the
event that the context assignment is outside `S_c`, and let `Bad_cd` be
edge disagreement.  Then

```text
Pr[Bad_c]=eta_c,       Pr[Bad_cd]=delta_cd.              (JTP3)
```

If none of these bad events occurs, the running intersection property glues
the tuple to a global satisfying assignment.  When no such assignment
exists, their union has probability one.  The union bound gives

```text
1 <= sum_c eta_c + sum_cd delta_cd,                     (JTP4)
```

which is `(JTG3)`.  If a verifier assigns every displayed check weight at
least `w_min`, its expected loss is at least `w_min` times the right side
of `(JTP4)`, hence at least `w_min`.

## 4. Gluing odd subsets over `F_2`

For the algebraic statement, identify a subset of `S_c` with its incidence
vector `t_c in F_2^{S_c}`.  Its separator marginal is the pushforward

```text
(r_(c,e)* t_c)(rho)
 = sum_(s in S_c: s|R_e=rho) t_c(s) mod 2.              (JTP5)
```

First note that edgewise bi-extendability `(JTG4)` and the tree property
imply that every assignment in every `S_c` extends to at least one global
assignment: root at that assignment, choose a matching neighbor assignment
on each incident separator, and continue outward.  Choices in distinct
branches cannot conflict because any shared variable occurs along their
connecting path.

We again induct after removing a leaf `l`.  Let `Sol'` be the global
solutions on the remaining tree.  By induction there is
`u in F_2^{Sol'}` with context marginals `t_c`.  On the separator `R`,
the pushforward of `u` and that of `t_l` are the same vector `q`.

For each separator assignment `rho` define the fibers

```text
G_rho={y in Sol':y|R=rho},
L_rho={s in S_l:s|R=rho}.                               (JTP6)
```

Whenever either fiber occurs, bi-extendability and the preceding extension
observation make both nonempty.  We need a matrix
`M_rho in F_2^{G_rho times L_rho}` whose row sums are the coefficients
`u(y)` and whose column sums are `t_l(s)`.  Such a matrix exists exactly
when the total requested row and column sums agree.  Here both totals are
`q(rho)` by `(JTP5)`.

For completeness, choose anchors `y_0 in G_rho` and `s_0 in L_rho`.
Put `M(y,s_0)=u(y)` for `y!=y_0`,
`M(y_0,s)=t_l(s)` for `s!=s_0`, all other non-anchor entries zero, and
choose `M(y_0,s_0)` to give the last row sum.  Equality of the two totals
then gives the last column sum as well.

The pairs in `G_rho times L_rho` glue to global solutions.  Taking their
coefficients to be `M_rho` over all `rho` defines
`t in F_2^{Sol}`.  Its old-context marginals are those of `u` and its leaf
marginal is `t_l`.  This completes the induction.  Its augmentation equals
the augmentation of every marginal, so it is odd.

Let a local long-code character be

```text
chi_(t_c)(f)=product_(s:t_c(s)=1) f(s).                 (JTP7)
```

The constructed `t` says that a compatible family of these characters is
the restriction of the odd product of global dictator characters indexed
by `{x:t(x)=1}`.  Every parity equation true on every global dictator is
true on that odd product.  This gives a valid acyclic, bi-extendable repair
of the refuted unrestricted odd-subset argument.

## 5. Why a cycle is a real escape, but not yet a decoder

The Mermin--Peres square uses the six row and column contexts of a `3 by 3`
array.  Put the following two-qubit Pauli involutions in its cells:

```text
I tensor X,  X tensor I,  X tensor X
Z tensor I,  I tensor Z,  Z tensor Z
Z tensor X,  X tensor Z,  Y tensor Y.                  (JTP8)
```

Every row and column is commuting.  All three row products and the first
two column products are `+I`, while the last column product is `-I`.
Thus `(JTP8)` is an exact four-dimensional operator solution.  A scalar
solution is impossible: multiplying the six scalar parity equations counts
each cell twice on the left, giving `+1`, but the right sides multiply to
`-1`.

Each cell belongs to its row and its column, so the context-intersection
graph is `K_(3,3)`.  A join tree would have to contain all nine row-column
edges to connect the two occurrences of every cell, but a tree on six
vertices has only five edges.  This is precisely where the gluing proof is
blocked.

The example proves that cyclic sharing can destroy atomwise scalar
extendability while retaining a global perfect quantum model.  It does not
supply the desired Taller--Vidick repair: `(JTP8)` is already a fixed
finite-dimensional perfect model.  Tensoring or adjoining this disjoint
gadget to a source test therefore leaves an immediate finite-dimensional
perfect realization of the new part.  The live construction must make the
cyclic phase depend on the source's cross-context data and prove a
dimension-independent reverse decoder; incidence topology alone supplies
neither.
