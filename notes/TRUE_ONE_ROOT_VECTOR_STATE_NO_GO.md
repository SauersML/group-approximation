# One-root finite permutation models are universal

Date: 2026-08-11

## 1. Purpose

The irreducible domination formula invites the following maneuver: replace a
normalized trace with a single vector state by a Rayleigh-quotient argument,
then approximate that vector state by a finite-image representation.  This
note proves that the maneuver loses all information relevant to TRUE.

Every quotient of a finitely generated free group, with no soficity or
hyperlinearity assumption, has exact finite permutation models at one
distinguished root on every finite word window.  Soficity asks for the same
local behavior at almost every root.  Thus the missing datum is precisely
the normalized trace, or equivalently the ambient-rank density of good
roots.

## 2. Exact rooted completion

Let

`F=F(S)`, `q:F->Gamma=F/N`,                            `(OR1)`

where `S` is finite and `N` is normal.

**Theorem 1 (exact one-root finite model).**  For every finite `E subset F`
there are a finite `F`-set `X` and a point `x in X` such that

`g x=x  iff  g in N`                                  `(OR2)`

for every `g in E`.

**Proof.**  Choose `L` at least the maximum `S`-word length of an element of
`E`.  Let `V` be the radius-`L` ball around `1_Gamma` in the Cayley graph of
`Gamma`.

For each `s in S`, left multiplication defines a partial bijection

`T_s:D_s->R_s`, `v |-> s v`,                          `(OR3)`

where `D_s={v in V:s v in V}` and `R_s=sD_s`.  Since `T_s` is a bijection,
the complements `V-D_s` and `V-R_s` have the same cardinality.  Extend
`T_s` arbitrarily to a permutation `tilde T_s` of `V`.  Freeness of `F(S)`
makes the assignments `s |-> tilde T_s` a genuine action of `F` on the
finite set `X=V`.

Put `x=1_Gamma`.  If `g` has length at most `L`, every prefix of a reduced
word for `g`, read from `x`, stays in `V`.  Along that path the completed
permutations agree with Cayley multiplication.  Hence

`g x=q(g)`.                                            `(OR4)`

For `g in E`, equation `(OR2)` follows.  End proof.

Let `P_X` be the permutation representation on `ell^2(X)`.  The theorem is
equivalently the exact coefficient identity

`<P_X(g)delta_x,delta_x>=1_N(g)`                       `(OR5)`

on `E`.  Exhausting `F` by finite sets gives:

**Corollary 2.**  The normal indicator `1_N` is a pointwise limit of vector
coefficients of finite permutation representations of `F`, for every
normal subgroup `N`.

This is stronger than merely approximating `1_N` by finite-image unitary
vector states.  It is also elementary; property FD of free groups is not
needed.

## 3. The trace-to-vector Rayleigh reduction

The tempting reduction itself is valid.  Let `sigma:F->U(d)` and define

`D_g=(sigma(g)-1)^*(sigma(g)-1)/2`,                    `(OR6)`

so that

`tr_d(D_g)=1-Re tr_d(sigma(g))=:delta_sigma(g)`.       `(OR7)`

For a unit vector `v`, put

`e_v(g)=<D_gv,v>=1-Re<sigma(g)v,v>`.                  `(OR8)`

**Lemma 3 (Rayleigh selection).**  For finite `R subset F` and `w in F`,
there is a unit vector `v` such that

`e_v(w)/(sum_(r in R)e_v(r))`
` >= delta_sigma(w)/(sum_(r in R)delta_sigma(r))`,     `(OR9)`

with the evident infinite-ratio convention.

**Proof.**  Average the numerator and denominator of the vector quotient
over the unit sphere.  Their averages are respectively
`delta_sigma(w)` and `sum_R delta_sigma(r)`.  If every vector ratio were
strictly smaller than the ratio of these averages, integration would give
a contradiction.  The zero-denominator case follows by the same positive
operator argument.  End proof.

One can also apply the lemma to an expanding conjugacy window

`R_B={b r b^(-1):b in B,r in R}`.                     `(OR10)`

Trace invariance gives

`sum_(u in R_B)delta_sigma(u)=|B|sum_(r in R)delta_sigma(r)`. `(OR11)`

Thus an unbounded irreducible trace ratio can be converted, after choosing
`|B|` to grow sufficiently slowly, into a one-vector ratio on an expanding
normal-relator window.

## 4. Why the reduction is vacuous

Corollary 2 shows that the output class of the Rayleigh maneuver is
universal.  Even if `Gamma=F/N` is not hyperlinear, its regular coefficient
`1_N` already has exact finite permutation approximants at one root on
every finite window.

The distinction is the order of averaging.  A root coefficient is

`c_(X,x)(g)=1_{g x=x}`,                                `(OR12)`

whereas the permutation trace is

`c_X(g)=|{y in X:g y=y}|/|X|`
`     =(1/|X|)sum_(y in X)c_(X,y)(g)`.                `(OR13)`

Theorem 1 controls one summand of `(OR13)`.  Soficity requires the required
relations and separation at a set of roots of density tending to one.
Nothing in Rayleigh selection preserves that density.

Consequently the implication

`large normalized-trace ratio -> large vector-state ratio`              `(OR14)`

cannot be used as the decisive TRUE transfer: it discards normalized rank.
Any viable argument must retain at least one of the following equivalent
forms of macroscopic information:

1. a normalized trace throughout the rounding;
2. a corner whose rank is `1-o(1)` of the ambient dimension;
3. a finite rooted model in which the good-root set has density `1-o(1)`;
4. a common approximately invariant diagonal algebra with tracially large
   support.

This also pinpoints the limitation of property FD and Fell approximation in
the present problem.  Their vector-state conclusion lies on the one-root
side of `(OR13)`, while the hyperlinear-to-sofic question is exactly the
passage to the averaged side.

## 5. Outcome

The irreducible domination theorem remains useful only while its normalized
trace is preserved.  Selecting a high-energy vector is a mathematically
correct but information-destroying step.  The universal character-transfer
gate should therefore be formulated as a **tracial/macroscopic-rank**
rounding problem, not as finite-image approximation of individual matrix
coefficients.
