# MF detection for infranormal Kazhdan subgroups

2026-09-13. Mathematical proof; the new extensions below have not been
formalized in Lean or checked by a repository build. The inputs are the
manuscript's finite-corona projection calculus and central-corner lemma.
No new non-MF example or priority claim is asserted.

The normality assumption in `thm:normal-kazhdan` can be replaced by
infranormality, even inside a subgroup of finite index. Finiteness already
turns one-sided conjugation of the Kazhdan projection into equality.
Normality supplies more than the corner argument needs.

## 1. Statement

All groups here are countable. Write

\[
 S(G)=\{g\in G:\|V_n(g)-I\|_{2,d_n}\longrightarrow0
       \text{ for every operator-norm asymptotic representation }(V_n)
       \text{ of }G\}.
\]

The models have unitary values, satisfy `V_n(1)=I`, and are asymptotically
multiplicative on every fixed pair. No separation is assumed. The norm is
normalized: `||A||_{2,d}^2=Tr(A* A)/d`. Both `S(G)` and `Rad_MF(G)` are
normal subgroups, and `Rad_MF(G) <= S(G)`: MF invisibility forces
operator-norm convergence to the identity in every model, hence HS
convergence. Products, inverses, and conjugation preserve HS convergence,
giving normality of `S(G)`.

For `K <= G` define

\[
 P_G(K)=\{g\in G:gKg^{-1}\le K\},\qquad
 H_G(K)=\langle P_G(K)\rangle.
\]

Here `P_G(K)` is the compression semigroup, and `K <= H_G(K)`.
The condition `H_G(K)=G` is called infranormality. This terminology is
from Kun--Thom, [*Nonsofic wreath products of residually finite groups*,
Introduction](https://arxiv.org/html/2608.06222v1#S1), checked 2026-09-13.
Their sofic results are not used below.

**Theorem.** Suppose `K` has property (T) and
`[G:H_G(K)] < infinity`. Then

\[
 \boxed{\quad K\le S(G)\quad\Longleftrightarrow\quad
 K\le\operatorname{Rad}_{\mathrm{MF}}(G).\quad}             \tag{1}
\]

In particular, if `L <= G` has property (T), `K <= D_G(L)` has property
(T), and `[G:H_G(K)]` is finite, every homomorphism from `G` to an MF
group kills `K`. A nontrivial such `K` certifies that `G` is not MF.

This includes normal `K`, infranormal `K`, and Kazhdan subgroups whose
normalizer has finite index. No property (T) assumption on `G` or
`H_G(K)` is needed. Equation (1) compares containment of the whole
subgroup; it does not assert equality of `K intersect S(G)` and
`K intersect Rad_MF(G)` element by element.

## 2. One-sided conjugation centralizes the projection

Let `B` be a finite unital C*-algebra, `rho:G -> U(B)` a homomorphism,
and `p` the image of the Kazhdan projection `e_K` under the induced map
`C*_max(K) -> B`. For `g in P_G(K)`, put `U=rho(g)`.
The manuscript's one-sided order lemma gives

\[
 U^*pU\le p.
\]

These projections are unitarily equivalent. Finiteness forces equality,
so `Up=pU`. The elements of `G` whose images commute with `p` form a
subgroup. Consequently

\[
 p\in\rho(H_G(K))'.                                      \tag{2}
\]

This comparison needs no faithful trace. If projections `a <= b` are
equivalent via `v` with `v*v=b`, `vv*=a`, then `v+(1-b)` is an isometry
with range projection `a+1-b`. Finiteness makes it unitary, hence `a=b`.
Norm matrix coronas are finite by unitary lifting and polar correction,
as in `lem:stable-finite` of the manuscript.

When `H_G(K)=G`, (2) gives exactly the centrality needed to compress an
ambient model. The group `K` need not be normal.

## 3. A finite detector after taking the corner

Suppose `H_G(K)=G`, and let `Theta:G -> U(Q_d)` be a corona homomorphism
nontrivial on `K`. Its Kazhdan projection image `p` commutes with
`Theta(G)` by (2). Also `p != 1`, since `Theta(k)p=p` for every `k in K`.
Thus `q=1-p` is a nonzero commuting projection. The central-corner lemma
produces an operator-norm asymptotic representation

\[
 W_n:G\longrightarrow U(r_n)
\]

representing `g -> q Theta(g)` in the corner corona, after retaining
coordinates where the projection lift is nonzero. The ranks `r_n` are
positive, with no lower bound on `r_n/d_n`. For the induced map
`pi:C*_max(K) -> Q_r`,

\[
 \pi(e_K)=0.                                               \tag{3}
\]

Choose a finite probability average

\[
 a=\sum_{k\in F}\mu(k)u_k,\qquad \mu(k)\ge0,\qquad
 \sum_{k\in F}\mu(k)=1,\qquad \|a-e_K\|<1/8.                \tag{4}
\]

The set `F` and weights depend only on `K`, not on `Theta`. This averaging
fact is already recorded in `kazhdan-projection-is-norm-limit-of-finite-averages`;
it is not new here. A construction from a Kazhdan pair appears below.

Set `A_n=sum_{k in F} mu(k) W_n(k)`. Its corona class is `pi(a)`, so

\[
 \limsup_n\|A_n\|=\|\pi(a)\|<1/8.
\]

Eventually `||A_n|| < 1/4`. Unitarity gives the exact identity

\[
 \begin{aligned}
 \sum_{k\in F}\mu(k)\|W_n(k)-I\|_{2,r_n}^{2}
 &=2-2\operatorname{Re}\operatorname{tr}_{r_n}(A_n)\\
 &\ge 2-2\|A_n\|>3/2.
 \end{aligned}                                             \tag{5}
\]

Hence, eventually,

\[
 \max_{k\in F}\|W_n(k)-I\|_{2,r_n}>\sqrt{3/2}>1.            \tag{6}
\]

If `K <= S(G)`, its defining hypothesis applies to the new models `W_n`,
making every term in this finite maximum tend to zero. This contradicts
(6) and proves (1) for infranormal `K`.

Equation (6) is useful independently: every corona map nontrivial on an
infranormal Kazhdan subgroup has a corner model with a fixed finite set
carrying a uniform positive normalized-HS signal. It does not assert that
the signal occupies a positive fraction of the original matrix.

**Construction in (4).** For nontrivial `K`, fix a nonempty finite symmetric
generating Kazhdan set `T` and `kappa>0` such that, on the orthogonal
complement of invariant vectors, `max_{t in T} ||rho(t)xi-xi|| >= kappa ||xi||`
in every unitary representation. Put `s=|T|` and

\[
 b=\tfrac12 1+\frac1{2s}\sum_{t\in T}u_t,
 \qquad \eta=\frac{\kappa^2}{4s}.
\]

In every representation `b` is a positive contraction, and

\[
 \langle(1-\rho(b))\xi,\xi\rangle
 =\frac1{4s}\sum_{t\in T}\|\rho(t)\xi-\xi\|^2
 \ge\eta\|\xi\|^2
\]

on that complement. Therefore `||b^j-e_K|| <= (1-eta)^j`.
Choose a positive integer `j` with `(1-eta)^j < 1/8` and set `a=b^j`.
This is a probability average supported in the word ball of radius `j`.
The trivial subgroup case needs no detector.

## 4. Finite-index heredity of the shadow

**Lemma.** For every finite-index subgroup `H <= G`, identifying
subgroups through inclusion,

\[
 S(H)=H\cap S(G).                                          \tag{7}
\]

Left-to-right follows by restricting models of `G`. Conversely, start
with any operator-norm asymptotic representation `V_n:H -> U(d_n)`.
Put `m=[G:H]`, choose left-coset representatives `t_1=1,t_2,...,t_m`, and
write

\[
 gt_i=t_{\sigma_g(i)}c(g,i),\qquad c(g,i)\in H.
\]

Define unitary block-permutation matrices by

\[
 \widetilde V_n(g)(e_i\otimes v)
 =e_{\sigma_g(i)}\otimes V_n(c(g,i))v.
\]

The exact cocycle identity
`c(gh,i)=c(g,sigma_h(i))c(h,i)` gives

\[
 \|\widetilde V_n(gh)-\widetilde V_n(g)\widetilde V_n(h)\|
 =\max_{1\le i\le m}
 \|V_n(c(gh,i))-V_n(c(g,\sigma_h(i)))V_n(c(h,i))\|
 \longrightarrow0.                                       \tag{8}
\]

Thus these are models of `G`. If `h in H`, its action fixes the first
coset, with first diagonal block exactly `V_n(h)`. Consequently

\[
 \|\widetilde V_n(h)-I\|_{2,md_n}^{2}
 \ge\frac1m\|V_n(h)-I\|_{2,d_n}^{2}.                        \tag{9}
\]

For `h in H intersect S(G)`, the left side tends to zero, hence so does
the right side for every choice of `V_n`. This proves (7). No normality
or property (T) is used.

The same construction gives the familiar finite-index identity for
`Rad_MF`, since the distinguished block gives
`||tilde V_n(h)-I|| >= ||V_n(h)-I||`. That radical identity is already
recorded in `corona-finite-index-radical-heredity`. The additional statement
here is (7), which retains the fixed normalization factor `1/m`.

## 5. Finish the generalization

Take `H=H_G(K)` of finite index. Every compressor of `K` in `G` already
lies in `H`, so `P_H(K)=P_G(K)` and `K` is infranormal in `H`.
If `K <= S(G)`, (7) gives `K <= S(H)`. Section 3 gives
`K <= Rad_MF(H)`, and restriction of MF homomorphisms from `G` gives
`K <= Rad_MF(G)`. This proves (1).

Quantitatively, restrict a corona map to `H`, take the corner models in
Section 3, and induce them back to `G`. Equations (6) and (9) give

\[
 \max_{k\in F}\|\widetilde W_n(k)-I\|_{2,mr_n}>1/\sqrt m
\]

eventually. These induced models need not represent the original corona
map. The universal quantifier in `S(G)` permits their use.

For the compression application, the manuscript's `cor:defect-hs` says
`D_G(L) <= S(G)` for property-(T) subgroups `L`. Apply (1) to `K` inside
this defect. The same conclusion holds if the defect is replaced by the
subgroup generated by any family of such defects, since `S(G)` is a
subgroup.

The weaker hypothesis is not equivalent to normality. For the manuscript's
affine base `K=Z^3 semidirect SL_3(Z)` and its ascending HNN extension
along `(v,A) -> (2v,A)`, the stable letter strictly compresses `K`.
The extension is generated by `K` and that letter, so `K` is infranormal
and not normal. This illustrates the distinction between the hypotheses;
the affine HNN group itself is residually finite, and its nontrivial `K`
does not satisfy `K <= S(G)`.

## 6. Scope and an associated correction

The analytic requirement is that the Kazhdan projection commute with the
ambient corona image. Infranormality guarantees it by finite projection
comparison. This does not remove property (T) of `K` or justify arbitrary
infinite-index restriction of the shadow. The finite-average simplification
was already established in `normal-kazhdan-via-finite-average-corner`;
the new conclusions here are the infranormal upgrade, its finite-index
extension, and (7).

The same comparison corrects a sentence in
`strict-compressor-kazhdan-radical-is-tracially-zero`. If `p <= q=tpt*`
are strict-compressor Kazhdan projections in a maximal group C*-algebra,
every homomorphism into a finite unital C*-algebra kills `q-p`.
A norm matrix ultraproduct cannot retain `q-p`, even though it need not
have a faithful tracial state. Trace invisibility alone would not imply
this; the additional input is equivalence of the two ordered projections.

The external source above supplies terminology only. This is an extension
derived from the repository's existing proofs, with no claim that a
literature-wide novelty audit has been completed.
