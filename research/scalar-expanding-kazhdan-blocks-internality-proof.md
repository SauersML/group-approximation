---
rg: 2
id: scalar-expanding-kazhdan-blocks-internality-proof
kind: route
title: "Bound rectangular intertwiners, align expanding blocks, and recover the full commutant"
target: scalar-expanding-kazhdan-blocks-give-internality
requires: []
artifacts:
  - research/artifacts/liu-internality-normalization-audit-2026-09-20.md
  - research/artifacts/liu-section-six-acceptance-and-thom-bypass-2026-09-20.md
---

## Attribution and precise assertion

This is a checked exposition of Jihao Liu,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Lemma 6.4 and Proposition 6.5. It proves the target's
conditional assertion from its supplied fixed-gap block decomposition.
It does not assert that such decompositions exist for arbitrary models.
The later normalization/double mechanism is due to Andreas Thom,
[Theorems 1.2-1.3](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
and the concrete pair/lamp construction to Gabor Kun and Andreas Thom,
[Theorems A and E](https://arxiv.org/abs/2608.06222); neither is used here.

Write `H=<s_1,...,s_h>`, `u_j,n` for the supplied lifts, and `v_j,n`
for the nearby reducing tuple. One can append inverses to the list, with
inverse lifts, if needed; this preserves the scalar-gap inequality and
vanishing perturbation. For the trivial group use the identity list.
Energy has normalization `1/(4h)`. Decrease the fixed gap `c` to lie in
`(0,1)`.

## Bounded matching lemma

Consider two scalar-gap-`c` tuples `U_n,V_n` of ranks `r_n,t_n` whose
relators tend to zero in each block's normalized trace. Define

```text
lambda(U,V)=min_(Z!=0) sum_j ||U_j Z-Z V_j||_HS^2/(4h ||Z||_HS^2).
```

Let `Delta(U,V)` be the infimum of the Hilbert-Schmidt distance between
isometrically embedded tuples, including the identity as coordinate zero,
divided by `sqrt(r+t)`. The embeddings may be taken in dimension `r+t`,
so the minimum is attained. Direct compression and the identity coordinate
give

```text
|r-t|/(r+t) <= Delta^2,
lambda <= Delta^2/(2h(1-Delta^2))              when Delta<1,
Delta(U,Y) <= sqrt((r+t)/(r+b)) Delta(U,V)
               + sqrt((t+b)/(r+b)) Delta(V,Y),
```

where `b` is the rank of `Y`. For the second inequality use
`Z=iota* jmath`, whose squared HS norm is at least
`(1-Delta^2)(r+t)/2`. For the third, align the two middle embeddings and
use the ordinary triangle inequality before dividing by `sqrt(r+b)`.

Choose a Kazhdan displacement constant `kappa>0` for the list. In every
unitary representation its orthogonal complement to invariant vectors has
energy at least `a=kappa^2/(4h)`. This follows from the defining Kazhdan
inequality: at least one generator displaces any vector in that complement
by `kappa` times its norm. Apply it to conjugation on any finite tracial
algebra; its invariant subspace is the L2-space of the commutant. Averaging
bounded elements, then using density, identifies that subspace.

Take a fixed `lambda_0>0` so small that

```text
sqrt(lambda_0)/c < 1/4,
(sqrt(lambda_0)+sqrt(2/c)lambda_0^(1/4))^2 < a/16.
```

We prove that `lambda(U_n,V_n)<=lambda_0` forces `Delta(U_n,V_n)->0`.
Interchange the tuples coordinatewise to have `r>=t`. Normalize a
minimizing rectangular matrix by `Tr(ZZ*)=r`; put `b=(ZZ*)^(1/2)` and
`m=tr_r(b)`. Trace Cauchy-Schwarz applied to the difference of products,
followed by Powers-Stormer, yields

```text
energy_U(b)<=sqrt(lambda),
1-m^2<=sqrt(lambda)/c=:delta,
m^2<=t/r,          ||b-I_r||_(2,r)^2=2(1-m)<=2delta.
```

The standard Powers-Stormer input is `||a-b||_2^2<=||a^2-b^2||_1` for
positive matrices, with the same trace; see Adrian Ioana,
[*Almost commuting matrices and stability for product groups*](https://ems.press/content/serial-article-files/51186),
JEMS 27 (2025), equation (2.1), printed p.4036. It applies before any
ultraproduct passage, so no bound on `||Z||_op` is needed.

Extend the polar part of `Z` to an isometry `J:C^t->C^r`. Its range
contains the support of `b`, and

```text
||Z-J||_HS^2/r <= 2delta,
[sum_j ||U_j J-J V_j||_HS^2/(4hr)]^(1/2)
  <= sqrt(lambda)+sqrt(2/c)lambda^(1/4).
```

The latter uses `||U_j(Z-J)-(Z-J)V_j||_HS<=2||Z-J||_HS`. The bounded
isometries, rather than the original `Z_n`, define a class `v` in
`prod_omega M_(r_n+t_n)`. The direct-sum tuples define a homomorphism by
the relator hypotheses. Let `D` be its commutant and `p,q` the summand
projections. Their traces stay bounded below, because `t/r>=1-delta`.
In particular `||v||_2^2>=3/8`, while the Kazhdan inequality gives
`||v-E_D(v)||_2<=1/4`. Hence `w=E_D(v)` is nonzero and lies in `pDq`.

The two scalar gaps show `pDp=Cp` and `qDq=Cq`: bounded corner lifts
have vanishing commutators in their own normalization, since their ambient
traces are bounded below, and the gaps make them scalar. Thus
`w*w=beta q`, `ww*=alpha p`; nonzero `w` implies `alpha=beta>0` and
equal traces imply `tau(p)=tau(q)`. Therefore `t_n/r_n->1`, and a scalar
multiple of `w` is a partial isometry from `q` onto `p` in `D`.

Lift it by rectangular contractions `X_n` and extend their polar parts to
isometries `W_n:C^(t_n)->C^(r_n)`. Since `X_n*X_n->I` and
`(1-s)^2<=(1-s^2)^2` on `[0,1]`, `||X_n-W_n||_HS/sqrt(r_n)->0`.
Thus the normalized intertwining errors of `W_n` vanish. Splitting the
domain at `W_n W_n*` gives

```text
||U_j-W V_j W*||_HS^2=||U_j W-W V_j||_HS^2+r-t.
```

Together with the identity coordinate and `t_n/r_n->1`, this proves
`Delta(U_n,V_n)->0`, completing the bounded matching lemma.

## Uniform block selection and exact multiplicities

The perturbed tuple still represents `pi`, by telescoping each fixed
word. Enumerate its relators `r_1,r_2,...`. Choose `k_n->_omega infinity`
slowly enough that the summed squared ambient errors of the first `k_n`
relators are at most `k_n^-4` on an ultrafilter-large set. Discard blocks
with one of these errors, in block normalization, greater than `k_n^-1`.
Their total relative rank is at most `k_n^-2`. Every fixed relator now
holds uniformly over retained blocks. The original discarded block still
has vanishing trace.

Let `epsilon_n` be the maximum `Delta` over retained pairs with
`lambda<=lambda_0`. It tends to zero: otherwise choosing maximizing
pairs on an ultrafilter-large set contradicts the bounded matching lemma.
Off that set use identical one-dimensional trivial tuples. This completion
has scalar gap vacuously and satisfies every relator.

Choose `rho<1/4` with `rho^2/(2h(1-rho^2))<lambda_0`. Declare two blocks
equivalent if `Delta<rho`. Related pairs have distance at most `epsilon_n`.
Their ranks are within a factor two, so the weighted triangle inequality
gives distance at most `4epsilon_n<rho` through a middle block. Hence this
is an equivalence relation eventually. Distinct classes have
`lambda>lambda_0`.

In each class choose a member of least rank `t` as representative. For a
member of rank `r>=t`, set `theta_n=epsilon_n+1/n`, choose embeddings with
squared tuple distance at most `4theta_n^2(r+t)`, and put `Z=iota*jmath`.
Then

```text
r-t <= 4theta_n^2(r+t),
Tr(I_t-Z*Z)<=2theta_n^2(r+t),
||W-Z||_HS^2<=2theta_n^2(r+t)
```

for an isometric polar extension `W`. Replace the member tuple by
`W V_j W*+(I-WW*)`. Compression, the triangle inequality, and the last
bound show that its summed squared change is at most
`(16+64h)theta_n^2 r`, and its discarded rank is at most
`8theta_n^2 r`. Sum these estimates by the original member ranks; their
sum is at most the ambient dimension, so there is no block-count factor.
Use identity on all discarded space.

Write `p_n` for the total kept projection and `w_j,n` for this tuple.
Then lost trace `chi_n=tr(1-p_n)` and total tuple error
`eta_n=(sum_j ||u_j,n-w_j,n||_2^2)^(1/2)` tend to zero. The isometries
`W_i` into different member spaces have orthogonal ranges, so `W_i W_j*`
are exact coherent matrix units. On the kept space,

```text
w_j,n=direct_sum_nu (I_(m_nu) tensor V_j^nu),
D_n=direct_sum_nu (M_(m_nu) tensor C I_(t_nu)).
```

Every rectangular sector between different classes has gap `lambda_0`.
Within one class, after the chosen identifications, the gap off its
scalar intertwiner is `c`. Squared norms and energies sum over these
orthogonal sectors, giving gap `gamma=min(c,lambda_0)` off `D_n`.

## Both commutant inclusions

Put `A_n=D_n+ C(1-p_n)`, omitting zero summands. For a contraction `x`,
compression costs at most `2sqrt(chi_n)`. The retained-sector gap yields

```text
||x-E_(A_n)(x)||_2 <= 2sqrt(chi_n)
  + ([sum_j ||[u_j,n,x]||_2^2]^(1/2)+2eta_n)/(2sqrt(h gamma)).
```

Also every contraction of `A_n` commutes with each `w_j,n` and hence has
original commutator-list norm at most `2eta_n`. The latter proves
`[A_n]_omega subset pi(H)' cap M`. Apply the former to any bounded lift
of any element of the commutant, rescaled to contractions; its conditional
expectations give a bounded lift in `A_n` of the same element. This is the
reverse inclusion. Complete the construction by scalar algebras on any
excluded ultrafilter-small index set. All final algebras are unital in
the original dimensions.

The proof establishes only the stated conditional fixed-gap assertion.
It neither supplies the block decomposition nor asserts the unconditional
analytic theorem of Liu's Section 5.
