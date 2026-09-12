# Simultaneous MF radicals of finite Deligne covers

Date checked: 2026-09-07.

This proves a structural classification and a quantitative propagation
theorem. It does **not** prove the nontrivial triple-cover sector empty.
The unresolved choice is whether one-third belongs to the subgroup below.

## 1. The normalization and the approximation convention

Let `Gamma=Sp_4(Z)` and let

```text
1 -> Z<z> -> E_infinity -> Gamma -> 1
```

be the inverse image of the integral lattice in the universal cover of
`Sp_4(R)`. Choose a unital section `s` and define its integer cocycle by

```text
s(g)s(h)=z^b(g,h)s(gh).
```

Set `E_q=E_infinity/<z^q>` and write `z_q` for the image of `z`.
The covering kernel `K_q=<z_q>` has order `q`. It need not be the full
center: the central elements over `-I` also matter in representation theory,
but every element outside `K_q` is detected by the residually finite base.

Here `b` is the cocycle of this exact extension. The usual Meyer signature
cocycle has a factor of four relative to the free universal-cover class;
its mod-three use in older notes does not authorize replacing `b` by that
cocycle in a statement about **all** covering degrees. No explicit bounded
representative is needed for this argument.

Write `c_theta(g,h)=exp(2 pi i theta b(g,h))`. Let `P_op` be the set of
`theta in R/Z` admitting maps `U_n:Gamma->U(d_n)`, `d_n>=1`, such that
`U_n(e)=I` and

```text
||U_n(g)U_n(h)-c_theta(g,h)U_n(gh)||_op -> 0       (1)
```

for every fixed multiplication pair. These are pointwise operator-norm
models with no trace or separation condition. Equivalently the full
twisted group C-star algebra has a nonzero unital MF quotient, by the
universal-property and polar-lifting argument already used in
`deligne-maslov-opnorm-sector-is-mf-quotient`.

The group-MF convention is the repository's weak norm-corona convention:
an injective group homomorphism into the unitary group of a matrix corona.
No claim that the reduced twisted C-star algebra is MF is used.

## 2. A closed subgroup of scalar parameters

The identity scalar model gives `0 in P_op`. Tensor two sequences with
parameters `theta` and `phi`, pairing their coordinates after a common
enumeration. The new defect at each fixed pair is bounded by the sum of
the two old defects because all tensor factors are unitary. The new
parameter is `theta+phi`. Entrywise complex conjugation gives `-theta`.
Thus `P_op` is a subgroup.

To prove it closed, suppose `theta_n->theta` and each `theta_n` belongs
to `P_op`. Enumerate `Gamma^2`. For each `n`, choose one positive-dimensional
model at `theta_n` with error below `1/n` on the first `n` pairs. For each
fixed pair, `b(g,h)` is one fixed integer, so
`c_(theta_n)(g,h)->c_theta(g,h)`. The chosen models satisfy (1) at `theta`.
This is pointwise diagonalization, and does not require that the cocycle be
globally bounded or that the convergence be uniform over `Gamma^2`.

The metaplectic double cover `E_2` is residually finite. Choose a finite
quotient detecting `z_2`. In its left regular representation the negative
spectral space of `z_2` is nonzero and invariant. The section acts on that
space as an exact `c_(1/2)`-projective representation. Therefore
`1/2 in P_op`. This uses an actual exact representation, rather than an
implication from Connes embeddability to operator approximation.

Closed subgroups of the circle are either finite cyclic or the whole
circle. Hence

```text
P_op=R/Z, or P_op=(1/m)Z/Z for a positive even integer m.       (2)
```

## 3. Every visible finite central character is a scalar model

Fix `q`, and let `Theta:E_q->U(Q)` be any group homomorphism, where
`Q=prod_n M_(d_n)/direct_sum_n M_(d_n)` is the norm matrix corona.
Let `Z=Theta(z_q)`. Its spectral Fourier projections are

```text
P_j=(1/q) sum_(a=0)^(q-1) exp(-2 pi i ja/q) Z^a,
                j=0,...,q-1.
```

They sum to one, and centrality of `z_q` makes them commute with the entire
image. We claim that every `j` with `P_j!=0` satisfies `j/q in P_op`.

Here is the coordinate argument, including the positive-dimension issue.
Lift `Z` to unitaries `Z_n`. Since `Z^q=I`, the quantities
`||Z_n^q-I||` tend to zero. Round the spectra of `Z_n` to the nearest
`q`th roots of unity, changing them by `o(1)` in norm. Their exact Fourier
projections `P_(j,n)` lift `P_j` and form an orthogonal decomposition of
every coordinate. If `P_j!=0`, infinitely many of these projections have
positive rank; restrict to those coordinates.

Lift each `Theta(s(g))` to unitary matrices `V_(g,n)`. For each fixed `g`,
`[P_(j,n),V_(g,n)]->0` in norm. On the nonzero corner set

```text
A_(g,n)=P_(j,n)V_(g,n)P_(j,n).
```

The two unitarity defects of this compression tend to zero in the corner
norm, because the omitted off-diagonal blocks tend to zero. Consequently
polar decomposition changes `A_(g,n)` by `o(1)` to a corner unitary
`U_(g,n)`. This conclusion has no rank-dependent constant.

The section multiplication law in the corona lifts to

```text
V_(g,n)V_(h,n)-Z_n^b(g,h)V_(gh,n) -> 0.
```

Compressing, the omitted cross-corner term tends to zero, while `Z_n`
acts on the corner as `exp(2 pi i j/q)`. Polar correction preserves the
vanishing defect. This gives (1) at `theta=j/q` in dimensions
`rank P_(j,n)>=1`, proving the claim.

Conversely, suppose `theta=j/q in P_op`. Represent every element of
`E_q` uniquely as `z_q^a s(g)`, with `a mod q`. Then

```text
z_q^a s(g) |-> [(exp(2 pi i a j/q)U_n(g))_n]              (3)
```

is a group homomorphism into a norm-matrix corona. The multiplication
law follows exactly from (1). Its central character is `j/q`.

Thus the scalar characters that can appear in any norm-corona model of
`E_q` are exactly

```text
S_q=P_op intersect ((1/q)Z/Z).                            (4)
```

## 4. The annihilator computes the full radical

Residual finiteness of `Gamma` implies
`Rad_MF(E_q) subset K_q`: compose a finite quotient of `Gamma` detecting
the image of a given element with `E_q->Gamma`. Every such finite
representation is also a matrix-corona representation.

For `z_q^a`, the spectral decomposition in Section 3 says that an arbitrary
corona model kills this element precisely when all its supported characters
have value one on it. Conversely (3) realizes every character in `S_q`.
It follows that

```text
Rad_MF(E_q)={z_q^a : exp(2 pi i a theta)=1 for all theta in S_q}. (5)
```

This is the full radical, not only its intersection with the covering
kernel, because all other elements were already separated by finite
quotients of the base.

Since `P_op` is a subgroup, `S_q` is a subgroup of the cyclic character
group. Its annihilator is trivial exactly when `S_q` is the whole group,
or equivalently when `1/q in P_op`. In this case (3) at `j=1` detects
every nonidentity element of `K_q`. Combine it by block direct sum with
a faithful norm-corona model of the residually finite base, pulled back
to `E_q`. The resulting model separates all of `E_q`.

No general quotient-closure assertion for MF groups is involved. The base
is independently residually finite, and block direct sum makes the two
separation roles explicit. We have proved

```text
E_q is MF iff 1/q in P_op.                               (6)
```

If the first alternative of (2) holds, every radical vanishes. In the finite
alternative, elementary arithmetic gives

```text
S_q=(1/gcd(q,m))Z/Z,
Rad_MF(E_q)=<z_q^gcd(q,m)>,
|Rad_MF(E_q)|=q/gcd(q,m),
E_q is MF iff q divides m.                              (7)
```

In particular **one non-MF finite cover forces all but finitely many
covering degrees to be non-MF**. MF covers of unbounded degree force the
full-circle case and hence every finite cover to be MF.

## 5. One gap bounds all possible MF degrees

Let `W subset Gamma^2` be a nonempty finite multiplication window. Let
`B=max_W |b(g,h)|`, and define `f_W(theta)` to be the infimum, over all
positive dimensions and all unitary tuples indexed by every element
`g,h,gh` with `(g,h) in W`, of

```text
max_((g,h) in W)
 ||U_g U_h-exp(2 pi i theta b(g,h))U_(gh)||_op.
```

For circle distance `dist`, the phase inequality gives

```text
|f_W(theta)-f_W(phi)| <= 2 pi B dist(theta,phi).           (8)
```

Indeed it gives this bound for the maximal defect of each fixed tuple,
uniformly in dimension; taking the infimum in both directions preserves
the bound. At every `theta in P_op`, `f_W(theta)=0`.

Suppose `f_W(theta_0)>=epsilon>0`. If `B=0`, the identity tuple contradicts
this hypothesis, so `B>0`. The subgroup cannot be the whole circle. In
the finite alternative choose `j/m` nearest `theta_0`. Its circle distance
is at most `1/(2m)` and its defect infimum is zero. Therefore (8) implies

```text
epsilon <= pi B/m,
m <= pi B/epsilon.                                      (9)
```

By (7), every MF cover degree divides `m`, giving

```text
E_q is MF ==> q <= pi B/epsilon.                         (10)
```

This excludes all sufficiently large degrees, including degrees coprime
to the denominator of an excluded rational parameter. It is stronger
than propagating an obstruction only to multiples of one degree.

Every absent parameter has a positive finite-window gap of this form:
otherwise a diagonal choice with error below `1/n` on the first `n`
multiplication pairs gives a point-norm model at that parameter. Include
`(e,e)` among the windows: since `b(e,e)=0`, its defect equals
`||U_e-I||`, so replacing `U_e` by `I` changes every fixed-pair defect
by `o(1)`. This supplies the normalization in (1). Thus
the bound is conditional on a genuine finite-window certificate, rather
than on a numerical local minimum in one fixed dimension.

## 6. The triple-cover endpoint and the remaining work

The desired exact radical of `E_3` is equivalent to `1/3 notin P_op`.
If that input is proved, (2) has finite even order `m` with `3` not dividing
`m`. Formula (7) then additionally gives for every `a>=1`

```text
Rad_MF(E_(3^a))=<z_(3^a)>,
Rad_MF(E_(2*3^a))=<z_(2*3^a)^2>.
```

No positive dimension-uniform gap at one-third was obtained in this
attack. The established results above organize and amplify a future gap;
the existing sector-emptiness claim remains an explicit prerequisite of
the route to the exact triple-cover target.

The classification is for the finite covers. It makes no claim that
`Rad_MF(E_infinity)=mZ`: an infinite-order central corona unitary need
not have finite spectrum, so the finite Fourier-corner argument does not
apply. Passing to a scalar fiber instead would introduce a quotient whose
MF property has not been justified.

## 7. External and repository audit

The repository already contains the tracial closed-subgroup theorem
`maslov-ce-parameter-set-is-a-closed-subgroup`, its hyperlinear all-cover
classification, and the single-cover norm-sector/MF-quotient equivalence.
The new claims are the simultaneous **operator-norm radicals** (5)--(7)
and the finite-window quantitative bound (9)--(10). No global novelty
claim is made from the limited literature search.

[Stover, *Residual finiteness and discrete subgroups of Lie groups*,
Theorem 1.5 and its following paragraph](https://arxiv.org/html/2407.07680v2)
records Deligne's finite residual as twice the cyclic covering kernel.
For example degree six therefore has a finite quotient detecting the
central order-two direction; dividing by the invisible order-three
subgroup gives the required metaplectic quotient. This agrees with the
existing `maslov-mod3-gap-is-metaplectic-base-degree-six-gap` input.

[Bachner--Dogon--Lubotzky, *On L1-approximation of groups*, introduction
and Proposition 1.6](https://arxiv.org/html/2508.17392v3) treats the general
non-MF question as open and proves the finite-normal norm-to-trace
implication under a hyperlinear-quotient hypothesis. It does not provide
the absent scalar parameter needed here.

[Dadarlat--Glebe, *Central Extensions and Almost Representations*,
Theorem 6.4](https://www.math.purdue.edu/~mdd/Webpapers/Central-extensions.pdf)
already uses nonzero MF quotients of small twisted full group algebras to
obstruct matricial stability. That result is consistent with the present
subgroup argument; it does not decide the Maslov norm-parameter subgroup.
The inspected paper gives no matrix witness or exhaustion certificate for
the one-third sector.

All arguments here are exact symbolic arguments. No local executable
code, build, optimization run, or MSI job was needed for their proof.
