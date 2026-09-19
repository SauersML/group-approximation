# Property (T) gives a uniform traciality gap for infinite induced orbits

Date: 2026-08-12

## 1. Outcome

The amenable coadjoint stabilizer in
`FALSE_AMENABLE_COADJOINT_FRAME_CHARACTER.md` produces an exact monomial
representation on one infinite homogeneous orbit. It does not produce
finite-rank tracial models of that representation. There is a quantitative
reason which is independent of amenability.

Let `H` have property `(T)`, let `A<H` have infinite index, and let

`lambda_(H/A):H->U(ell^2(H/A))`                         `(CIT1)`

be the quasi-regular representation. If `(S,kappa)` is a Kazhdan pair for
`H`, then every positive trace-class operator `rho` of trace one satisfies

`max_(s in S)`
` ||lambda(s)sqrt(rho)-sqrt(rho)lambda(s)||_(HS)>=kappa.` `(CIT2)`

Thus no sequence of finite-rank density matrices can satisfy the
approximate-traciality hypothesis used by tracial rounding arguments. In
particular, direct finite-rank compression of the exact coadjoint-induced
representation has a dimension-independent defect floor.

This closes a tempting shortcut, but not the live FALSE route. Arbitrary
matrix microstates of the generated C-star algebra need not be spatial
compressions of the displayed infinite representation. More importantly,
the paired orbit-chart construction deliberately uses two root-dependent
matrix fields which stay far from every honest finite-dimensional covariant
pair. That nonliftable relative holonomy remains the exact open gate.

## 2. The Hilbert--Schmidt commutant is zero

Put `X=H/A` and let `lambda=lambda_X`. The group `H` acts transitively on
the infinite set `X`.

**Lemma 1.** The only Hilbert--Schmidt operator on `ell^2(X)` commuting
with `lambda(H)` is zero.

**Proof.** If `T lambda(h)=lambda(h)T`, then transitivity gives

`||T delta_(hx)||=||lambda(h)T delta_x||=||T delta_x||` `(CIT3)`

for all `h in H` and `x in X`. Hence the column norm `||T delta_x||` is
constant on `X`. But

`||T||_(HS)^2=sum_(x in X)||T delta_x||^2.`             `(CIT4)`

Since `X` is infinite, finiteness of `(CIT4)` forces the common column norm
to be zero. Thus `T=0`. End proof.

The same argument works for any infinite transitive permutation
representation; no information about the subgroup `A` is used beyond its
infinite index.

## 3. Quantitative Kazhdan gap

Let `HS(ell^2(X))` be the Hilbert space of Hilbert--Schmidt operators. The
formula

`sigma(h)T=lambda(h)Tlambda(h)^(-1)`                   `(CIT5)`

defines a unitary representation of `H`. By Lemma 1 it has no nonzero
invariant vector.

Fix the convention that `(S,kappa)` is a Kazhdan pair when every unitary
representation with a unit vector `xi` satisfying

`max_(s in S)||pi(s)xi-xi||<kappa`                     `(CIT6)`

has a nonzero invariant vector.

**Theorem 2 (quasi-regular traciality gap).** For every positive
trace-class `rho` with `Tr(rho)=1`, inequality `(CIT2)` holds.

**Proof.** The operator `T=sqrt(rho)` is a unit vector in the Hilbert space
of Hilbert--Schmidt operators. Moreover,

`||sigma(s)T-T||_(HS)`
` =||lambda(s)sqrt(rho)-sqrt(rho)lambda(s)||_(HS).`     `(CIT7)`

If all quantities in `(CIT7)` were smaller than `kappa`, property `(T)`
and `(CIT6)` would give a nonzero invariant Hilbert--Schmidt operator,
contrary to Lemma 1. End proof.

For a rank-`d` projection `P`, take `rho=P/d`. Then `(CIT2)` becomes

`max_(s in S) ||lambda(s)P-P lambda(s)||_(HS)/sqrt(d)`
` >=kappa.`                                             `(CIT8)`

Thus even after normalizing by the compression dimension, one Kazhdan
generator has order-one boundary.

## 4. Application to the framed coadjoint character

Retain the split form

`G=K semidirect H`,
`H=E_4(Z[Lambda]) semidirect SL_3(Z)`                  `(CIT9)`

and the irrational framed character `chi_theta` from
`FALSE_AMENABLE_COADJOINT_FRAME_CHARACTER.md`. Its stabilizer satisfies

`H_chi <= {+-I_4} times Stab_(SL_3(Z))(v)`,
`Stab_(SL_3(Z))(v)~=Z^2.`                              `(CIT10)`

The group `H` has property `(T)` and is nonamenable. Since `H_chi` is
amenable, it cannot have finite index in `H`; otherwise `H` would be a
finite extension of an amenable group. Hence `H/H_chi` is infinite.

The induced monomial representation

`Pi_theta=Ind_(K semidirect H_chi)^G(chi_theta)`        `(CIT11)`

restricts on `H` to `lambda_(H/H_chi)`. Theorem 2 therefore gives

`max_(s in S)`
` ||Pi_theta(s)sqrt(rho)-sqrt(rho)Pi_theta(s)||_(HS)`
` >=kappa`                                              `(CIT12)`

for every trace-one density operator `rho` on its representation space.

This has two immediate consequences.

1. The exact induced representation cannot be fed directly into a
   Paddock-type tracial rounding theorem by choosing increasingly large
   finite-rank density matrices.
2. Soficity of the action `H curvearrowright H/H_chi` supplies
   root-dependent finite Schreier charts, but those charts cannot be glued
   into finite-rank compressions of one global orbit representation with
   vanishing tracial boundary.

The second point is the normalized-trace version of the distinction in
`FALSE_AMENABLE_STABILIZER_ORBIT_CHART_INDUCTION.md`: a root-dependent
local chart is not a global principal bundle with one equivariant
transversal.

## 5. Exact computational consequence

A finite computation which freezes one large compression of `(CIT11)` and
optimizes only its boundary is guaranteed to see a positive floor at one
of the fixed Kazhdan generators. Scaling that experiment cannot prove
FALSE.

The first informative finite system must instead contain **two** external
transition fields and their relative holonomy. It must test whether

1. each field has vanishing fixed-window covariance defect;
2. the two fields agree on the positive tangent/elementary window; and
3. their marked relative character energy stays positive.

Equivalently, the finite variables must be those in
`FALSE_EQUIVARIANT_FIBER_FUNCTOR_STABILIZER_REDUCTION.md` and
`FALSE_POSITIVE_COMMUTANT_CHARACTER_MATCHING.md`, including the sparse
kernel-carry consistency equations. A single orbit character or a single
Schreier transversal omits the load-bearing variable.

## 6. Scope

Theorem 2 is a general property-`(T)` fact, not a proof that the generated
C-star algebra is non-MF. MF microstates are abstract approximately
multiplicative maps and need not arise from finite-rank compressions of a
chosen faithful representation. Nor does `(CIT12)` rule out the paired
nonliftable maps required for FALSE: those maps intentionally evade exact
external covariance and are quantitatively far from honest covariant
representations.

What the theorem does prove is that the amenable coadjoint orbit solves
only the algebraic and rooted-Schreier parts of the construction. Positive
normalized-trace amplification must come from genuinely paired relative
holonomy, not from repeating or compressing the exact induced orbit.

## 7. Literature scope

The general equivalence between finite-rank Folner sequences and amenable
traces is standard operator-algebraic background; see Ara--Lledo and the
survey of Lledo--Yakubovich. Bekka--Kalantar treat spectral-gap rigidity for
quasi-regular and, more generally, induced representations. The contribution
of this note is not a novelty claim for that background. It records the
one-line quantitative Kazhdan estimate `(CIT2)` in exactly the density-matrix
normalization needed by the framed FALSE construction and uses it to remove
a concrete, otherwise tempting amplification experiment.

## References

Pere Ara and Fernando Lledo, *Amenable traces and Folner C-star algebras*,
J. Funct. Anal. 264 (2013), 1797--1814; arXiv:1206.1488.

Bachir Bekka and Mehrdad Kalantar, *Quasi-regular representations of
discrete groups and associated C-star algebras*, Trans. Amer. Math. Soc. 373
(2020), 2105--2133; arXiv:1903.00202.

Fernando Lledo and Dmitry Yakubovich, *Folner sequences in operator theory
and operator algebras*, Rev. Math. Phys. 26 (2014), 1430002;
arXiv:1303.3392.
