# Finite-orbit return maps: the ordinary completely positive step is available

Date: 2026-09-05. This is an auxiliary construction for the Berend
decomposition-rank attack, not a solution or a new Cairn target. It
isolates a step which can actually be completed, rather than treating
all return-map construction as unknown.

## A finite-target replacement lemma

Let `A` be separable and unital, and let `q_n:A -> Q_n` be unital
quotient maps with decreasing kernels `I_n` and `intersection I_n=0`.
Then every cpc map `psi:A -> F` to a finite-dimensional C*-algebra can
be approximated in point norm by cpc maps of the form `psi_n q_n`,
where `psi_n:Q_n -> F`. If `psi` is unital, the `psi_n` can be unital.

Here is a proof avoiding an unproved uniform inverse estimate on a
finite-dimensional operator system. First fix `k`. The quotient maps
on `M_k(A)` have decreasing kernels with zero intersection. Their
diagonal map into `product M_k(Q_n)` is therefore an injective
homomorphism, so

`||q_n^(k)(b)|| increases to ||b||` for every `b in M_k(A)`.

Let `S_n` denote the state space of `M_k(Q_n)` pulled back to
`M_k(A)`. These are increasing convex sets. For every selfadjoint `b`,
their support functions satisfy

`sup_(rho in S_n) rho(b) -> sup_(rho in S(M_k(A))) rho(b)`.

Indeed choose `c>=||b||`, and apply the norm limit to the positive
element `b+c1`; its norm minus `c` is the maximum of the spectrum of
`b`. Hahn--Banach separation in the weak-* topology now shows that
`union S_n` is weak-* dense in `S(M_k(A))`. This is a convex-union
argument; it does not assert weak-* density of pure states.

Use the usual matrix-state correspondence for completely positive
maps `A -> M_k`: the functional corresponding to `psi` is

`omega_psi([a_ij])=sum_(i,j) <psi(a_ij)e_j,e_i>`.

It is positive, and a positive functional of this form determines a
completely positive map. For a unital `psi`, its norm is `k`.
Approximate `omega_psi/k` weak-* by states from `S_n`. The resulting
cp maps `eta_n:Q_n -> M_k` satisfy

`eta_n(q_n(a)) -> psi(a)`,  `eta_n(1) -> 1`.

For all sufficiently large `n` the second element is positive
invertible. Replace `eta_n` by

`psi_n(b)=eta_n(1)^(-1/2) eta_n(b) eta_n(1)^(-1/2)`.

These maps are unital completely positive and have the same point-norm
limit after composition with `q_n`. Separability permits a sequential
diagonal choice. If a larger index is needed, compose a previously
chosen map with the quotient `Q_n -> Q_j` for `n>=j`.

For a nonunital cpc map, apply the unital assertion to

`A direct_sum C -> M_k`,
`(a,lambda) -> psi(a)+lambda(1-psi(1))`,

and the quotient maps `q_n direct_sum id_C`, then restrict to the
first summand. Finally handle a finite direct sum of matrix targets
componentwise. This proves the lemma.

## Application to the Berend quotients

The established increasing finite-orbit quotients of the Berend algebra
meet the hypotheses. As a result, a prescribed finite-dimensional
approximation can always have its incoming map replaced by one
factoring through a sufficiently large finite-orbit quotient. The
return map from that finite-dimensional algebra is left unchanged.
In particular this replacement preserves its colour count and its
norm exactly.

Two consequences are available unconditionally:

1. Nuclearity gives ucp maps `sigma_n:Q_n -> A` such that
   `sigma_n q_n -> id_A` in point norm. To construct them, start with
   ucp finite-dimensional nuclear approximations `phi psi` of the
   identity and replace `psi` by `psi_n q_n` as above. Their compositions
   `phi psi_n` are ucp. Choose increasing indices and fill the gaps
   using the restriction maps between the quotients.
2. If `dim_nuc(A)<=d`, the same argument gives approximations
   `phi_n psi_n q_(j(n))` with the usual fixed `d+1` order-zero colours
   of `phi_n`; their total return norm is at most `d+1`. The incoming
   map `psi_n` is cpc and no extra colour is introduced.

Thus neither the existence of ordinary contractive return maps nor
the ability to impose finite-orbit factorization on the incoming map
is an additional hypothesis. What has not been constructed is one
family having both contractive total return and a fixed finite number
of order-zero colours.

The K-theory obstruction proved in
`research/artifacts/berend-k-theory-quotient-obstruction-2026-09-05.md`
is consistent with these return maps: the quotient-dependent unitary
witness forces maximal multiplicativity defect of `sigma_n`, whereas
`sigma_n q_n` becomes multiplicative on every fixed finite subset of
the source. These are distinct, precisely quantified conditions.

## A concrete unsuccessful construction

An exact equivariant lift of the diagonal of a nontrivial finite orbit
cannot be used as a building block. Suppose `F` is a finite invariant
set and `T:C(F) -> C(T^3)` is a positive equivariant map. Let
`Gamma_0` be the finite-index subgroup fixing every point of `F`.
Each `T(1_{x})` is a continuous `Gamma_0`-invariant function. The
restriction of a Berend unit action to this subgroup has a dense
orbit, so these functions are constant. Hence `T` has scalar range
and cannot split restriction when `|F|>1`.

This does not prevent the preceding ucp return maps: they need not
preserve the diagonal or be exactly equivariant. Nor does it obstruct
decomposition-rank approximations. It specifically rules out the
proposed construction which lifts whole finite-orbit diagonal and
stabilizer blocks exactly before doing the colour decomposition.

No claim of infinite or finite decomposition rank follows from this
note. The new usable step is the proved finite-target replacement
lemma and its resulting contractive return-map construction.

## Why commutation of the total return weight is insufficient

Write a nuclear-dimension approximation as `R=sum_i phi_i psi_i`,
where each `phi_i:F_i -> A` is cpc and order zero and each incoming
map is cpc. Put `h=sum_i phi_i(1)`. If `||R(1)-1||<=epsilon<1`, then
`h>=R(1)>=(1-epsilon)1`, so `h` is invertible.

Suppose even that `h` commutes exactly with every colour range. The
normalized maps `theta_i(x)=h^(-1/2)phi_i(x)h^(-1/2)` are then order
zero, and their sum is unital. But

`||sum_i theta_i psi_i(1)-h^(-1)||<=epsilon/(1-epsilon)`.

Thus this normalization recovers the source unit only if `h` is itself
close to one. It does not solve the contractivity problem merely by
preserving order zero. A completely exact example with both colours
active is `A=F_0=F_1=C`, `phi_0=phi_1=id`,
`psi_0=psi_1=(1/2)id`. Here `R=id` and `h=2`; the normalized composite
is `(1/2)id`.

The missing operation is a compensating redistribution of the incoming
weights. The following is a quantitative sufficient condition for doing
that operation without any perturbation of order-zero relations.

## Exact redistribution when the incoming weights are near the centers

Let `a_i=psi_i(1)`, and suppose positive central contractions
`b_i in Z(F_i)` satisfy `||a_i-b_i||<=delta_i`. Put
`c_i=b_i+delta_i 1`; when necessary use `delta_i+eta` and let the
arbitrarily small positive `eta` tend to zero in the estimates below.
Then `c_i` is central, positive invertible and `a_i<=c_i`. Define

`psi_i'(x)=c_i^(-1/2)psi_i(x)c_i^(-1/2)`,

`phi_i'(y)=phi_i(c_i y)`.

The incoming map is cpc because its value at one is at most one.
The outgoing map is completely positive and order zero because `c_i`
is central. There is an exact equality

`phi_i' psi_i'=phi_i psi_i`.

Moreover, `0<=c_i-a_i` and `||c_i-a_i||<=2delta_i`, so

`||sum_i phi_i'(1)||<=1+epsilon+2 sum_i delta_i`.

Dividing every `phi_i'` by this common upper bound makes the total
return contractive and leaves the colour count unchanged. If `R`
approximates the identity within `epsilon` on a finite set of
contractions, the new approximation error is at most

`2epsilon+2 sum_i delta_i`.

The bound is independent of matrix sizes. Hence finding nuclear-
dimension approximations whose incoming weights approach the centers
of their finite-dimensional targets is sufficient for the same finite
decomposition-rank bound. Near-projection weights are not necessary
for this particular redistribution.

One explicit way to test the hypothesis is to average `a_i` under the
unitary group of `F_i`: the average `b_i` is central and

`||a_i-b_i||<=sup_(u in U(F_i)) ||[a_i,u]||`.

Commutators only with images of fixed source elements are weaker than
this estimate. No uniform passage from those commutators to the full
unitary-group supremum has been proved for the Berend approximations.

## Spectral corner compression: the exact hypothesis and error bound

There is a second sufficient condition corresponding directly to
near-projection weights. Suppose `0<=delta<1-t<1` and every `a_i` has
spectrum in `[0,delta] union [1-t,1]`. Put

`p_i=1_[1-t,1](a_i)`,  `psi_i^p(x)=p_i psi_i(x)p_i`.

Restricting `phi_i` to `p_i F_i p_i` preserves order zero. Since
`p_i<=(1-t)^(-1)a_i`, the total return norm is at most
`(1+epsilon)/(1-t)`. Scale all return maps by
`lambda=(1-t)/(1+epsilon)` to obtain a contractive total return.

For a source contraction `x`, Stinespring's inequality gives

`||psi_i(x)-p_i psi_i(x)p_i||<=2 sqrt(delta)`.

For example, write `psi_i(x)=V_i^* pi_i(x)V_i`; the two discarded
corner terms each have norm at most
`||(1-p_i)V_i^*|| ||V_i||<=sqrt(delta)`.
With `m` colours, the compressed composite therefore differs from `R`
by at most `2m sqrt(delta)`. Its norm is at most `1+epsilon`, since
its value at one is bounded above by `R(1)`. Scaling adds at most
`epsilon+t` to the error on the unit ball. The final error on the
prescribed finite set is consequently at most

`2epsilon+t+2m sqrt(delta)`.

Simply cutting at `1-t` without the lower spectral gap does not give
this estimate: discarded eigenvalues can then be as large as `1-t`.

Neither strong quasidiagonality nor the finite-orbit replacement lemma
forces this spectral condition on a prescribed incoming map. The
replacement lemma deliberately preserves its value on the source unit.
Even the scalar quotient supports the cpc map `x -> (1/2)tau(x)1`,
whose unit weight remains distance `1/2` from every projection.
Duplicating all colours of any approximation and halving the incoming
maps preserves its composite while producing this same normalization
issue. These examples refute automatic spectral-gap assertions about
arbitrary approximations; they do not refute the existence of a better
chosen approximation. Producing such a choice for Berend, compatible
with its fixed colour budget, is still unproved.

## A finite-orbit obstruction to input-only spectral cutting

This example uses the actual Berend quotients, rather than an unrelated
algebra. There are finite `Gamma=Z^2` orbits of unbounded cardinality:
otherwise a fixed power of `alpha` would fix every torsion point, while
each nonidentity power of `alpha` has only finitely many fixed points.
Choose such orbits `O_n`, equip them with the connected Schreier graph
for the two unit generators and their inverses, and let its diameter
be `D_n`. Bounded degree and unbounded cardinality imply `D_n -> infinity`
after passing to a subsequence. Choose a diameter endpoint `x_n`.

Let `pi_n:A -> M_(|O_n|)` be the finite-orbit representation with
trivial stabilizer character. It acts on `l^2(O_n)` by diagonal
evaluation of `C(T^3)` and permutations for the acting generators.
Its image is the full matrix algebra: diagonal point projections and
the transitive permutations generate matrix units. Put

`b_n(x)=dist_(O_n)(x_n,x)/D_n`,

regarded as a diagonal positive contraction. It commutes exactly with
the coefficient torus and has commutator norm at most `1/D_n` with
each of the two acting generator unitaries. Approximation by finite
crossed-product sums shows

`||[b_n,pi_n(a)]|| -> 0` for every fixed `a in A`.

Nevertheless `dist(b_n,Z(M_(|O_n|)))=1/2`, because its spectrum includes
zero and one. A diameter geodesic supplies eigenvalues `j/D_n` for
all `0<=j<=D_n`. Consequently its distance from every projection is
at least `1/2-1/(2D_n)`, and `||b_n-b_n^2|| -> 1/4`.

Define the cpc incoming maps

`psi_n(a)=b_n^(1/2)pi_n(a)b_n^(1/2)`.

They factor through the prescribed finite-orbit quotients (enlarge
the finite invariant set to contain `O_n` if needed). For positive
orthogonal `a,c`,

`||psi_n(a)psi_n(c)||<=||a|| ||[b_n,pi_n(c)]|| -> 0`.

They are therefore asymptotically order zero on the fixed source,
but their unit weights stay far from projections and from the
finite-dimensional centers. They are not asymptotically multiplicative,
as the pair `a=c=1` shows.

Worse, for any threshold `0<t<=1`, the diagonal spectral projection
`p_n=1_[t,1](b_n)` is nontrivial. A connected graph has an edge from
its support to its complement. Thus for at least one of the two
generator permutations `U`,

`||[p_n,U]||=1`.

Taking the high spectral corner can therefore turn vanishing
fixed-generator commutators into maximal ones. Strong quasidiagonality
of the source does not alter this example, since these are already
exact finite-dimensional representations before weighting.

This construction does not include order-zero return maps whose sum
recovers the identity. It refutes only the attempted inference from
strong quasidiagonality, finite-orbit factorization, and asymptotic
order zero of the incoming maps. The full return-map constraints
must supply any further spectral conclusion.

## What the full return-map constraints actually force

The following estimate uses the full approximation, including the
return maps. Suppose `R=sum_i tau_i`, where
`tau_i=phi_i psi_i`, and every `phi_i` and `psi_i` is cpc. For a
source unitary `u`, assume

`||R(1)-1||<=epsilon`, `||R(u)-u||<=epsilon`.

Set `e_i=tau_i(1)` and `C=2 sqrt(epsilon(1+epsilon))`. Then

`||tau_i(u)-e_i u||<=C`,

`||tau_i(u)-u e_i||<=C`, and `||[e_i,u]||<=2C`.

To prove this, faithfully represent the target on a Hilbert space and
take Stinespring representations `tau_i(x)=V_i^* pi_i(x)V_i`.
Set `V=(V_i)_i`, `pi=direct_sum pi_i`, and let `P_i` be the
projection onto the `i`th summand. Thus `R(x)=V^* pi(x)V`,
`tau_i(x)=V^* P_i pi(x)V`, and `||V||<=sqrt(1+epsilon)`.
For `D=pi(u)V-Vu`,

`D^*D=R(1)-R(u^*)u-u^*R(u)+u^*R(1)u`.

Its norm is at most `4epsilon`. Multiplying `D` by `V^*P_i`
proves the first estimate; applying it to `u^*` and taking adjoints
proves the second. No assumption on matrix size or on the number of
colours enters these bounds.

For the order-zero supporting homomorphism write
`phi_i(y)=h_i pi_i^o(y)`, where `h_i=phi_i(1)` commutes with the
supporting range, and put `a_i=psi_i(1)`. The preceding estimates imply

`||h_i^2 pi_i^o([a_i,psi_i(u)])||<=4C`,

`||h_i^2 pi_i^o(psi_i(u)^*psi_i(u)-a_i^2)||<=6C`.

For the first inequality, use
`[e_i,tau_i(u)]=h_i^2 pi_i^o([a_i,psi_i(u)])`,
`tau_i(u)=e_i u+error`, and `||[e_i,u]||<=2C`.
For the second, `tau_i(u)^*tau_i(u)` is within `2C` of
`u^* e_i^2 u`, which is within `4C` of `e_i^2` by the square
commutator bound `||[e_i^2,u]||<=2||[e_i,u]||<=4C`.
These are estimates in the actual outgoing
supports. They enforce weighted approximate centrality and the
relative unitary equation with unit `a_i`, rather than idempotence of
`a_i`.

## Full approximations can have diffuse weights on full return supports

There is an exact model showing that no conclusion of spectral
concentration follows from the full constraints alone, even for a
strongly quasidiagonal AF algebra. Let
`A=tensor_(j>=1) M_2`, let `A_N=tensor_(j=1)^N M_2`, and let
`E_N:A -> A_N` be the trace-preserving conditional expectation.
Choose `N_n>n` with `N_n-n -> infinity` and choose a positive
contraction `b_n` in the tensor factors from `n+1` through `N_n`
whose eigenvalues form a uniform grid from zero to one.

Take `F_n=A_(N_n) direct_sum A_(N_n)`. Both return colours are the
same unital inclusion `A_(N_n) -> A`. Define the two incoming maps by

`psi_(0,n)(x)=b_n^(1/2) E_(N_n)(x)b_n^(1/2)`,

`psi_(1,n)(x)=(1-b_n)^(1/2) E_(N_n)(x)(1-b_n)^(1/2)`.

The direct-sum incoming map is cpc, both return colours are
order-zero *-homomorphisms, and the total outgoing norm is exactly
two. For every `x in A_n`, the composite equals `x` exactly, because
`b_n` commutes with `A_n`. Density and contractivity of the composite
give point-norm convergence to `id_A` on all of `A`.

Both return supports `phi_(i,n)(1)` are exactly `1`. Nevertheless
both incoming unit weights have spectrum filling `[0,1]` increasingly
densely, distance exactly `1/2` from the matrix center, distance tending
to `1/2` from the set of projections, and idempotence defect tending
to `1/4`. These are active weights: neither colour is an unused
summand, and no outgoing support cuts them away.

This example does not disprove an existential repair theorem: its
source already has decomposition rank zero. It does prove that such
a theorem must change the approximations, rather than deduce a
spectral-gap property of the given incoming weights from complete
return-map constraints. Nor does this AF example give a Berend
lower bound or a Berend construction.
