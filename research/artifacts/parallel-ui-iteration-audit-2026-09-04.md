# Audit of the uniformly integrable cohomological correction

The one-step argument in `parallel-arithmetic-holonomy-2026-09-04.md`
is valid, subject to a minor word-representative clarification below.
Damping improves its conclusion: one can preserve uniform integrability
of the normalized residuals while making the defect relatively smaller.
This still does not prove convergence to exact representations. Moreover,
for the arithmetic groups in question, qualitative stability restricted
to this uniformly integrable input class would already imply unrestricted
normalized-HS stability. The remaining iteration issue therefore carries
the full stability problem.

## Published input and analytic audit

[Bader--Sauer, arXiv:2308.06517v3](https://arxiv.org/html/2308.06517v3)
Theorem A gives vanishing through degree two for representations without
invariants when `n>=4`. Theorem C identifies scalar degree-two lattice
cohomology with continuous cohomology in this range. Equation (1) makes
that scalar group zero. These inputs justify the stated specialization
to `SL_n(Z)`, `n>=4`; they do not give the same conclusion for `SL_3(Z)`.

For arbitrary trivial Hilbert coefficients, the scalar assertion extends
as claimed. A finite presentation gives finite-rank free resolution terms
through degree two; after applying trivial coefficients, the relevant
scalar differentials have finite-dimensional domains or ranges. Tensoring
their finite-dimensional linear algebra with the Hilbert coefficient
space preserves the degree-two exactness. Splitting a unitary module into
invariants and their orthogonal complement is therefore legitimate.

The regular Hilbert-ultraproduct subspace is the correct coefficient
module. The product estimate, skew-Hermitian defect class, cocycle
identity, real projection, and exponential remainder estimates all check
out. Van Kampen expansions use only fixed words. No normalized-HS
submultiplicativity is being assumed.

One clarification is needed in the last displayed generator estimate.
The word `q_s` need not literally be the generator letter `s`. If these
are different, the estimate must include
`||U_j(q_s)-U_j(s)||_2=O(delta_j)`, obtained from their fixed null word.
Alternatively choose `q_s=s` when the presentation's generator images
permit this. For a general presentation, let `e_(j,s)` be the
skew-Hermitian part of `(U_j(q_s)U_j(s)^*-I)/delta_j`. This is regular,
and its discarded Hermitian part tends to zero in 2-norm by the same
product estimate used for the defect cocycle. Replace the generator
correction `b_j(s)` by `b_j(s)-e_(j,s)`. Then
`exp(-delta_j[b_j(s)-e_(j,s)])U_j(s)` differs from `v_j(s)` by
`o(delta_j)` and cancels the first-order defining errors. Below, the
notation `b_(j,s)` means these adjusted skew-Hermitian corrections.

## A stronger, profile-preserving improvement

Write `A_(j,r)=(U_j(r)-I)/delta_j`, with
`max_r||A_(j,r)||_2=1`. The cohomological argument supplies regular
skew-Hermitian generator corrections `b_(j,s)` such that the full
correction cancels the first-order defining errors. For `0<=t<=1`, put

```text
V_j(t,s)=exp(-t delta_j b_(j,s)) U_j(s).
```

The same Taylor and product estimates, uniformly for `t` in this compact
interval, give

```text
eta_j := max_r sup_(0<=t<=1)
 ||(V_j(t,r)-I)/delta_j-(1-t)A_(j,r)||_2 ->_omega 0.    (UI1)
```

Indeed the linear term in `t` is minus the original defining error,
up to a vector tending to zero; all higher terms have uniformly vanishing
normalized 2-norm. The domination in the exponential estimate uses
`t<=1`, so its bounded-part and tail bounds are uniform in `t`.

Choose positive `epsilon_j->_omega 0` with
`eta_j/epsilon_j->_omega 0`, for example
`epsilon_j=sqrt(eta_j)+1/j` on the ultrafilter-large set where this is
less than one. Set `V_j=V_j(1-epsilon_j)` and let `delta'_j` be its
defining defect. Equation `(UI1)` yields

```text
delta'_j/(epsilon_j delta_j) ->_omega 1,
max_r ||(V_j(r)-I)/delta'_j-A_(j,r)||_2 ->_omega 0.      (UI2)
```

Thus the new defect is positive and `o_omega(delta_j)`, the generator
correction is `O(delta_j)`, and its normalized defining residuals have
the same Hilbert-ultraproduct classes as the original residuals.
In particular they are still uniformly square-integrable along the
ultrafilter. The usual subsequence extraction gives ordinary sequence
versions of these conclusions.

This is stronger than a bare improvement that might expose a concentrated
new leading error. It retains a deliberately larger copy of the old
regular error until all nonlinear remainders are relatively negligible.

## Why repeated damping does not yet give exactness

For every fixed finite number of improvements, `(UI2)` can preserve the
original residual profile in the ultraproduct. This is not a uniform
estimate over infinitely many iterations at each fixed matrix size.
The sufficiently-large-index cutoff can increase at every iteration.
Diagonalizing supplies an iteration count `k_j->infinity` and a still
approximate tuple; it does not supply an exact tuple in each dimension.

The distinction occurs already in an explicit stable example. In `C_2`,
let `P_j` have rank one, put `t_j=d_j^(-1/4)`, and set

```text
U_j(s)=exp(i t_j)[I+(i-1)P_j].
U_j(s)^2-I=(exp(2i t_j)-1)I-2exp(2i t_j)P_j.
```

Here `delta_j~2t_j`, and the normalized error converges in 2-norm to
`iI`, so it is uniformly integrable. Removing the diffuse scalar phase
exposes the residual `-2P_j`, whose normalized version is
`-sqrt(d_j)P_j` and is not uniformly integrable. Damping can keep a
diffuse residual above the rank-one scale for every fixed iteration.
At a fixed `j`, taking that phase all the way to zero still leaves the
rank-one defect. Repairing that block is an additional operation. The
group `C_2` is stable, so this is an obstruction to the proposed inference,
not a counterexample to stability or to the existence of a better scheme.

A minimal-defect argument in a compact neighborhood has the same gap:
its minimizing tuple need not have a uniformly integrable normalized
residual. The assumption controls the initial sequence, and `(UI2)`
controls selected finite transitions; neither controls arbitrary limits
or minimizers at smaller and smaller defect scales.

## Uniformly integrable input stability would imply full stability

Here is a precise reason that this issue cannot be dismissed as a small
sector restriction. Suppose the finite presentation has a defining relator
with a nonzero exponent-sum vector. Choose real numbers `x_s` such that

```text
a_r=sum_s exponent_s(r) x_s,
A=max_r |a_r|>0.
```

Given *any* asymptotic representation `U_j` with defect `delta_j->0`,
choose `t_j->0` with `delta_j/t_j->0`, and define

```text
W_j(s)=exp(i t_j x_s) U_j(s).
```

Scalar factors commute, so exactly

```text
W_j(r)-I=(exp(i t_j a_r)-1)I
             +exp(i t_j a_r)(U_j(r)-I).
```

Writing `Delta_j` for the new defining defect, the triangle and reverse
triangle inequalities imply `Delta_j/t_j->A`. Consequently

```text
max_r ||(W_j(r)-I)/Delta_j-i(a_r/A)I||_2 -> 0.          (UI3)
```

These normalized residuals are uniformly square-integrable, since they
are 2-norm close to uniformly operator-bounded scalar matrices. Also
`max_s||W_j(s)-U_j(s)||_2<=t_j max_s|x_s|->0`.

Therefore, if every uniformly integrable input sequence were asymptotic
to genuine representations, then every input sequence would be. The
argument preserves the same-dimension or flexible version of the desired
conclusion. It also preserves fixed-word limiting traces if those are
part of the input requirement.

For a nonempty finite presentation of a group with finite abelianization,
the defining exponent-sum vectors span the rational generator space;
the required choice of `x` exists. In particular this applies to the
arithmetic Kazhdan groups at issue. Thus even qualitative stability of
the uniformly integrable sector is equivalent here to unrestricted
stability. The cohomological one-step lemma, including `(UI2)`, does not
yet establish either one.

## Result and verification scope

The subsequently added Section 6 of the arithmetic artifact also checks
out. Each individual adjoint unitary preserves the regular subspace in
both directions, so its orthogonal projection commutes with that adjoint
operator even though the full ultraproduct action need not obey the group
law. If `A_j,B_j` have 2-norm `O(delta_j)` and bounded operator norms,
the scaled product `A_j B_j/delta_j` is 2-norm bounded and pairs to zero
with every operator-bounded test sequence, by trace Cauchy--Schwarz.
Thus its regular projection vanishes. This justifies both the projected
skew-Hermitian defect and the projected cocycle identity.

After solving the projected cocycle, mixed nonlinear terms involving the
old possibly concentrated defects still vanish in full 2-norm: the
scaled exponential difference is regular, while the other factor is
operator-bounded and small in 2-norm. Orthogonality to the regular
subspace is equivalent to vanishing normalized 1-norm, since the polar
partial isometry is an allowable bounded test sequence. These observations
validate `(AH8)` through `(AH10)` and interpolation for `1<=p<2`.

Finally, the finite join of the relator spectral tail projections has
trace bounded by the sum of their traces. Its complement is below each
low-spectrum projection. Every relator residual is normal, being a
unitary minus identity, so the same cutoff bounds multiplication on
both sides. This proves `(AH11)`. The resulting small projection is
not shown approximately invariant at a scale useful for HS correction;
the stated boundary-leakage warning is necessary. This audit finds no
extra conclusion giving flexible stability from Section 6.

The phase-completeness argument is now encoded as
`scalar-phase-regularization-makes-ui-stability-complete`, including the
general Tietze extension `P^+=<S,z|R,z=1>`. Setting the additional
generator to `exp(i t_j)I`, with `delta_j/t_j->0`, supplies the scalar
dominant residual for every finite presentation, even when all old
relators have zero exponent sums. Uniformly integrable input stability
for that presentation would imply full stability of the original group.

The audit supports the arithmetic specialization and strengthens one-step
improvement by proving preservation of the normalized residual profile.
It does not close the iteration gap. A scale-uniform tail estimate or a
rigorous repair of newly exposed concentrated defects is still missing.
All arguments here were checked analytically; no code or build was run,
and this document is not a proof-kernel verification.
