---
rg: 2
id: transpose-average-kills-positivity-only-channel-rounding-proof
kind: route
title: Haar-Choi lower bounds for the transpose average and the Schwarz step of channel rounding
target: transpose-average-kills-positivity-only-channel-rounding
requires: []
---

Notation: `tau=Tr/d`, `||y||_2^2=tau(y*y)`, `||.||_HS` is the unnormalized
Frobenius norm, `e_ij` are matrix units, `theta(x)=x^T`, `S=(id+theta)/2`.
For a linear map `Phi` on `M_d`, `C_Phi=sum_ij e_ij (x) Phi(e_ij)` is its
Choi matrix. `Omega=C_id=sum_ij e_ij (x) e_ij` and `F=C_theta=sum_ij e_ij (x) e_ji`
is the flip.

## Pre-commit answers (heretic card)

The three unstated assumptions shared by the hot families' rounding
certificates are:

- **(A)** the obstruction is group rigidity or stability;
- **(B)** the non-Connes-embedding input enters through trace selection;
- **(C)** the certificates are `L^2`-linear or order-spectral (SOS, gaps,
  heat, cohomology), and complete positivity is a technical side condition.

This route denies (C).

- **Why it can succeed where earlier attempts did not.** Spectral cutoff,
  special-class rounding and compact-group selection were each dropped
  because a construction failed. None of them tested which hypothesis
  carries the load. A single exact positive idempotent tests all
  positivity-only arguments at once.
- **First falsifiable step.** Check numerically, for `d=2..6`, the Choi
  spectrum, the Haar identity and the algebra lower bound on random
  subalgebras. This is done by the script; all checks pass.
- **Calibration.** Commutative Markov operators, where positive equals CP
  and rounding is known. There `S` has no analogue, so nothing false is
  predicted. On exact expectations the bounds are attained or consistent.

## 1. Structure of S

- **Unital, trace-preserving, positive.** `theta` is unital, trace-preserving
  and preserves spectra, hence positivity. `S` inherits all three.
- **Self-adjoint on L^2.** `Tr((x^T)* y)=Tr(conj(x) y)=Tr(x* y^T)`, so
  `theta` is `L^2`-self-adjoint, and so is `S`.
- **Idempotent.** `theta^2=id` gives `S^2=(2 id+2 theta)/4=S`.
- **Kadison.** It holds for every positive unital map.
- **Schwarz fails at e_12.** `S(e_12)=(e_12+e_21)/2`, so
  `S(e_12)*S(e_12)=(e_11+e_22)/4`, while `S(e_12* e_12)=e_22`. The difference
  has eigenvalue `-1/4` on `e_1`.
- **Not 2-positive.** Apply `id_2 (x) S` to the positive matrix
  `sum_(i,j<=2) e_ij (x) e_ij`. The result
  `[[e_11,(e_12+e_21)/2],[(e_12+e_21)/2,e_22]]` has quadratic form `-1` at
  `a=(0,1), b=(-1,0)`.
- **Range.** `S(M_d)` is the set of symmetric matrices `x=x^T`.

## 2. The Haar-Choi identity

For any linear `Phi`, write `Phi(u)=sum_ij u_ij Phi(e_ij)`. Haar orthogonality
`E[u_ij conj(u_kl)]=delta_ik delta_jl/d` gives

```text
E_u ||Phi(u)||_2^2 = (1/d) sum_ij (1/d) ||Phi(e_ij)||_HS^2 = ||C_Phi||_HS^2 / d^2 .
```

Unitaries are contractions, so `||Phi||_(infinity->2) >= ||C_Phi||_HS/d`. (H)

Two trace identities follow from the definitions:

```text
<Omega, C_Phi>_HS = sum_ij Phi(e_ij)_ij = Tr_(L^2)(Phi),
<F, C_Phi>_HS     = sum_ij Tr(e_ij Phi(e_ij)) = Tr_(L^2)(theta Phi).
```

Also `||Omega||_HS^2=||F||_HS^2=d^2` and `<Omega,F>=Tr(F Omega)=Tr(Omega)=d`,
since `F Omega=Omega`. Therefore

```text
||C_S||_HS^2 = (d^2 + 2d + d^2)/4 = (d^2+d)/2 .
```

## 3. Distance to expectations (item 2)

Let `A` be a unital `*`-subalgebra with `m=dim A`. Let `E=E_A` be the
`tau`-preserving expectation, the `L^2`-orthogonal projection onto `A`.

- `E` is UCP, so `C_E>=0` and `Tr C_E = Tr E(1) = d`.
- `<Omega,C_E>=Tr_(L^2)(E)=m`, and `||C_E||_HS^2 = Tr_(L^2)(E*E) = m`.
- `<F,C_E>` is real, and `|<F,C_E>| <= ||F||_op Tr C_E = d`.

Hence

```text
||C_S - C_E||_HS^2 = (d^2+d)/2 - (m + <F,C_E>) + m >= (d^2+d)/2 - d = d(d-1)/2 ,
```

and (H) gives `||S-E_A||_(infinity->2) >= sqrt((d-1)/(2d))`.

Equality in the Choi estimate means `<F,C_E>=d`. This holds for `A=M_d`
(`C_E=Omega`) and for the diagonal masa (`C_E=sum_i e_ii (x) e_ii`).

## 4. Distance to CP maps (item 3)

`C_S=(Omega+F)/2`. On the antisymmetric subspace `F=-1` and `Omega=0`, so
`C_S=-1/2` there, with multiplicity `d(d-1)/2`. The other eigenvalues are
`1/2`, on the symmetric subspace orthogonal to `omega=sum e_i (x) e_i`, and
`(d+1)/2`, on `omega`.

If `T` is CP then `C_T>=0`. Let `Q` be the projection onto the
antisymmetric subspace. Then
`||C_S-C_T||_HS >= ||Q(C_S-C_T)Q||_HS`, and `-QC_TQ<=0` while
`QC_SQ=-Q/2`. For `K>=0`, `||Q/2+K||_HS >= ||Q/2||_HS`. Hence
`||C_S-C_T||_HS >= (1/2) sqrt(d(d-1)/2)`, and (H) gives
`||S-T||_(infinity->2) >= sqrt((d-1)/(8d))`.

This is the distance from `C_S` to the PSD cone. It is attained by the CP
map with Choi matrix `(C_S)_+`, but that attains the Choi bound, not
necessarily the `infinity->2` bound.

## 5. Failure of product closure (item 4)

If `a,b` are real symmetric, then `(ab)^T=ba`, so `S(ab)=(ab+ba)/2` and
`S(ab)-ab=-[a,b]/2`.

Take `Z=diag(1,-1)`, `X=[[0,1],[1,0]]`, and `a=Z(x)I_(d/2)`,
`b=X(x)I_(d/2)` for even `d`. These are fixed symmetric unitaries with
`[a,b]=2(e_12-e_21)(x)I`, which is `2` times a unitary. Hence
`||S(ab)-ab||_2=1`.

Compare Section 4 of the heat-rounding artifact. Estimate (4.4),
`||P(ab)-ab||_2 <= sqrt(2eps)+2eps`, would give `0` at `eps=0`. Its proof
writes `P(ab)-P(a)P(b)=V* pi(a)(I-VV*) pi(b) V`, which needs a Stinespring
dilation. The one place where a positivity-only argument certainly breaks
is here. The range of a positive idempotent is closed only under the
Jordan product.

## 6. Exact two-positive dichotomy (item 5)

Let `P` be unital, 2-positive, trace-preserving and exactly idempotent.
Put `A=P(M_d)`.

- 2-positive unital maps satisfy Schwarz, `P(x*x)>=P(x)*P(x)`.
- For `x` in `A`: `P(x*x)-x*x>=0`, and it has trace `0` by trace
  preservation. By faithfulness of `tau`, `P(x*x)=x*x`, so `x*x` is in `A`.
- `A` is `*`-closed, because positive maps are `*`-preserving.
- Polarization `sum_(k=0..3) i^k (x+i^k y)*(x+i^k y) = 4 y*x` gives `y*x`
  in `A` for `x,y` in `A`. Replacing `y` by `y*` gives closure under products. So `A` is a unital
  `*`-subalgebra.
- If `P` is also `L^2`-self-adjoint, it is the orthogonal projection onto
  `A`, i.e. `E_A`.

## 7. Corollary

Suppose a proof establishes: "unital, positive, trace-preserving, `L^2`
self-adjoint, Kadison, defect `delta` implies distance `<=f(delta)` from an
expectation", with `f(0)<1/2`. Apply it to `S_d`, where `delta=0`. It
contradicts Section 3.

For perturbations, the triangle inequality gives
`||P-E_A|| >= 1/2 - ||P-S_d||`.

By Section 6 the conclusion does hold exactly under 2-positivity. So the
hypothesis that must be used is two-positivity, and it must enter at the
product step of Section 5. Every spectral, coarea, pinched-flow or
Cheeger-type step that only uses the order structure on individual
Hermitian elements is blind to the difference between `S_d` and `E_A`.

The statement is dimension-free because `sqrt((d-1)/(2d)) >= 1/2` for all
`d>=2`.

## Verification

Run `nice -n 10 timeout 1200 python3 experiments/channel-rounding-2026-09-17/transpose_obstruction.py`.
Output is recorded in `transpose_obstruction_output.txt`. For `d=2..6` the
script checks:

- the Choi spectrum;
- distance `sqrt((d-1)/(8d))` of `C_S` to the PSD cone;
- the Haar identity, by Monte Carlo with 4000 samples, error below `0.05`;
- the algebra lower bound on scalars, masas, block diagonals and
  `I_m (x) M_k`, each conjugated by random unitaries, with equality for
  `M_d` and the masa;
- the Schwarz and 2-positivity violations;
- the product-closure defect `1`.
