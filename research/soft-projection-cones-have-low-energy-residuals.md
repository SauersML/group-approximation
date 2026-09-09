---
rg: 2
id: soft-projection-cones-have-low-energy-residuals
kind: claim
title: Least-squares projection cones have low-energy residuals without an operator bound on the packing
distinct_from:
  low-energy-povms-yield-flexible-projection-cuts: That starts with a supplied near-projective POVM and bounds the sum of its threshold cuts by three times the identity; this permits an unbounded positive conic sum and controls its square root and least-squares residual before any POVM is available.
  reflected-corners-control-defective-quantum-variance: That assumes projection expansion in a supplied corner; this supplies a residual and dual certificate for an arbitrary selected projection pool, without asserting that the residual projection expands.
artifacts:
  - research/artifacts/soft-projection-cone-residual-energy-2026-09-08.md
---

Let `K:M_d->M_d` be self-adjoint, bistochastic, and UCP, with
normalized trace `tau` and energy `E_K(x)=tau(x*(x-K(x)))`.
For every finite positive sum of projections `S=sum_i w_i q_i`,
without assuming `S<=I`,

```text
E_K(sqrt(S))<=2sum_i w_i E_K(q_i),
E_K((I-S)_+)<=8sum_i w_i E_K(q_i).                     (1)
```

Let `F` be any selected family of nonzero projections satisfying
`E_K(q)<=h tau(q)`, where `h>=0`. Let `C` be its closed conic
hull, and let `S` minimize `||I-S||_2^2` over `C`. Set

```text
Delta=||I-S||_2^2,       X=I-S,       R=X_+.
```

The minimizer exists and is unique. It satisfies

```text
tau(S^2)=tau(S)=1-Delta,       0<=Delta<=1,
tau(Xq)<=0 for every q in F,
0<=R<=I,       tau(R)>=Delta,
E_K(R)<=8h tau(S)<=8h,
tau(X K(R))>=g:=Delta^2-4sqrt(h Delta).                 (2)
```

These statements also hold for an infinite pool, using its closed
conic hull and limits of finite conic sums.

Put `delta=||K^2-K||_(infinity->2)`. If `g>0`, there is a
nonzero spectral projection `q=1_(K(R)>t)`, `0<t<1`, with

```text
tau(Xq)>=g/2,
tau(q)>=g^2/(4Delta),
E_K(q)<=2sqrt(Delta)sqrt(delta/2)/g,
E_K(q)/tau(q)<=8Delta^(3/2)sqrt(delta/2)/g^3.            (3)
```

In particular the actual mixed-norm defect suffices; no global
`2->2` defect bound is assumed. At `delta=0`, the projection
in (3) can be chosen with zero energy.

The pool may, for example, consist of projections satisfying an
additional expansion test. Equation (3) does not prove that its
output passes that test. Positive dual gain and low energy alone
do not solve component selection: `I` itself has zero energy and
`tau(X)=Delta>0` whenever the conic fit is imperfect. The substantive
estimate is the soft-sum and residual control in (1)--(2); converting
the residual into admissible expanding seeds remains a separate gap.

There is also a finite weighted amplification consequence. For a
finite family of projections and rational weights `w_i=k_i/M>=0`,
put

```text
S=sum_i w_i q_i,       beta=||S-I||_2,       s=tau(S)>0,
D=sum_i k_i rank(q_i)=Md s.
```

For any finite family of source unitaries `U_a`, define
`epsilon^2=max_a sum_i w_i ||[U_a,q_i]||_2^2`.
Polar completion in the corners supplies unitaries on the direct
sum of `k_i` copies of each `q_i C^d`. For every length-`L` word,
with `a_w=||U_w-I||_2`, they satisfy

```text
||V_w-I||_(2,D)
 <=[sqrt(a_w^2+2a_w beta)+L epsilon]/sqrt(s),

|tr_D(V_w)-tr_d(U_w)|
 <=L epsilon/sqrt(s)+(beta+|s-1|)/s.                  (4)
```

Thus weighted cone coverage approaching `I`, together with vanishing
weighted generator boundary, inherits fixed relators and canonical
fixed-word traces after amplification, without a POVM purity
assumption. At a cone minimizer, `beta=sqrt(Delta)` and `s=1-Delta`;
general real cone sums are reached by finite-sum and rational-weight
approximation. No expansion of the chosen corners follows from (4).

This is a written finite-dimensional proof. It establishes neither
general channel rounding nor nonhyperlinearity.

DERIVATION
hermitian-dilation-and-conic-duality-control-residuals
