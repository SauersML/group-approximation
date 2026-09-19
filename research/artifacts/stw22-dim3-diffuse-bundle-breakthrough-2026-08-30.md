# STW XXII: factor-uniform dimension-three diffuse-bundle audit

## What is new

The inclusive spectral-supercarrier theorem supplies a two-sphere filling
modulus for every strong Stiefel space in every separable-predual II1
factor, with one numerical modulus. The relative three-ball theorem fills
the low spectrum inside the complement of a previously filled high frame.
Putting all copies into one rectangular row of `M_m(N)` transfers those
two inputs to arbitrary weighted-copy fibres without choosing the copies
independently.

## Exact amplification arithmetic

With `tau_m=(Tr_m tensor tau)/m`, `e=e_11 tensor 1`, and
`R(v)=sum e_1j tensor v_j`,

```text
R(v)^*R(v)=diag(a,...,a),
tau_m(diag(p,...,p))=tau(p),
tau_m(e)=1/m,
d_tuple(v,w)^2=m||R(v)-R(w)||_(2,tau_m)^2.             (A1)
```

The normalized trace on `eM_m(N)e` multiplies `tau_m` by `m`, so a fixed
reference frame identifies the high rectangular Stiefel space isometrically
with a Stiefel space in that diffuse corner. The support condition
`m tau(supp(a))<1` is exactly

```text
tau_m(P_high)+tau_m(P_low)<tau_m(e),                   (A2)
```

the strict reserve required by the relative low-spectrum theorem.

The low extension is one matrix operator `X`, not `m` separate selections.
The identity `X^*X=diag(b,...,b)` recovers every source and every cross
orthogonality relation. Its size in tuple metric is

```text
sqrt(m) 2sqrt(tau_m(diag(b,...,b)))
 =2sqrt(m tau(b))<=2sqrt(eta).                         (A3)
```

This estimate is independent of the factor, copy number, weight, and
positive slack.

## Relative-selection audit

The hard cutoff occurs only in the fixed weight `a` while a single fibre
sphere is filled, so its projection is constant in the sphere parameter.
The high frame is continuous because the inverse square root is bounded on
the high band. The low boundary is filled by the separately audited
relative dyadic-band theorem. That theorem handles `b=0`, uses singleton
boundary values with an explicit lower-semicontinuity proof, retains a
strict trace reserve at every recursive band, and combines its degree-zero,
degree-one, and degree-two moduli before invoking Michael with `n=2`.

## Bundle-selection audit

The pre-existing stabilization theorem supplies one complete ambient
Hilbert space, nonempty closed weighted-copy values, lower semicontinuity
uniformly across finite factors, and operator-ball recovery. Countable
generation gives separable-predual fibres. The new factor-uniform
degree-two modulus is therefore exactly the missing input for Michael
selection over compact Hausdorff bases of covering dimension at most
three. The standard arbitrary-`m` spectral-cut replication then kills every
bounded positive fibre-gap trace and identifies the trace simplex with
`Prob(K)`.

## Scope boundary

Every fibre is assumed diffuse II1. The proof uses Jekel contractibility
for stabilizer corners in the Stiefel supercarrier step. Matrix stabilizers
may have a `pi_1` obstruction; no matrix or mixed-fibre dimension-three
claim is made. The older all-finite-factor theorem through dimension two
remains unchanged.

Primary inputs checked: E. Michael, *Continuous Selections II*, Ann. of
Math. 64 (1956), Theorem 1.2; I. Farah and A. Vaccaro, *Continuous
Selection of Unitaries in II1 Factors*, Proc. Amer. Math. Soc. 154 (2026),
Theorem 1.1 and Claims 3.1--3.2; D. Jekel, *The unitary group of a II1
factor is SOT-contractible*, Math. Ann. 393 (2025), Theorem A; and M.
Takesaki, *Theory of Operator Algebras III*, Lemmas XIV.2.1--2.