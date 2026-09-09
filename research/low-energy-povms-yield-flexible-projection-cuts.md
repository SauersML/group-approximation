---
rg: 2
id: low-energy-povms-yield-flexible-projection-cuts
kind: claim
title: A supplied low-energy POVM gives projection cuts with controlled total boundary and flexible matrix dimension
distinct_from:
  outcome-count-free-subpovm-completion: That produces an orthogonal PVM close to supplied effects with a cost controlled by their purity deficit; this permits overlapping physical cuts and passes to their abstract direct sum, making total boundary vanish with effect energy even when the purity deficit is fixed.
  reflected-corners-control-defective-quantum-variance: That estimates variance inside one supplied expanding corner; this constructs low-energy projection cuts from a supplied POVM and inherits source unitary word errors, without asserting expansion.
  symmetric-markov-near-idempotents-round-to-partitions: That obtains an actual partition expectation for a classical reversible kernel; these quantum projection cuts need not be orthogonal in the original matrix space and supply a flexible direct-sum model instead.
artifacts:
  - research/artifacts/low-energy-povm-flexible-cuts-2026-09-08.md
---

Let `K:M_d->M_d` be self-adjoint, bistochastic, and UCP, with
`tau=Tr/d` and `E_K(x)=tau(x*(x-K(x)))`. Suppose a finite
POVM `f_i>=0`, `sum_i f_i=I`, satisfies

```text
sum_i tau(f_i-f_i^2)<=gamma<1/3,
sum_i E_K(f_i)<=eta.
```

There are thresholds `t_i in (1/3,2/3)` and projections
`r_i=1_(f_i>t_i)` such that, for `S=sum_i r_i`,

```text
sum_i E_K(r_i)<=3sqrt(3eta),
S<=3I,             ||S-I||_1<=3gamma,
(1-3gamma)d <= D:=sum_i rank(r_i) <= (1+3gamma)d.
```

The projections may overlap physically. Their abstract direct sum
`H_new=direct_sum_i r_i C^d` has dimension `D` and exactly
orthogonal summands.

For any finite list of source unitaries `U_a`, put

```text
epsilon=max_a [sum_i ||[U_a,r_i]||_(2,d)^2]^(1/2),
s=D/d.
```

Polar completion in each corner supplies unitaries
`V_a=direct_sum_i V_(a,i)` on `H_new`. For every word `w`
of length `L` in these generators and their inverses,

```text
||V_w-I_D||_(2,D)
 <= [sqrt(3)||U_w-I_d||_(2,d)+L epsilon]/sqrt(s),

|tr_D(V_w)-tr_d(U_w)|
 <= L epsilon/sqrt(s)+6gamma/s.
```

These estimates are independent of the number of effects. If
`K=sum_a omega_a Ad(U_a)` is self-adjoint, with positive weights
of total one, then

```text
epsilon^2 <= (6/omega_min)sqrt(3eta).
```

More generally, any supplied inequality
`||[U_a,x]||_2^2<=A E_K(x)` for self-adjoint `x` gives
`epsilon^2<=3A sqrt(3eta)`.

Thus, when `gamma,eta` and the source fixed-word errors tend to
zero under uniformly bounded energy-domination constants, the direct-sum dimension ratio
tends to one and both relators and canonical fixed-word traces
are inherited. Exact source relations other than unitarity are
not asserted to remain exact after polar repair.

The artifact also gives the original-source localization application
`f_i=K(p_i)` for a supplied orthogonal seed partition, and a
precise rank comparison with those seeds. It does not extract the
seed partition, prove that the new corners expand, construct a
same-dimension orthogonal partition, or prove general channel
rounding or nonhyperlinearity.
