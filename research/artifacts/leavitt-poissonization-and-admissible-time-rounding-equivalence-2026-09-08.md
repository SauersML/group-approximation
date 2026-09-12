# Heat structure and admissible-time quantifiers in the rounding problem

2026-09-08. Written finite-dimensional arguments, independently audited.
No computation or build. These reductions do not establish heat rounding
or determine hyperlinearity of H.

Use normalized matrix trace, normalized Hilbert--Schmidt norm, and
`||T||_(infinity->2)=sup_(||x||_op<=1)||T(x)||_2`. A bistochastic UCP
map preserves the identity and trace and is completely positive. Such
maps contract both operator norm and L2.

## 1. Poissonization preserves a near-idempotent channel uniformly

Let `P:M_d->M_d` be a bistochastic UCP map, self-adjoint on L2, and put

```text
delta=||P^2-P||_(infinity->2),
A=I-P,                     Q_t=exp(-t A),   t>=0.
```

Then `0<=A<=2I` on L2. The Poisson expansion

```text
Q_t=exp(-t) sum_(j>=0) (t^j/j!) P^j
```

makes Q_t a self-adjoint bistochastic UCP map. It also gives a
dimension-independent estimate:

```text
||Q_t-P||_(infinity->2)
 <= 2 exp(-t)+(t-1+exp(-t)) delta.                     (1)
```

Indeed, for every integer `j>=1`, telescoping with L2 contractivity gives

```text
P^j-P=sum_(a=0)^(j-2) P^a(P^2-P),
||P^j-P||_(infinity->2)<=(j-1)delta.
```

The sum is empty for j=1. The j=0 term has norm at most two. Summing
the Poisson weights proves (1), since their weighted sum of `j-1`
over j>=1 is `t-1+exp(-t)`.

For `0<delta<1`, choose `t=log(1/delta)` and set

```text
b(delta)=delta(log(1/delta)+1+delta).
```

Then

```text
||Q_t-P||_(infinity->2)<=b(delta) -> 0,
||Q_t^2-Q_t||_(infinity->2)<=delta+3b(delta) -> 0.      (2)
```

The second estimate follows by expanding
`Q_t^2-P^2=Q_t(Q_t-P)+(Q_t-P)P` and using the two contractivities.
In particular the transformed maps satisfy actual uniform
near-idempotence, not just a heat representation.

These generators also satisfy the exact residual identity

```text
A^2-A=P^2-P,       ||A^2-A||_(infinity->2)=delta.       (3)
```

Thus an approximate analytic gap certificate with gap parameter one
and an empty sum of squares is present, with `delta t->0`. Equation
(3) is not an identity in a fixed group algebra. The map P need not
be mixed unitary, its Kraus rank need not be bounded, and no fixed
generating group or canonical character is produced.

## 2. General heat rounding is equivalent to general channel rounding

Consider the following dimension-independent sequential statement:

```text
(U) Every sequence of self-adjoint bistochastic UCP maps P_n with
    ||P_n^2-P_n||_(infinity->2)->0 admits unital matrix subalgebras B_n
    with ||P_n-E_(B_n)||_(infinity->2)->0.
```

Statement (U) is equivalent to its restriction to Poisson heat maps
`Q_n=exp(-t_n(I-T_n))`, where T_n are self-adjoint bistochastic UCP
maps, `t_n->infinity`, and

```text
|| (I-T_n)^2-(I-T_n) ||_(infinity->2) t_n -> 0.
```

One may either impose uniform near-idempotence of Q_n explicitly or
deduce it from (1)--(2). To deduce it directly in this formulation,
put delta_n equal to the displayed generator defect before multiplication
by t_n. Formula (1) shows `||Q_n-T_n||_(infinity->2)->0`; telescoping
then gives `||Q_n^2-Q_n||_(infinity->2)->0`.

The forward implication is immediate. For the converse apply the
restricted theorem to the maps in (2), with T_n=P_n, and transfer the
resulting expectations back by the triangle inequality. At zero-defect
indices, P_n already is a trace-preserving conditional expectation.
Alternatively, use any t_n tending to infinity there and (1).

For completeness, a trace-preserving UCP idempotent has algebraic
range: if P(x)=x, Schwarz gives `P(x*x)>=x*x`; equality of their
traces and faithfulness force equality, and likewise for `xx*`.
The multiplicative-domain identities then make the fixed space a
unital star algebra and P its trace-preserving expectation.

Consequently, infinite divisibility and the abstract bounded residual
estimate (3) cannot by themselves make the unrestricted rounding
problem easier. This does not identify (U) with the H-specific
rounding property (R): the latter also has fixed adjoint word maps,
canonical traces, and actual group-algebra SOS data.

## 3. Native rounding at one admissible time gives every admissible time

Fix one full canonical matrix microstate sequence for the native
property-(T) group and its fixed SOS certificate. Write

```text
P_n(t)=exp(-t A_n),
epsilon_n=bound on the fixed SOS equality-row defects,
kappa>0=the fixed Kazhdan gap parameter.
```

The [heat-energy estimate](leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md)
provides a constant C depending only on the fixed certificate and,
for every contraction x,

```text
<A_n P_n(r)x,P_n(r)x>
 <=2 exp(-2 kappa r)||x||_2^2+C epsilon_n/kappa.       (4)
```

For any s,t>=0, this implies

```text
||P_n(t)-P_n(s)||_(infinity->2)^2
 <=(2/kappa) exp(-2 kappa min(s,t))
   +(2C epsilon_n/kappa)|t-s|.                       (5)
```

To prove it, suppose s<=t. Spectral calculus for `A_n>=0` gives

```text
||(P_n(s)-P_n(t))x||_2^2
 <=||P_n(s)x||_2^2-||P_n(t)x||_2^2
 =2 integral_s^t <A_n P_n(r)x,P_n(r)x> dr.
```

Integrate (4) and take the operator-unit-ball supremum. Interchanging
s and t handles the other order.

It follows that whenever both time sequences are admissible,

```text
s_n,t_n->infinity,       epsilon_n max(s_n,t_n)->0,
```

their heat maps have vanishing uniform difference. In particular,
for this fixed microstate sequence, the following are equivalent:

- Some admissible time sequence admits rounding to E_(B_n).
- Every admissible time sequence admits rounding to E_(B_n), using
  the same algebras once one such sequence and its algebras are chosen.
- One prescribed admissible logarithmic time sequence admits rounding.

For a logarithmic choice without zero-error exceptions, replace the
error bound by `bar epsilon_n=max(epsilon_n,exp(-n))` and, after a
finite initial segment, take

```text
s_n=kappa^(-1) log(1/bar epsilon_n).
```

Enlarging a certified error bound preserves every estimate and gives
`s_n->infinity` and `bar epsilon_n s_n->0`.

Thus the premise (R) in
[the two-use nonhyperlinearity reduction](leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md)
can replace 'every admissible time' by 'some admissible time' for
each full canonical microstate sequence. The universal quantifier over
microstate sequences is still essential to that argument: the second
use concerns the sequence obtained by selection and restriction through
the native isomorphism H->L. No rounding sequence is constructed here.
