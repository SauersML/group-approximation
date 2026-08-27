# One mixed Pauli word localizes a Gram under a uniformly gapped transitive actor

## The exact Weyl square function

Let `P_N` be a finite Heisenberg/Pauli group on a fixed nontrivial central
character sector, with Weyl quotient `V_N`.  Write `W_v`, `v in V_N`, for
unitary Weyl representatives, and let

```text
E_P(T)=|V_N|^(-1) sum_(v in V_N) W_v T W_v^*.          (KPR1)
```

This is the trace-preserving conditional expectation onto the Pauli
commutant.  For every matrix `T`,

```text
|V_N|^(-1) sum_v ||[T,W_v]||_2^2
 =2||T-E_P(T)||_2^2.                                   (KPR2)
```

Indeed, expand each commutator square and average.  Since `E_P` is the
orthogonal projection in Hilbert--Schmidt space, the cross term is
`||E_P(T)||_2^2`, giving `(KPR2)`.

There is also an unweighted martingale form.  Choose a symplectic Pauli
basis and let `E_i` average over the `i`th one-cell Pauli subgroup.  The
`E_i` commute.  With

```text
T_0=T,        T_i=E_i E_(i-1)...E_1(T),                (KPR3)
```

the differences are orthogonal and

```text
sum_(i=1)^N ||T_(i-1)-T_i||_2^2
 =||T-E_P(T)||_2^2.                                    (KPR4)
```

Thus the correct localization statistic is a genuine operator martingale
square function.  It has no factor `N`; the familiar `sqrt(N)` loss appears
only when `(KPR4)` is bounded by `N` separate pointwise generator errors.

## Collapse of the whole square function to one prototype

Let a finite actor `K_N` act by automorphisms of `P_N`, transitively on
`V_N\{0}`.  Suppose symmetric generating sets `S_N` of uniformly bounded
cardinality have a uniform conjugation-module gap `kappa>0`, in the
normalization

```text
|S_N|^(-1) sum_(s in S_N)||[T,U_s]||_2^2
 >= kappa ||T-E_K(T)||_2^2,                            (KPR5)
```

where `E_K` averages conjugation by the actor.

Fix one nonzero Weyl word `W_0` and define

```text
epsilon_K^2=|S_N|^(-1)sum_s ||[T,U_s]||_2^2,
epsilon_0=||[T,W_0]||_2.                               (KPR6)
```

Put `Tbar=E_K(T)` and `a=||T-Tbar||_2`.  Equation `(KPR5)` gives

```text
a<=epsilon_K/sqrt(kappa).                              (KPR7)
```

Actor invariance and orbit transitivity show that every nonidentity Weyl
commutator with `Tbar` has the same norm as the prototype, up to its central
phase.  Moreover

```text
||[Tbar,W_0]||_2<=epsilon_0+2a.                        (KPR8)
```

Applying `(KPR2)` to `Tbar` and then the triangle inequality yields the
dimension-free localization estimate

```text
dist_2(T,P_N')
 <= a+(epsilon_0+2a)/sqrt(2)
 <= epsilon_0/sqrt(2)
    +(1+sqrt(2))epsilon_K/sqrt(kappa).                 (KPR9)
```

The constants do not depend on the Pauli rank, the representation
dimension, or the multiplicity.  Consequently one prototype mixed
commutator really can expose the entire scalable Pauli multiplicity algebra
when accompanied by one uniformly gapped transitive actor packet.

For a decoded Gram deficiency `T=q=E-X^*X`, `(KPR9)` places `q` near the
commutant of the multiplicity Pauli algebra, namely the fixed Fanizza label
factor.  The rank-quantization gap from
`semisimple-trace-charts-cannot-authenticate-proper-fullness` can then
apply after the usual projection exactification.

## What the dual-prefix tower supplies and what it does not

At depth `n`, the dual-prefix Leavitt construction supplies a Pauli packet
of symplectic rank

```text
N=2^n.                                                  (KPR10)
```

Therefore `(KPR1)--(KPR4)` apply exactly at every fixed depth.  The two
Morita branches supply all Weyl coordinates and one common central sign.
They do not supply the actor hypothesis `(KPR5)`: the branch maps are
root-dependent, their images form a central product, and no fixed
word-generated uniformly gapped actor moving one Weyl word through every
nonzero vector is part of the bare Leavitt chart.

This distinction decides the defect-versus-dimension issue.  If transport
of the prototype to depth `n` costs `A_n` relator cells and the available
actor gap is `kappa_n`, the same proof gives an error coefficient of order

```text
A_n/sqrt(kappa_n).                                     (KPR11)
```

Hyperlinear microstates impose no rate relating their defect `delta_k` to
their dimension `d_k`.  Hence any unbounded coefficient in `(KPR11)` leaves
the diagonal escape: choose dimensions so large relative to `delta_k` that
the depth needed to exceed Pauli capacity lies beyond the controlled
scale.  Pointwise convergence at every fixed depth cannot choose a
supercritical depth.

Conversely, a uniform `kappa` and bounded-area exposure of `(KPR6)` remove
that schedule completely through `(KPR9)`.  The remaining construction
problem is therefore exact and narrow:

> make one fixed Gram word actor-invariant at uniform spectral-gap cost,
> and put one nonzero dual-prefix Weyl word in its mixed commutator orbit.

This is not another request for all depthwise commutators.  It is a uniform
Kazhdan--Clifford actor compiler for the dual-prefix multiplicity tower.
Projective Clifford lifts are sufficient: central phases disappear from
conjugation and from commutator norms, so no splitting of the finite
Clifford extension is assumed.
