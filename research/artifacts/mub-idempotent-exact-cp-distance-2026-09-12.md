# Exact UCP distance of the two-masa idempotent

Date: 2026-09-12. This closes the specific UCP-approximation gap listed
in the two channel-rounding frontier claims. It does not settle general
near-idempotent channel rounding or construct a nonhyperlinear group.

## Statement

Let `d>=2`, `tau=Tr/d`, and let `D,C` be maximal abelian unital
subalgebras of `M_d` whose trace-preserving expectations satisfy
`E_D E_C=E_C E_D=E_0`, with `E_0(x)=tau(x)1`.
For `Q=E_D+E_C-E_0`,

```text
inf_(P UCP) ||P-Q||_(infinity->2) = 1/3.                 (1)
```

Here `||T||_(infinity->2)=sup_(||x||_op<=1)||T(x)||_2` and
`||x||_2^2=tau(x*x)`. No symmetry or trace-preservation assumption
is imposed on `P` in the infimum. The minimizing map
`P_*=(id+E_D+E_C)/3` satisfies both additional assumptions.

## Cyclic unitary test family

Write the minimal projections of `D` as `e_0,...,e_(d-1)` and
those of `C` as `f_0,...,f_(d-1)`. For `zeta=exp(2 pi i/d)` put

```text
u_k=sum_j zeta^(kj)e_j,   v_l=sum_j zeta^(lj)f_j.
```

Both are orthonormal unitary bases of their respective masas for the
normalized trace; their nonidentity members have trace zero. Averaging
conjugation by all `u_k` is `E_D`, and averaging conjugation by all
`v_l` is `E_C`. This is the finite geometric-sum identity on the
matrix entries in each masa's defining basis.

Set `w_kl=u_k v_l`. On the axes, `Q(w_k0)=u_k` and
`Q(w_0l)=v_l`. If `k,l!=0`, bimodularity and orthogonality give

```text
E_D(u_k v_l)=u_k E_D(v_l)=0,
E_C(u_k v_l)=E_C(u_k)v_l=0,
tau(u_k v_l)=0,
Q(w_kl)=0.                                             (2)
```

Only unitarity of these test matrices is needed below; there is no
assumption that they form a group or that `P` is diagonal on them.

## The Kraus mass inequality

Take a Kraus representation `P(x)=sum_i a_i* x a_i` with
`sum_i a_i*a_i=1`. In particular `sum_i ||a_i||_2^2=1`.
Define the real overlaps

```text
r_kl=Re tau(w_kl* P(w_kl)),
A=sum_(k!=0) r_k0 + sum_(l!=0) r_0l,
B=sum_(k,l!=0) r_kl,
p_D=sum_i ||E_D(a_i)||_2^2,
p_C=sum_i ||E_C(a_i)||_2^2,
s=sum_i |tau(a_i)|^2.
```

Since `P(1)=1`, `r_00=1`. The cyclic averages just proved give

```text
p_D=(1/d) sum_k r_k0,
p_C=(1/d) sum_l r_0l,
s=(1/d^2) sum_(k,l) r_kl.                              (3)
```

For clarity, the summand for a Kraus operator `a` is
`tau(w* a* w a)`. On averaging the axis `w=u_k`, the conjugated
factor becomes `E_D(a*)`, whose trace pairing with `a` is
`||E_D(a)||_2^2`. For the double average,

```text
(1/d^2) sum_(k,l) v_l* u_k* a* u_k v_l
 = E_C E_D(a*) = tau(a*)1,
```

so its pairing with `a` is `|tau(a)|^2`. This also shows why the
order of the factors in `w_kl` causes no difficulty.

The operator `S=E_D+E_C-E_0` is the orthogonal projection on
`D+C` in `L^2(M_d,tau)`. Hence its complementary Kraus mass is
nonnegative:

```text
0 <= sum_i ||(I-S)(a_i)||_2^2
   = 1-p_D-p_C+s
   = [(d-1)^2-(d-1)A+B]/d^2.                           (4)
```

The last equality uses `p_D+p_C=(2+A)/d` and
`s=(1+A+B)/d^2`. Unitality is the only channel normalization used.

## Sharp lower bound

Let `epsilon=||P-Q||_(infinity->2)`. Each `w_kl` is unitary and
has `L^2` norm one, so Cauchy--Schwarz and (2) imply

```text
r_k0 >= 1-epsilon (k!=0),
r_0l >= 1-epsilon (l!=0),
r_kl <= epsilon (k,l!=0).
```

Thus `A>=2(d-1)(1-epsilon)` and `B<=(d-1)^2 epsilon`.
Substitution into (4), with the direction of the negative coefficient
of `A` respected, yields

```text
0 <= d^2 sum_i ||(I-S)(a_i)||_2^2
  <= (d-1)^2(3epsilon-1).
```

Since `d>=2`, this proves `epsilon>=1/3` for every UCP map.

## Attaining the bound

The map `P_*=(id+E_D+E_C)/3` is a convex combination of three
self-adjoint bistochastic UCP maps. Decompose normalized `L^2` as

```text
C1 direct_sum (D minus C1) direct_sum (C minus C1)
   direct_sum (D+C)^perp.
```

The map
`3(P_*-Q)=id-2E_D-2E_C+3E_0` has eigenvalues `0,-1,-1,+1`
on these four orthogonal summands. Its `2->2` norm is one, so
`||P_*-Q||_(infinity->2)<=1/3`. Every nonidentity `u_k` is a
unitary eigenvector with eigenvalue `-1/3`, proving equality.
This verifies the upper bound on the whole operator unit ball,
not just the finite test family.

## Consequence and scope

The exact idempotent `Q` cannot be approached in mixed norm by UCP
maps, irrespective of growing dimensions, the choice of mutually
unbiased bases, or symmetry assumptions on the approximants. Its small
individual negative Choi eigenvalues do not imply a small mixed-norm
repair. More robustly, any linear map `T` with
`||T-Q||_(infinity->2)<=rho` has distance at least `1/3-rho`
from every UCP map, by the triangle inequality.

The best UCP approximant displayed here has mixed idempotence defect
exactly `2/9`: on the three non-scalar summands its eigenvalues are
`2/3,2/3,1/3`, so `P_*^2-P_*` is `-2/9` on the entire
traceless subspace and zero on scalars. Its `infinity->2` norm is
`2/9`, attained on any traceless unitary. Thus even the sharp repair
does not yield the vanishing-defect family sought by the negative
rounding frontier.

## Literature and provenance check

Repository lexical searches on 2026-09-12 found this exact family in
`bistochastic-near-idempotents-round-dimension-free` and
`bistochastic-channel-rounding-fails`, where mixed-norm UCP
approximability was explicitly left unresolved. The argument above is
self-contained finite-dimensional linear algebra and Kraus calculus.

Related prior work includes Ohno and Petz, *Generalizations of Pauli
channels*, Acta Mathematica Hungarica 124 (2009), 165--177,
[DOI](https://doi.org/10.1007/s10474-009-8171-5),
[full primary preprint](https://arxiv.org/pdf/0812.2668), on complete
positivity for maps diagonal on decompositions into complementary
subalgebras. Its introduction, qubit example, and complementary-unitary
averaging construction are prior art for the ingredients here.
The primary conference paper *Parameter Estimation of Quantum Processes
Using Convex Optimization*, MTNS 2010,
[PDF](https://www.conferences.hu/mtns2010/proceedings/Papers/363_216.pdf),
also gives complementary-subalgebra channel parametrizations and their
CP constraints. These were checked on 2026-09-12.

Those parametrizations are relevant prior art, not a novelty claim for
the framework used here. The conclusion proved here minimizes against
all UCP maps for any pair of orthogonal masas, without requiring a full
decomposition into mutually unbiased masas or a diagonal competitor.
No assertion of publication-level novelty or of the resolution of an
external named open problem is made. No numerical search or local
computation is used as proof evidence.
