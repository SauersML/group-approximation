# STW LXXIX: an index criterion for AF-ideal extensions

Date checked: 2026-09-04 (America/New_York).

## Status and provenance

The current [STW v2](https://arxiv.org/html/2506.10902v2), Problem LXXIX,
asks for a quasidiagonality characterization of finite decomposition rank
among nowhere scattered algebras with finitely many ideals and finite
nuclear dimension. The [arXiv record](https://arxiv.org/abs/2506.10902)
identifies v2 as the 2026-05-08 revision. This check found no resolution of
the full problem. What follows is a restricted positive answer, obtained
by combining existing theorems, and a correction to this repository's
factorwise proposal. It is not presented as a novel solution of LXXIX.

The decisive primary sources are:

* C. L. Schochet, [The fine structure of the Kasparov groups III: Relative
  quasidiagonality](https://jot.theta.ro/jot/archive/2005-053-001/2005-053-001-004.pdf),
  J. Operator Theory 53 (2005), 91–117: p. 96, Proposition 2.1 and
  Theorem 3.5 (p. 107).
* E. Kirchberg and W. Winter, [Covering dimension and
  quasidiagonality](https://arxiv.org/pdf/math/0207164v1): Theorem 4.4,
  Proposition 5.1 and Examples 6.1(i–ii), in the **v1 numbering** read here.
  Later versions use different numbering.
* W. Winter and J. Zacharias, [The nuclear dimension of
  C*-algebras](https://arxiv.org/pdf/0903.4914), Proposition 2.9.
* E. Park, [Toeplitz algebras and extensions of irrational rotation
  algebras](https://faculty.tcu.edu/epark/papers/Toeplitz_CMB.pdf),
  Canad. Math. Bull. 48 (2005), 607–613, Theorem 2 and Proposition 5.
* H. Thiel and E. Vilalta, [Nowhere scattered
  C*-algebras](https://arxiv.org/abs/2112.09877): characterization by the
  absence of nonzero elementary ideal-quotients.

The full Park article, including its index computations, was checked:
the rotation extension below is already in that paper. Schochet's
concrete-extension theorem, not just the abstract statement about
KK-classes, is the input used below. These are conceptual published
results; there is no computational witness, source-code supplement or
exhaustion claim here. Repository searches for the rotation extension,
Schochet relative quasidiagonality, and the factorwise criterion found
no existing node for this dichotomy.

## 1. The restricted characterization

Let `B` be a separable infinite-dimensional simple unital AF algebra with
totally ordered `K_0(B)`, and `D` a separable simple unital non-elementary
nuclear UCT algebra. Assume only that `K_0(D)` is torsion-free and
`d=dr(D)<infinity`; `K_1(D)` is unrestricted. Consider any unital essential
extension

```text
0 -> J=K tensor B --i--> E --q--> D -> 0.                 (1)
```

Write `delta:K_1(D)->K_0(B)` for the index boundary. Then

```text
delta=0
  iff J has an E-quasicentral approximate unit of projections
  iff dr(E)<infinity
  iff E is strongly quasidiagonal
  iff E is quasidiagonal
  iff E is stably finite.                               (2)
```

In the zero-index case `dr(E)=d`. Otherwise `dr(E)=infinity`.
In all cases `dim_nuc(E)<=d+1`.

### Zero index gives relative quasidiagonality

Finite decomposition rank makes `D` quasidiagonal. Since `B` has an
approximate unit of projections, the relative-quasidiagonality observation
on Schochet's p. 96 and Proposition 2.1 apply to `D,B`. Essentiality in
(1) identifies `E` faithfully with its canonical image in `M(J)`.
Theorem 3.5 identifies a quasicentral projection approximate unit for that
image when the K-theory boundary vanishes and the remaining UCT extension
class is pure. Since `K_1(B)=0`, the second boundary vanishes and the
relevant degree-zero extension group is just
`Ext^1(K_0(D),K_0(B))`. Every such group extension is pure: if
`0->H->G->K_0(D)->0` is exact and `nx` lies in `H`, torsion-freeness of
the quotient forces `x` into `H`, hence `H intersect nG=nH`. This verifies
the purity condition without a restriction on `K_1(D)`. Thus `delta=0`
supplies the required approximate unit in the actual ideal `J`.

This does **not** claim that the extension splits. Torsion-free groups
need not be free, and pure extension classes need not vanish.

By the Kirchberg–Winter projectional extension maximum,

```text
dr(E)=max(dr(J),dr(D))=max(0,d)=d.                       (3)
```

Their finite-decomposition-rank theorem supplies strong quasidiagonality,
which implies quasidiagonality and hence stable finiteness.

### Stable finiteness forces zero index

By hypothesis `K_0(B)` is totally ordered. If `delta` is nonzero, its
image contains a strictly positive
element `g` (replace an element by its negative if necessary).
There is a nonzero projection `p` in a matrix algebra over `J` with
`[p]=g`. Exactness in (1) gives `i_*(g)=0`.

Because `E` is unital, `K_0(E)` is the Grothendieck group of `V(E)`.
Thus `[p]=0` in `K_0(E)` yields a projection `r` in a matrix algebra over
`E` with

```text
p direct_sum r  ~  0 direct_sum r.                      (4)
```

The right-hand projection is a proper subprojection of the left-hand
one, since `p` is nonzero. Equation (4) therefore exhibits an infinite
projection in a matrix algebra over `E`. This contradicts stable
finiteness. It proves the last-to-first implication in (2); the other
implications were proved above. It also proves that **any** nonzero index
forces infinite decomposition rank, rather than merely obstructing the
specific approximation construction in (3).

The total order is essential to this argument: a general ordered
dimension group can have a nonzero subgroup containing no nonzero
positive element. No such subgroup exists in a totally ordered group.
In particular, every UHF algebra qualifies, since its K-zero group has
the usual order inherited from the rationals.

### Membership in the LXXIX class

The ideal `J` is simple. Essentiality implies that every nonzero ideal
of `E` meets `J` nontrivially and therefore contains it. Since `D` is
simple, the full ideal lattice is precisely `0<J<E`. The two simple
factors are non-elementary: `D` by assumption and `J` because its
full simple unital AF corner is infinite-dimensional and has no minimal
projections. No nonzero ideal-quotient is elementary; `E` itself is not
simple. The nowhere-scattered characterization consequently applies.

Nuclearity passes through the extension. The general nuclear-dimension
extension estimate gives

```text
dim_nuc(E)<=dim_nuc(J)+dim_nuc(D)+1<=0+d+1.              (5)
```

There is no appeal here to the open maximum formula in Problem LXXXII.

## 2. A matched pair inside this class

Fix irrational `theta`, put `U=M_(2^infinity)` and `D=A_theta tensor U`.
The irrational rotation algebra is AT. Tensoring its circle-matrix
inductive system with the matrix stages of `U` leaves an AT system, so
`dr(D)<=1`. Its K-groups are

```text
K_0(D)=Z[1/2]^2,       K_1(D)=Z[1/2]^2,                 (6)
```

as follows directly by taking direct limits of the matrix-stage K-groups
of `A_theta`. In particular `D` is not AF, and `dr(D)=dim_nuc(D)=1`.
It is simple, unital, nuclear, UCT and monotracial.

### Nonzero-index member

On `l2(N)` define

```text
S e_n=e_(n+1),       V e_n=exp(2 pi i n theta)e_n,
T_theta=C*(S,V).
```

Then `VS=exp(2 pi i theta)SV` and `P=1-SS*` is the rank-one
projection onto `e_0`. The elements `S^i P (S*)^j` give all matrix units,
so `K` is contained in `T_theta`. It is essential because the only
bounded operator annihilating all rank-one operators is zero.
Modulo `K`, both generators are unitaries satisfying the irrational
rotation relation. They generate the quotient. Simplicity of `A_theta`
makes this nonzero unital quotient representation injective. Hence

```text
0 -> K -> T_theta -> A_theta -> 0.                      (7)
```

This is Park's extension in the Fourier basis. Its index on the two
generators is `(-1,0)`: `S` has zero kernel and one-dimensional cokernel,
whereas `V` is already unitary. Set `E_1=T_theta tensor U`. Exactness and
matrix-stage naturality turn the index into

```text
delta_1:Z[1/2]^2 -> Z[1/2],       (x,y) |-> -x.         (8)
```

Essentiality survives tensoring. Explicitly, if a positive element `x`
annihilates `K tensor U`, apply the faithful slice `id tensor tau_U`:
its image annihilates `K`, hence is zero; faithfulness makes `x=0`.
Applying this to `x*x` proves that the annihilator ideal is zero.

The theorem gives `dr(E_1)=infinity` and `dim_nuc(E_1)<=2`.
The proper isometry `S tensor 1` independently checks the negative
conclusion. Quotient monotonicity gives `dim_nuc(E_1)>=1`. No exact
nuclear dimension for this member is claimed.

### Zero-index member

Choose a faithful unital quasidiagonal representation
`rho:A_theta->B(H)` with `H` separable infinite-dimensional. Its
intersection with `K(H)` is zero: the preimage of that intersection is
an ideal of the simple `A_theta`, and cannot be all of it because the
represented unit is not compact. Put

```text
F_0=K(H)+rho(A_theta),       E_0=F_0 tensor U.           (9)
```

The sum in (9) is closed: it is the inverse image under the Calkin map
of the closed image of `A_theta`. Its extension by `K(H)` splits by
`rho`, and therefore its index vanishes. Tensoring preserves the
splitting and, by the preceding slice argument, essentiality. The
endpoints of its extension are exactly those for `E_1`.
The theorem gives `dr(E_0)=1`; quotient monotonicity and
`dim_nuc<=dr` give `dim_nuc(E_0)=1`.

One can also see its projectional approximate unit without Schochet:
finite-rank projections witnessing quasidiagonality of `rho` are
quasicentral in `F_0`; their tensors with `1_U` work in `E_0`.

### The traces also agree

Every bounded positive trace on `K tensor U` vanishes. For the equivalent
orthogonal projections `e_nn tensor 1`, boundedness on their finite sums
forces their common trace to be zero. Their increasing finite sums form
an approximate unit, so the trace vanishes on the entire ideal.

Consequently every tracial state of either `E_i` factors through `D`.
Conversely the unique tracial state of `D` pulls back to one on `E_i`.
Both middle algebras thus have the same singleton tracial state simplex,
with trace kernel exactly their unique nonzero proper ideal. They do
not have identical filtered K-theory: (8) is precisely information that
the composition factors and trace simplex omit.

## 3. Correction and remaining problem

Both simple composition factors in each example are strongly
quasidiagonal with decomposition ranks `0,1`. Their isomorphism types,
the three-element ideal chain, and the tracial state simplexes agree.
The middle decomposition ranks do not. Thus the factorwise strong-QD
proposal in the earlier LXXIX node is false even in this restricted
setting; the index must be taken into account. The separate assertion
about **all** subquotients would include the middle algebra and is not
refuted by this example.

For the AF-ideal class of Section 1, (2) is the required exact
quasidiagonality criterion. Extending it to the whole LXXIX class remains
open here. The proof uses an AF ideal, total order on its K-group, UCT
and torsion-free quotient K-zero, and already finite decomposition
rank of the quotient. None of these may be silently dropped. In
particular, finite nuclear dimension plus quasidiagonality alone has
not been substituted for the finite-decomposition-rank hypothesis.

This is a proof from published mathematics, not a Lean formalization.
Cairn checks certify graph syntax and dependencies, not the analytic
theorems cited in this artifact.

Validation on MSI, 2026-09-05: the isolated LXXIX subgraph (three claims,
two routes) passes `check --changed` and `preview`. A separate duplicate
check against the full imported research graph finds no candidates for
the two new claims. The full-graph check fails on 37 existing source
errors in other nodes; no full-graph green result is claimed.
