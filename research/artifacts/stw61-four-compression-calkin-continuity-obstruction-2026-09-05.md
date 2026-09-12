# LXI: four coefficient rotations obstruct a uniform Calkin-continuous threshold upgrade

Date: 2026-09-05. Complete proof, internally reviewed with no unresolved
gap found. This is not external peer review or formal verification.
This rules out one precise extension of the moving-threshold
method. It neither proves nor refutes the unrestricted
maximal-commutator assertion, and does not settle LXI.

## 1. The proposed upgrade and the exact obstruction

The finite-rank-side theorem uses a fixed coefficient
representation and a strongly continuous path of self-adjoint
unitaries V_t from +I to -I. Every compression to a fixed finite
space is norm continuous, so its endpoint sign change forces
a zero eigenvalue.

For p=s_1s_1* in a unital T_2 representation, both sides of p
have infinite-dimensional ranges. A proposed replacement is
to use infinite compressions, with norm continuity at least
after quotienting by compact operators, so that an essential
spectrum or Fredholm argument can replace the finite matrix
crossing.

The following theorem gives an exact limitation on that
proposal. The same threshold path cannot have that continuity
property for every W, even for four constant coefficient
unitaries.

**Theorem.** Let S_1,S_2 be isometries with orthogonal ranges
on an infinite-dimensional Hilbert space H, and suppose

```text
E=I-S_1S_1*-S_2S_2*
```

is compact. This includes the standard Fock representation,
where E is the rank-one vacuum projection. Let V_t, 0<=t<=1,
be self-adjoint unitaries with V_0=I and V_1=-I. Strong
continuity may be assumed, as in a threshold construction,
but is not needed for the implication below.

Define four isometries

```text
R_1=S_1,
R_2=S_2,
R_+=(S_1+S_2)/sqrt(2),
R_i=(S_1+i S_2)/sqrt(2).
```

At least one of the four paths

```text
t |-> [R_j* V_t R_j] in B(H)/K(H),   j in {1,2,+,i},
```

fails to be norm continuous. Each R_j is obtained from S_1
by a fixed coefficient unitary in C*(1,S_1,S_2), explicitly
constructed below.

The theorem concerns one common threshold path and one fixed
coefficient representation. It does not rule out choosing
different paths or representations depending on W.

## 2. Four explicit coefficient unitaries

Let P=S_1S_1*+S_2S_2*. For a scalar two-by-two unitary U,
define

```text
W_U=sum_(a,b=1)^2 S_a U_ab S_b* + E.
```

The first term is a unitary in the corner PB(H)P, with
initial and range projection P; it is orthogonal to E.
Thus W_U is a genuine unitary and

```text
W_U S_1=sum_(a=1)^2 S_a U_a1.
```

Use the four scalar matrices

```text
U_1 = [[1,0],[0,1]],
U_2 = [[0,1],[1,0]],
U_+ = [[1,-1],[1,1]]/sqrt(2),
U_i = [[1,i],[i,1]]/sqrt(2).
```

They give W_(U_j)S_1=R_j and

```text
W_(U_j)(S_1S_1*)W_(U_j)*=R_j R_j*.
```

All four unitaries are images of the identical coefficient
formulas in the universal T_2. In particular, any proposed
argument covering every mixed unitary in C(S^1)*T_2 must
cover these four without requiring any circle letters.

The compression to the original projection range, identified
with H through S_1, is exactly

```text
S_1* W_(U_j)* V_t W_(U_j) S_1 = R_j* V_t R_j.
```

Thus the four paths in the theorem are precisely four of
the compressions arising in the proposed method.

## 3. Polarization reconstructs all corners

Write

```text
A(t)=S_1* V_t S_1,
D(t)=S_2* V_t S_2,
B(t)=S_1* V_t S_2,
B(t)*=S_2* V_t S_1,
M_+(t)=R_+* V_t R_+,
M_i(t)=R_i* V_t R_i.
```

Since V_t is self-adjoint, direct multiplication gives

```text
2M_+ = A+D+B+B*,
2M_i = A+D+iB-iB*.
```

Consequently, with

```text
X=2M_+-A-D,
Y=2M_i-A-D,
```

one has

```text
B=(X-iY)/2,   B*=(X+iY)/2.
```

If the four compression paths are norm continuous modulo
compacts, these formulas make all four corner paths
[S_a* V_t S_b] norm continuous in the Calkin algebra.

Because E is compact, the difference V_t-PV_tP is compact
for every t. Therefore

```text
[V_t]=sum_(a,b=1)^2 [S_a] [S_a* V_t S_b] [S_b*]
```

in the Calkin algebra. The coefficient classes [S_a] are
fixed. Thus continuity of the four compression paths would
make t |-> [V_t] norm continuous.

Equivalently, the compact defect makes [S_1],[S_2] a Cuntz
pair in the quotient, and the four polarized compressions
recover the entire operator class, not merely part of it.

## 4. The endpoint contradiction

Every [V_t] is a self-adjoint unitary, with endpoint values
+1 and -1. There is no norm-continuous path of self-adjoint
unitaries between these endpoints in any nonzero unital
C*-algebra.

Indeed, (1+[V_t])/2 would be a norm-continuous projection
path from 1 to 0. The identity projection is isolated
within the projection space: for every projection Q!=1,

```text
||1-Q||=1.
```

The set of times at which the projection equals 1 is
therefore both open and closed. It contains 0, so by
connectedness it contains the entire interval, contradicting
the endpoint at 1. This contradiction proves the theorem.

No Fredholm hypothesis was required. The obstruction already
arises at the requested continuity level, before assigning
an index or deciding whether an individual compression is
Fredholm.

## 5. Consequences for compact corrections and spectral flow

For every fixed compact-defect Fock representation and
every common threshold path from +I to -I, one of the four
explicit compressed paths cannot be made norm continuous
by adding compact operators: compact perturbations leave
its Calkin class unchanged.

This remains true if one only asks for norm-continuous
Calkin representatives rather than norm continuity of
the original compressions. Polarization would still give
the impossible path of Section 4.

Thus strong continuity of the threshold family cannot be
silently upgraded to the continuity needed for this
particular bounded Fredholm-path strategy. For the usual
bounded self-adjoint spectral-flow framework, see Phillips,
*Self-adjoint Fredholm operators and spectral flow*,
Canad. Math. Bull. 39 (1996), 460--467
([primary paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/CFA9F1362A48E77D9B67212CDCEFA902/S0008439500022359a.pdf/self-adjoint-fredholm-operators-and-spectral-flow.pdf)).
No assertion about every possible definition or use of
spectral flow is intended here; the theorem rules out the
specific Calkin-norm-continuity premise stated in Section 1.

The algebraic proof also works with a proper closed ideal
J in place of K(H), whenever the defect belongs to J:
continuity of all four compressed classes in B(H)/J would
again force a norm-continuous self-adjoint-unitary path
from +1 to -1 in that nonzero quotient.

## 6. Exact remaining possibilities

This is a method obstruction, not a counterexample to
maximal commutator norm. In fact these four coefficient
unitaries themselves lie in classes already known to give
universal commutator norm one. The point is that a single
fixed-representation threshold construction cannot prove
the unrestricted theorem by claiming Calkin-norm continuity
for every compressed path.

The argument does not exclude W-dependent threshold paths,
varying coefficient representations without the fixed
Calkin coefficient classes used above, an appropriate
relative index without the prohibited continuity premise,
or a different topological parameter space. It supplies
no strict universal commutator and no LXI conclusion.

The finite-rank-side theorem remains valid: there only one
chosen projection side is finite dimensional, so its
compression is norm continuous automatically. The present
properly infinite projection problem asks for a property
which, even modulo compacts, is incompatible with the
finite family of coefficient rotations above.

## Internal review

The root reviewer independently checked the explicit scalar
unitary matrices and their coefficient lifts, the exact
compression identities, polarization of both off-diagonal
corners, reconstruction modulo the compact defect, and the
impossible norm-continuous projection path from 1 to 0 in
the Calkin algebra. The review also checked the restriction
to one common threshold path and one fixed representation.
No unresolved mathematical gap was found. This is an internal
review, not external peer review or formal proof verification.
