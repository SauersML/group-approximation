# LXI: a mixed semicircular obstruction which escapes every proper coefficient corner

Date: 2026-09-05. Complete proof, internally reviewed with no unresolved
gap found. This is not external peer review or formal verification.
No solution of LXI is claimed.

## 1. The theorem

Let C=C(S^1)*_C T_2 be the full unital free product. Write z for
the universal circle unitary, s_1,s_2 for the Toeplitz isometries,
and

```text
p=s_1s_1*,   p_2=s_2s_2*,   e=1-p-p_2.
```

Define the genuinely mixed self-adjoint elements

```text
h_i=z s_i+s_i* z*,   i=1,2,
H=C*(1,h_1,h_2) inside C.
```

**Theorem.** For every unitary W in H,

```text
||[z,WpW*]||=1.
```

The statement covers arbitrary unitaries in this noncommutative
generated algebra, including functional calculus of sums and
products of h_1,h_2. It is not restricted to one exponential or
an alternating word in factor unitaries.

There is also an explicit family demonstrating that this theorem
goes beyond the fixed-corner obstruction. For every real t!=0 put

```text
W_t=exp(i t h_1),   q_t=W_t p W_t*.
```

Then:

1. No proper projection P in the Toeplitz coefficient factor
   contains q_t. More generally, there are no such P and no
   scalar continuous unitary function f on S^1 for which
   q_t<=f(z)P f(z)*.
2. All three compressions e q_t e, p q_t p, and p_2 q_t p_2
   are nonzero. Thus the projection meets the Toeplitz defect
   and both generating range projections.
3. Nevertheless ||[z,q_t]||=1, and q_t and 1-q_t are properly
   infinite and full.

The norm test below keeps a nonzero Toeplitz defect. It does not
pass to a Cuntz quotient, use an MF coefficient representation,
or infer a universal upper bound from a quotient norm.

## 2. A left-right Fock representation

Let F be the full Fock space over C^2. Its orthonormal basis is
indexed by finite words in {1,2}, including the empty word Omega.
Let L_i prepend the letter i and R_i append it. These are
isometries with pairwise orthogonal ranges, and

```text
1-L_1L_1*-L_2L_2*=E_Omega,
```

where E_Omega is the rank-one vacuum projection. The left-right
relations on the word basis are

```text
[L_i,R_j]=[L_i*,R_j*]=0,
[L_i*,R_j]=delta_ij E_Omega,
[L_i,R_j*]=-delta_ij E_Omega.
```

The two vacuum errors cancel, so

```text
[L_i+L_i*, R_j+R_j*]=0   for all i,j.
```

Let K=R_1+R_1*. Define the Borel function g by g(x)=1 for x>=0
and g(x)=-1 for x<0, and let

```text
V=g(K).
```

This is a self-adjoint unitary in B(F). Since every L_i+L_i*
commutes with the bounded self-adjoint K, it commutes with the
spectral projections of K and with V. Borel functional calculus
is used only to construct a Hilbert-space representation; there
is no assertion that V belongs to the Toeplitz C*-algebra.

We will use the exact vacuum properties

```text
<V Omega,Omega>=0,   L_1L_1* V Omega=V Omega.
```

Here is a direct verification. The reducing subspace generated
from Omega by K is the span of the words 1^n, n>=0. In that
basis K is S+S* on l^2(N_0), where S is the unilateral shift.
The sine transform sending the n-th basis vector to
sqrt(2/pi) sin((n+1)theta), 0<theta<pi, turns S+S* into
multiplication by 2 cos(theta). Consequently

```text
<V Omega,Omega>
  =(2/pi) integral_0^pi g(2 cos(theta)) sin(theta)^2 dtheta
  =0.
```

The value at theta=pi/2 has measure zero. Since V Omega belongs
to the span of the words 1^n and has zero vacuum coefficient, it
belongs to the range of L_1. This proves both properties. In
particular, with P_1=L_1L_1*,

```text
[V,P_1]Omega=-V Omega,
||[V,P_1]||=1.
```

The upper bound follows from the general unitary-projection
commutator bound; the displayed vector proves the lower bound.

The creation-operator framework and its semicircular spectral
law are classical. See Nica--Speicher, *Lectures on the
Combinatorics of Free Probability*, Lecture 7, Definitions 7.13
and Proposition 7.16 in the
[author-hosted text](https://www.math.uni-sb.de/ag/speicher/publikationen/Nica-Speicher.pdf).
The specific commutator calculation and spectral facts needed
here have been proved directly above.

## 3. Proof of the maximal-norm theorem

The operators V L_1,V L_2 are isometries with orthogonal ranges.
Therefore the universal properties of T_2 and the full free
product give a unital representation pi:C -> B(F) with

```text
pi(z)=V,   pi(s_i)=V L_i.
```

The Toeplitz defect has image

```text
pi(e)=V E_Omega V,
```

which is a nonzero rank-one projection. Both generating
proper-infinite witnesses survive: pi(s_i) are actual isometries
with orthogonal ranges and this nonzero common defect.

Since V=V*=V^(-1),

```text
pi(h_i)=L_i+L_i*,
pi(p)=V P_1 V.
```

Fix W in U(H) and write Y=pi(W). Section 2 shows that V commutes
with each generator pi(h_i), hence with Y. Thus conjugating the
commutator by Y, and then by V, gives

```text
||[V,pi(WpW*)]||
  =||[V,V P_1 V]||
  =||[V,P_1]||
  =1.
```

Contractivity of pi implies ||[z,WpW*]||>=1. Conversely, for a
unitary u and projection q, the commutator in the q decomposition
has the off-diagonal contraction blocks -qu(1-q) and (1-q)uq.
Its norm is at most one. This proves the theorem.

The representation is selected so that the image of the entire
mixed algebra H commutes with V. It does not make the image of
p commute with V. The surviving vacuum defect supplies the
vector which detects their maximal commutator.

## 4. Scalar evaluations and escape from every coefficient corner

We next prove the asserted support properties of q_t. These
arguments use a different, standard representation: send z to
the scalar 1 or -1 and represent T_2 by its faithful left Fock
representation s_i |-> L_i.

For clarity, faithfulness here can be checked using the gauge
action. The Fock representation intertwines the gauge action
with the length grading. The degree-zero core is the increasing
union of the finite-dimensional algebras with blocks

```text
M_1 direct_sum M_2 direct_sum ... direct_sum M_(2^(n-1))
    direct_sum M_(2^n).
```

The first blocks act on the exact word-length subspaces below n,
and the last block acts on prefixes of length n. Fock represents
every block faithfully. Averaging the gauge action is a faithful
conditional expectation, so faithfulness on this core proves
faithfulness on T_2.

Write J_0=S+S* on l^2(N_0), and let K_0=ker L_1*. The word
decomposition by the maximal initial string of 1's gives

```text
F = l^2(N_0) tensor K_0,
L_1 = S tensor 1,
P_1 = (1-E_0) tensor 1.
```

Here E_0 is the projection onto the initial basis vector delta_0.
Under z |-> +/-1 the projection q_t is represented by

```text
Q_+ = (1-E_(xi_+)) tensor 1,
Q_- = (1-E_(xi_-)) tensor 1,
xi_+ = exp(i t J_0)delta_0,
xi_- = exp(-i t J_0)delta_0.
```

For t!=0 the unit vectors xi_+ and xi_- are not collinear. If
they were, the sine-transform description from Section 2 would
force exp(2 i t x) to be constant almost everywhere for the
vacuum spectral measure of J_0. That measure has positive
density throughout (-2,2), so this is impossible for nonzero t.

It follows that the subspaces xi_+ tensor K_0 and
xi_- tensor K_0 have zero intersection. Equivalently, the join
of Q_+ and Q_- in B(F) is the identity.

Suppose q_t<=P for a coefficient projection P in T_2. The two
scalar evaluations give Q_+<=rho(P) and Q_-<=rho(P), hence
rho(P)=1. Faithfulness of rho implies P=1. This excludes every
proper coefficient projection, with no need to specify one in
advance.

More generally, if q_t<=f(z)P f(z)* for a continuous unitary
function f:S^1 -> S^1, scalar evaluation at +/-1 turns f(z)
into a scalar unitary. The same two inequalities follow and
again force P=1. This includes all integer-power translates
z^k P z^(-k) as well.

## 5. The projection meets the defect and both ranges

Let

```text
psi(t)=<exp(i t J_0)delta_0,delta_0>.
```

For every t!=0, |psi(t)|<1. Indeed, equality in the triangle
inequality for the integral of the unit-modulus function
exp(i t x) would make that function constant almost everywhere
for the same full-interval spectral measure, which is impossible.

The multiplicity space K_0 is the orthogonal sum of the vacuum
line and the words beginning with 2. Thus in the decomposition
of Section 4,

```text
rho(e)=E_0 tensor E_Omega,
rho(p_2)=E_0 tensor (1-E_Omega).
```

Using the scalar evaluation z |-> 1 gives

```text
rho(e) Q_+ rho(e)=(1-|psi(t)|^2)rho(e) != 0,
rho(p_2) Q_+ rho(p_2)=(1-|psi(t)|^2)rho(p_2) != 0.
```

Also P_1 Q_+ P_1 is nonzero: in the l^2(N_0) factor there is
a nonzero vector orthogonal to both delta_0 and xi_+, on which
P_1 and Q_+ are both the identity. Nonzero represented
compressions imply

```text
e q_t e != 0,   p q_t p != 0,   p_2 q_t p_2 != 0
```

in the original full free product. This proves the claimed
defect and range support properties for every t!=0.

Finally, q_t is a unitary conjugate of p. The projection p is
equivalent to the properly infinite unit, and 1-p contains the
equivalent copy s_2s_2*. Both p and 1-p, and hence both q_t
and 1-q_t, are properly infinite and full.

## 6. Exact progress and remaining boundary

This supplies a broad new obstruction for unitaries in the
specific mixed algebra C*(1,zs_1+s_1*z*,zs_2+s_2*z*). It also
provides the explicit family q_t escaping every fixed proper
Toeplitz corner and its scalar functional translates. Its
nonzero overlap with the defect and both range projections
shows that merely moving into all three regions does not
overcome the norm obstruction.

The proof uses a representation of the original full free
product with a nonzero Toeplitz defect and gives an exact lower
bound. Thus it avoids the loss of norm in the preceding Bell
Cuntz-quotient test. It is independent of the MF obstruction
and of the fixed-corner hypothesis.

As in the preceding artifacts, full-free-product inclusion
transfers the same norm conclusion to C*(v,T_2) inside A*T_2
whenever v is a full-spectrum unitary of A. The usual BRR
strict-commutator criterion therefore cannot be met by the
conjugates described here in that ambient application.
The inclusion theorem used here is Armstrong--Dykema--Exel--Li,
*On embeddings of full amalgamated free product C*-algebras*,
Proposition 2.2, with the common amalgamating algebra C unchanged
([primary paper](https://arxiv.org/pdf/math/0210448)).

The theorem does not assert maximal norm for every unitary
of C(S^1)*T_2. In particular, a general mixed unitary need not
belong to the self-adjoint generated algebra H used above,
and its image need not commute with the chosen V. No strict
universal commutator, null-homotopy, surviving free-envelope
component, or solution of STW LXI is claimed.

## Internal review

The root reviewer independently checked the complete argument,
including the cancellation of the left-right vacuum commutators,
the sign functional calculus and exact vacuum vector, the
representation preserving a nonzero Toeplitz defect, faithfulness
of the standard Fock scalar tests, and the Wold-decomposition
proofs of corner escape and all three nonzero compressions.
No unresolved mathematical gap was found. This is an internal
review, not external peer review or formal proof verification.
