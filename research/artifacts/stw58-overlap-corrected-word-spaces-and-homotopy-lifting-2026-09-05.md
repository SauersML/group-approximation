# STW LVIII: overlap-corrected word spaces and global homotopy lifting

Date: 2026-09-05. **Proved relative statements, internally reviewed.**
The root review checked the transfer action, low-degree component
terms in the associated-bundle sequence, and the equivariant append
operation. No external peer review or formal verification is claimed.
This computes a correction space and proves a global lifting operation.
It does not prove K-stability of simple finite pure algebras.

## 1. Setup and the bounded conclusion

Let \(B\) be unital, and let \(C_0,C_1\subset B\) be full
hereditary subalgebras with a full hereditary subalgebra
\(C\subset C_0\cap C_1\). Put
\[
H_i=U_B(C_i)=\{u\in U(B):u-1\in C_i\},\qquad H=U_B(C).
\]
Fix \(d\ge1\). Assume the canonical maps
\[
\pi_j(H_i)\longrightarrow K_{j+1}(B),\qquad
\pi_j(H)\longrightarrow K_{j+1}(B)
\tag{1.1}
\]
are isomorphisms for \(0\le j\le d\). In degree zero the notation
means the component group. These assumptions hold for the
dimension-drop pieces in the preceding
[local-factorization artifact](stw58-local-factorization-and-overlap-cancellation-2026-09-05.md)
when their matrix sizes are at least \(d+2\), their coefficient
algebras have stable rank one, and the overlap is nonzero.

For each finite endpoint-word pattern we construct an explicit
space \(Q\) of factorizations with overlap correction data.
Its multiplication map
\[
q:Q\longrightarrow U(B)
\]
has the following proved properties:

- Stabilization after \(q\) induces an isomorphism
  \(\pi_j(Q)\cong K_{j+1}(B)\) for \(0\le j\le d\).
  Thus overlap correction removes the entire unavoidable
  K-theoretic balancing part of the word space.
- If the endpoint pieces come from the positive hereditary cover
  in the local-factorization theorem, any compactly parameterized
  homotopy in \(U(B)\) with a given initial lift to \(Q\) lifts
  after finitely many fixed identity-valued word blocks are added.
  The lift preserves stationary subfamilies exactly.

The remaining issue is the connectivity of the fiber of \(q\)
after these overlap corrections. The two conclusions above do
not assert that this fiber is connected or highly connected.

## 2. Why the raw multiplication fiber has extra homotopy

Choose a word pattern
\(\epsilon=(\epsilon_1,\ldots,\epsilon_l)\in\{0,1\}^l\),
\(l\ge2\), and set
\[
P_\epsilon=\prod_{\nu=1}^l H_{\epsilon_\nu},\qquad
m_\epsilon(g_1,\ldots,g_l)=g_1\cdots g_l.
\]
Let \(F_\epsilon=m_\epsilon^{-1}(1)\), based at the identity tuple.
There is an explicit map
\[
H^{l-1}\longrightarrow F_\epsilon,\qquad
(\eta_1,\ldots,\eta_{l-1})\longmapsto
(\eta_1,\eta_1^{-1}\eta_2,\ldots,
 \eta_{l-2}^{-1}\eta_{l-1},\eta_{l-1}^{-1}).
\tag{2.1}
\]
In the range (1.1), composition with the coordinate maps to
\(P_\epsilon\) induces
\[
\Delta:K_{j+1}(B)^{l-1}\longrightarrow K_{j+1}(B)^l,
\]
\[
\Delta(a_1,\ldots,a_{l-1})
=(a_1,-a_1+a_2,\ldots,-a_{l-2}+a_{l-1},-a_{l-1}).
\tag{2.2}
\]
Taking the first \(l-1\) prefix sums is a left inverse.
Consequently (2.1) is split injective on every \(\pi_j\),
\(1\le j\le d\). For \(j\ge2\) its image is a direct summand.
In degree one it is a group retract; no abelianity of the
whole fundamental group of the raw fiber is presumed.

Thus the raw fiber cannot be highly connected merely because
the matrix sizes increase. For example, a nonzero \(K_0(B)\)
already gives nontrivial fundamental groups in these fibers.
This does not refute stable-range gluing: these are precisely
the balancing classes which should first be removed.

## 3. The overlap-transfer action

There is a free right action of \(H^{l-1}\) on \(P_\epsilon\):
\[
(g_1,\ldots,g_l)\cdot(\eta_1,\ldots,\eta_{l-1})
=
(g_1\eta_1,\eta_1^{-1}g_2\eta_2,\ldots,
 \eta_{l-2}^{-1}g_{l-1}\eta_{l-1},
 \eta_{l-1}^{-1}g_l).
\tag{3.1}
\]
All expressions remain in the indicated endpoint groups because
\(H\) lies in both. The action is free by induction from the first
coordinate, and the product \(g_1\cdots g_l\) is invariant.

Let \(E(H^{l-1})\) be a contractible free space for this group and
form the homotopy quotient
\[
Q_\epsilon=P_\epsilon//H^{l-1}
 =E(H^{l-1})\times_{H^{l-1}}P_\epsilon.
\tag{3.2}
\]
One may use the usual numerable universal principal bundle.
We use this homotopy quotient rather than presume that an
ordinary orbit space has a locally trivial quotient map.
The invariant product defines a continuous map
\[
q_\epsilon:Q_\epsilon\longrightarrow U(B).
\tag{3.3}
\]
The basepoint is represented by a chosen point of \(E(H^{l-1})\)
and the identity word.

The associated-bundle fibration is
\[
P_\epsilon\longrightarrow Q_\epsilon
 \longrightarrow B(H^{l-1}).
\tag{3.4}
\]
Equivalently, its long exact sequence contains
\[
\pi_j(H^{l-1})\longrightarrow\pi_j(P_\epsilon)
 \longrightarrow\pi_j(Q_\epsilon)
 \longrightarrow\pi_{j-1}(H^{l-1})
 \longrightarrow\pi_{j-1}(P_\epsilon).
\tag{3.5}
\]
The first and last maps are the orbit maps, up to a harmless
common sign convention, and hence are (2.2) under (1.1).

## 4. Exact stable-range topology after correction

**Theorem 4.1.** Under (1.1), the composite of (3.3) with
unitary stabilization induces isomorphisms
\[
\pi_j(Q_\epsilon)\ \xrightarrow{\ \cong\ }\ K_{j+1}(B),
\qquad 0\le j\le d.
\tag{4.1}
\]

**Proof.** For \(j\ge2\), both orbit maps appearing in (3.5)
are injective, since \(\Delta\) is injective. Thus
\[
\pi_j(Q_\epsilon)\cong
\operatorname{coker}\bigl(\Delta:
K_{j+1}(B)^{l-1}\to K_{j+1}(B)^l\bigr).
\]
The coordinate sum identifies this cokernel with \(K_{j+1}(B)\).
Multiplication followed by stabilization induces exactly that
sum, proving (4.1) with its asserted canonical map.

For \(j=1\), the last map in (3.5) is the injective difference
map on component groups
\[
K_1(B)^{l-1}\longrightarrow K_1(B)^l.
\]
The connecting map from \(\pi_1(Q_\epsilon)\) therefore has
trivial image. Hence \(\pi_1(P_\epsilon)\to\pi_1(Q_\epsilon)\)
is surjective, with kernel the image of \(\pi_1(H^{l-1})\).
Its quotient is the same coordinate-sum cokernel
\(K_0(B)\). In particular this fundamental group is abelian;
that conclusion follows from the calculation.

Finally, the components of the homotopy quotient are the
orbits of the components of \(P_\epsilon\) under
\(\pi_0(H^{l-1})\). Equation (3.1) gives the difference action
on \(K_1(B)^l\), so the orbit set identifies canonically with
\(K_1(B)\) by the coordinate sum. This also proves the
degree-zero assertion. \(\square\)

This is not an assertion about the homotopy groups of \(U(B)\).
It computes the actual overlap-corrected domain of its
multiplication map. In particular it cannot be used to conclude
that \(q_\epsilon\) itself induces an isomorphism.

## 5. A precise global lifting operation

For this section additionally suppose
\[
h_0+h_1=1,\qquad C_i=\operatorname{Her}(h_i),\qquad
C=\operatorname{Her}(h_0h_1),
\]
and \(h_0h_1\) is full. The local-factorization theorem provides
a fixed endpoint-word pattern \(\lambda\), a neighborhood
\(V\) of \(1\) in \(U(B)\), and a continuous map
\[
S:V\longrightarrow P_\lambda,\qquad m_\lambda S(u)=u.
\tag{5.1}
\]
To obtain (5.1), expand each fixed conjugate
\(v\exp(ia(u))v^*\) into its three endpoint letters.
The tuple \(w_0=S(1)\) has product \(1\), though its fixed
conjugating letters need not individually be \(1\).
It is connected to the identity tuple through words of product
\(1\): contract every fixed \(v\) inside its endpoint group,
keeping the middle letter \(1\).

Appending \(w_0\) will be called fixed identity-valued padding.
It changes neither the represented unitary nor its homotopy class.

**Theorem 5.1 (compact homotopy lifting after finite padding).**
Let \(Y\) be compact and let
\[
G:Y\times[0,1]\longrightarrow U(B)
\]
be continuous. Suppose a continuous
\(f_0:Y\to Q_\epsilon\) satisfies
\(q_\epsilon f_0(y)=G(y,0)\).
Then there are a finite integer \(s\), the enlarged word pattern
\(\epsilon'=\epsilon\lambda^s\), and a continuous map
\[
\widetilde G:Y\times[0,1]\longrightarrow Q_{\epsilon'}
\]
whose product is \(G\) and whose initial value is \(f_0\)
with \(s\) fixed blocks \(w_0\) appended.

If \(G(y,t)\) is independent of \(t\) for \(y\) in any specified
subset \(Y_0\), then \(\widetilde G(y,t)\) equals that padded
initial lift for every \(y\in Y_0\) and every \(t\).

**Proof.** Choose a subdivision
\(0=t_0<t_1<\cdots<t_s=1\) such that
\[
G(y,t_{j-1})^*G(y,t)\in V
\]
for all \(y\in Y\) and \(t\in[t_{j-1},t_j]\).
Such a subdivision exists by uniform continuity in the interval
variable, uniformly over the compact space \(Y\).

Let \(r_j(t)\) equal \(t_{j-1}\) before that interval, \(t\)
on it, and \(t_j\) after it, and put
\[
d_j(y,t)=G(y,t_{j-1})^*G(y,r_j(t)).
\tag{5.2}
\]
Each \(d_j\) belongs to \(V\); its initial value is \(1\).
Noncommutative telescoping, in the displayed order, gives
\[
G(y,t)=G(y,0)\prod_{j=1}^s d_j(y,t).
\tag{5.3}
\]
Append the continuous word blocks
\(S(d_1(y,t)),\ldots,S(d_s(y,t))\) to the lift \(f_0(y)\).

This operation is well defined on the homotopy quotient, not
only on tuples with a globally chosen representative.
Indeed appending words gives an equivariant map
\[
P_\epsilon\times P_{\lambda^s}
 \longrightarrow P_{\epsilon'}
\]
for the original overlap-transfer group \(H^{l-1}\), included
as the first coordinates of the enlarged transfer group.
The other transfer coordinates are \(1\).
Choose compatible models
\(E(H^a)=(EH)^a\); appending fixed points in the new \(EH\)
coordinates then induces a continuous map
\[
Q_\epsilon\times P_{\lambda^s}\longrightarrow Q_{\epsilon'}.
\]
It is invariant under every change of representative of \(f_0\).
This constructs \(\widetilde G\), and (5.3) proves its product
is \(G\). At \(t=0\) each new block is \(S(1)=w_0\).
On a stationary subfamily every \(d_j\) is constantly \(1\),
which proves the relative assertion. \(\square\)

This theorem is a global statement for an arbitrary compact
parameter space and a whole homotopy, with exact initial and
stationary conditions. It is stronger than pointwise generation
of the identity component. It does not require stable nullity,
and it never transports a matrix-algebra homotopy into \(B\).

We make no assertion here that a chosen direct limit of the
word spaces is a Serre fibration. The finite-padding statement
above is the exact lifting property proved and used.

## 6. The residual problem is a fiber problem, not K-balancing

Theorem 4.1 removes the raw balancing homotopy detected by
(2.1). Theorem 5.1 permits continuation of correction data
along any already supplied homotopy in \(U(B)\).
Neither supplies an initial lift of an arbitrary sphere map.

For example, a loop in \(U(B)\) can be lifted as a path starting
at an identity-valued corrected word, after finite padding.
Its endpoint is another point in the fiber of the corrected
multiplication map over \(1\). To obtain a closed lift one still
needs a path in that corrected fiber joining the endpoint back
to the initial point. Raw overlap transfers have already been
included in \(Q\); their K-theory does not prove the existence
of this remaining fiber path.

Likewise, lifting maps on the two hemispheres of a higher
sphere leaves a transition problem in the corrected fiber on
the equator. Having the right stable homotopy groups for \(Q\)
does not imply connectivity of that fiber.

A stabilized nullhomotopy lies in \(U(M_m(B))\). Theorem 5.1
applied there stays there. It gives no homotopy in \(U(B)\),
so it cannot close this residual gap by descent.

Thus no unconditional global case \(k=1\) or \(k=2\) of LVIII
is asserted. The new rigorous results are the full stable-range
calculation of the overlap-corrected word space and compact
homotopy lifting after finitely many fixed identity-valued blocks.

## Sources and dependence

- The bounded local factorization and the matrix stable-range
  input are proved in
  [the preceding artifact](stw58-local-factorization-and-overlap-cancellation-2026-09-05.md).
- M. A. Rieffel, *The homotopy groups of the unitary groups of
  non-commutative tori*, J. Operator Theory 17 (1987), 237–254:
  [original paper](https://jot.theta.ro/jot/archive/1987-017-002/1987-017-002-005.pdf).
  The stable-rank-one consequence used is only the explicitly
  bounded matrix range in (1.1).
- A. Hatcher, *Algebraic Topology*, Sections 4.2–4.3, for the
  homotopy exact sequence of a fiber bundle and its low-degree
  component terms:
  [author's text](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf).

The action, its difference-map calculation, and the finite
homotopy-lifting construction are explicit above. No external
peer validation, formal verification, or literature-wide
novelty claim is asserted.
