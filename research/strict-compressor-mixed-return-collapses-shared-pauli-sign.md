---
rg: 2
id: strict-compressor-mixed-return-collapses-shared-pauli-sign
kind: claim
title: One strict compressor and one mixed return collapse the shared Pauli sign
artifacts:
  - research/strict-compressor-mixed-return-pauli-proof.md
distinct_from:
  kazhdan-stabilizer-collapses-shared-pauli-sign: that uses finite double-coset rank, all orbit prototypes, and compactness; this uses one strict compressor and one fixed off-site row, with no orbit-rank hypothesis.
  commutant-no-growth: that proves equality of two commutants for a genuine finite-dimensional representation; this inserts the equality into a shared-Pauli row and gives a quantitative sign estimate, including arbitrary finite-corner dilations.
  strict-one-sided-compression-forces-infinite-bi-index: that shows strict compression rules out finite orbit rank; this shows the same strictness supplies a different, one-row exact-actor collapse.
  approximate-collapse-for-kt-compressor: that is the arbitrary-microstate commutant-collapse problem for the Laurent actor; this identifies the single mixed-return consequence of that problem which the Pauli sign actually needs.
---

**ESTABLISHED EXACT-ACTOR THEOREM; THE ARBITRARY-MICROSTATE
NORMALIZATION CONDITION REMAINS OPEN FOR THE KUN--THOM ACTOR.**

Let \(H\leq G\), let
\[
        tHt^{-1}<H,                                      \tag{MR1}
\]
choose
\[
        \gamma\in H\setminus tHt^{-1},\qquad
        r=t^{-1}\gamma t.                                \tag{MR2}
\]
Then \(r\notin H\), so \(H\) and \(rH\) are distinct sites of \(G/H\).
Let \(\rho:G\to U(D)\) be a genuine finite-dimensional representation and
put
\[
        N=\rho(H)''\subseteq M_D(\mathbb C).              \tag{MR3}
\]
Conjugation gives an inclusion
\[
 \operatorname{Ad}\rho(t)(N)=\rho(tHt^{-1})''\subseteq N. \tag{MR4}
\]
The two algebras in (MR4) have the same finite vector-space dimension,
because they are unitarily conjugate.  Hence (MR4) is equality, and
\[
        \rho(r)=\rho(t)^*\rho(\gamma)\rho(t)\in N.         \tag{MR5}
\]

This one algebraic fact gives the following dimension-free Pauli estimate.
Assume \(H\) has a finite Kazhdan set \(Q\), with the convention
\[
 \operatorname{dist}(\xi,\mathcal K^H)
 \leq {1\over\kappa}\max_{q\in Q}\|\pi(q)\xi-\xi\|
                                                                  \tag{MR6}
\]
for every unitary representation \(\pi\) of \(H\).  For unitaries
\(A,B,J\in U(D)\), define
\[
\begin{aligned}
 d_0&=\|ABA^*B^*-J\|_2,\\
 d_H&=\max_{q\in Q}\|[B,\rho(q)]\|_2,\\
 d_X&=\|[A,\rho(r)B\rho(r)^*]\|_2 .
\end{aligned}                                                   \tag{MR7}
\]
Then
\[
 \boxed{\quad
 \|J-I\|_2\leq d_0+d_X+{4\over\kappa}d_H .
 \quad}                                                         \tag{MR8}
\]
Only one of the two root Pauli unitaries has to satisfy the stabilizer
rows, and only the single off-site row indexed by \(rH\) is used.  In
particular, exact shared-Pauli rows force \(J=I\).  No finite
double-coset rank, compactness recurrence, multiplicity bound, or
finite-presentation hypothesis occurs.

If \(H\) is infranormal but not normal in the Kun--Thom sense, a strict
compressor \(t\) as in (MR1) necessarily exists.  Thus every such Kazhdan
pair has a fixed mixed-return Pauli wall of the form (MR2)--(MR8), even
though strict compression also forces
\(|H\backslash G/H|=\infty\).

The estimate is stable under a nearby genuine actor.  Let \(u_q,u_r\) be
actor matrices, let \(d_H,d_X\) be defined as in (MR7) with \(u\) in place
of \(\rho\), and suppose
\[
 \eta=\max\bigl(\{\|u_q-\rho(q)\|_2:q\in Q\}
                   \cup\{\|u_r-\rho(r)\|_2\}\bigr).       \tag{MR9}
\]
Then
\[
 \boxed{\quad
 \|J-I\|_2\leq
 d_0+d_X+{4\over\kappa}d_H+
 \left(4+{8\over\kappa}\right)\eta .
 \quad}                                                         \tag{MR10}
\]

There is also a full-corner form.  Suppose actor matrices act on
\(\mathbb C^d\), while \(\rho\) acts on \(\mathbb C^D\), \(D\geq d\), and
an isometry \(V:\mathbb C^d\to\mathbb C^D\) satisfies
\[
 \alpha=\max_{s\in Q\cup\{r\}}
 \|V^*\rho(s)V-u_s\|_{2,d}.                               \tag{MR11}
\]
Then the finite-corner completion lemma gives arbitrary complementary
unitaries \(z_s\) for which the block actor error is at most
\[
 \sqrt{d/D}\,\sqrt{\alpha^2+6\alpha}.
\]
Applying (MR10) to \(A\oplus I,B\oplus I,J\oplus I\), and cancelling the
same factor \(\sqrt{d/D}\), yields
\[
 \boxed{\quad
 \|J-I_d\|_{2,d}\leq
 d_0+d_X+{4\over\kappa}d_H+
 \left(4+{8\over\kappa}\right)\sqrt{\alpha^2+6\alpha}.
 \quad}                                                         \tag{MR12}
\]
Thus finite-corner exactification only on the fixed packet
\(Q\cup\{r\}\) collapses the shared sign, independently of \(D/d\) and
without finite orbit rank.

What an arbitrary approximate actor must supply is now exact.  For relevant
actor microstates \(u\), define the **mixed-return normalization modulus**
by the implication
\[
 \operatorname{Def}_F(u)\to0,\quad
 \max_{q\in Q}\|[B,u_q]\|_2\to0
 \quad\Longrightarrow\quad
 \|u_rBu_r^*-B\|_2\to0                                  \tag{MR13}
\]
for every unitary \(B\).  Once (MR13) holds, the same one-row calculation
gives
\[
 \|J-I\|_2\leq d_0+d_X+
             2\|u_rBu_r^*-B\|_2\longrightarrow0.         \tag{MR14}
\]
Finite-corner actor exactification implies (MR13), but is stronger than
needed.

In ultraproduct language, (MR13) is precisely the one-element consequence
\[
 x\in \sigma(H)'\cap\mathcal M
       \quad\Longrightarrow\quad [x,\sigma(r)]=0.         \tag{MR15}
\]
Requiring (MR15) for all \(\gamma\in H\) is the compressor commutant
equality
\[
 \sigma(H)'=\sigma(tHt^{-1})',
\]
the Kun--Thom centralizer-normalization wall.  Property \((T)\) or robust
low-spectrum control by itself does not assert (MR15); it controls which
vectors have low \(H\)-energy, not whether the compressor preserves that
low-energy space in operator norm.

This distinction is sharp in general.  For
\[
 G=BS(1,2)=\langle a,t\mid tat^{-1}=a^2\rangle,\qquad
 H=\langle a\rangle,
\]
the pair is infranormal and nonnormal, with
\(r=t^{-1}at\notin H\).  Its shared-center Pauli semidirect product is
amenable, hence sofic and hyperlinear.  Canonical matrix microstates have
\[
 [B_H,u_a]\to0,\qquad
 \|u_rB_Hu_r^*-B_H\|_2\to\sqrt2,\qquad
 \|J-I\|_2\to\sqrt2,                                    \tag{MR16}
\]
while the single off-site row
\([A_H,u_rB_Hu_r^*]\to0\) holds.  Therefore pointwise actor
multiplicativity and all fixed Pauli relations do not imply (MR13).
This example has no Kazhdan stabilizer and does not decide the Kun--Thom
case; it proves that the missing normalization is a real source-specific
hypothesis, not a formal consequence of strict compression.
