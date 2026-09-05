---
rg: 2
id: square-covariance-cubic-spectrum-proof
kind: route
title: Match eigenangles and classify periodic noisy doubling below two fifths
target: unitary-square-covariance-forces-cubic-spectrum
requires: []
artifacts:
  - experiments/verify_cubic_spectral_basin.py
---

All norms below are operator norms. The argument applies in every finite
dimension; the finite-grid script is only an exact calibration, not a proof
of the universal assertion. Section and equation numbers follow the
cumulative research record.

### 14.1. Eigenvalue matching along a short unitary path

**Lemma.** Let \(A,B\in U(d)\) and \(\|A-B\|=\delta<2\). Their eigenvalues,
counted with multiplicity, can be matched so that each matched pair has
circular angular distance at most

\[
\alpha=2\arcsin(\delta/2).
\tag{14.1}
\]

**Proof.** There is a self-adjoint matrix \(H\) with spectrum in
\((-\pi,\pi)\) such that \(B=Ae^{iH}\). Diagonalizing \(A^*B\) shows that
\(\|H\|=2\arcsin(\delta/2)=\alpha\).

First suppose \(A\) has distinct eigenvalues. The path
\(A(t)=Ae^{itH}\), \(0\le t\le1\), is analytic in \(t\). Its
characteristic-polynomial discriminant is analytic and is nonzero at
\(t=0\). Its zeros on the compact interval are consequently finite. Away
from those times, eigenvalues are simple and can be followed differentiably;
this follows by the implicit-function theorem for a simple root of the
characteristic polynomial. A corresponding normalized eigenvector can be
chosen differentiably locally, by solving the eigenvector equations in a
coordinate chart where one component is nonzero.

For \(A(t)v(t)=e^{i\theta(t)}v(t)\), differentiation and multiplication by
\(v(t)^*\) give

\[
\theta'(t)=v(t)^*H v(t),\qquad |\theta'(t)|\le\|H\|.
\]

Here \(A'(t)=iA(t)H\), and normality gives
\(v(t)^*A(t)=e^{i\theta(t)}v(t)^*\). At each of the finitely many collision
times, join the incoming and outgoing branches with the same limiting
eigenvalue. Eigenvalues are continuous as a multiset: this follows from
continuity of polynomial roots, or by factoring a convergent sequence of
monic characteristic polynomials and comparing their limiting factors.
Choose continuous real lifts of the phases along the resulting branches.
The derivative bound on the finitely many intervening intervals implies a
total phase change of at most \(\|H\|\) for each branch. These branches
give the desired matching.

For general \(A\), choose unitary matrices \(A_k\to A\) with distinct
eigenvalues, by perturbing its eigenangles, and put \(B_k=A_ke^{iH}\).
The preceding proof matches the eigenvalues of \(A_k,B_k\) with angular
distance at most the same \(\|H\|\). List their eigenvalues so that they
converge, including multiplicities, to lists for \(A,B\). Passing to a
subsequence makes the matching permutation constant, since there are only
finitely many permutations. Taking the limit proves the lemma. ∎

This proof uses only elementary finite-dimensional spectral theory and
elementary facts about analytic functions. No estimate depends on \(d\).

### 14.2. A periodic approximate doubling orbit below the fifth-root threshold

**Lemma.** Fix

\[
\frac13\le a<\frac25,
\qquad 0\le\epsilon<\frac{2-5a}{10}.
\]

Let a finite cyclic sequence \(x_j\in[-a,a]\) satisfy

\[
x_{j+1}\equiv2x_j+e_j\pmod1,\qquad |e_j|\le\epsilon.
\tag{14.2}
\]

Then either every \(|x_j|\le\epsilon\), or the signs alternate and

\[
\left|x_j-\frac{\operatorname{sign}(x_j)}3\right|
\le\epsilon
\quad\text{for every }j.
\tag{14.3}
\]

**Proof.** Write

\[
c=\frac{a+\epsilon}{2},\qquad
b=\frac{1-a-\epsilon}{2}.
\]

The smallness hypothesis implies \(c<b\) and \(2a+\epsilon<1\).
For a point \(x\in[-a,a]\) to have any allowed successor in \([-a,a]\),
equation (14.2) requires

\[
x\in I_0\cup I_+\cup I_-,\qquad
I_0=[-c,c],\quad I_+=[b,a],\quad I_-=[-a,-b].
\tag{14.4}
\]

Indeed, if no integer is subtracted from \(2x+e\), then
\(|2x|\le a+\epsilon\). If 1 is subtracted, then
\(2x\ge1-a-\epsilon\); if \(-1\) is subtracted, the symmetric inequality
holds. No other integer is possible because \(|2x+e|<1\).

If \(x\in I_+\), then

\[
1-a-2\epsilon\le2x+e\le2a+\epsilon.
\]

The lower endpoint is greater than \(a\), so the successor must be
\(y=2x+e-1\), which is negative. Furthermore,

\[
|y|\ge1-2a-\epsilon>c.
\]

The last strict inequality follows from \(3\epsilon<2-5a\). Since \(y\)
also belongs to (14.4), it lies in \(I_-\). By symmetry \(I_-\) maps into
\(I_+\) along any admissible cyclic sequence.

Thus, if the cycle ever enters an outer interval, it stays in the outer
intervals, and periodicity shows that all its points are outer. Their signs
alternate. Set \(d_j=x_j-\operatorname{sign}(x_j)/3\). The wrap by 1 or
\(-1\) just identified gives exactly

\[
d_{j+1}=2d_j+e_j.
\]

Let \(M=\max_j|d_j|\). At a point attaining this maximum,
\(M\ge|d_{j+1}|\ge2M-\epsilon\), hence \(M\le\epsilon\).

If the cycle never enters an outer interval, all \(|x_j|\le c\). Then
\(|2x_j+e_j|\le a+2\epsilon<2/5<1/2\). Since the successor also lies in
\([-c,c]\subset(-1/2,1/2)\), no wrap is possible. Consequently
\(x_{j+1}=2x_j+e_j\) as an equality of real numbers. The same maximum
argument gives \(\max_j|x_j|\le\epsilon\). ∎

Finiteness of the cycle is essential. One cannot substitute an infinite
one-way orbit and assume its largest deviation must return.

### 14.3. Uniform cubic rigidity for one approximate Baumslag–Solitar pair

**Theorem.** Fix \(1/3\le a<2/5\), and set

\[
c_a=2\sin(\pi a),\qquad
\delta_a=2\sin\left(\frac{\pi(2-5a)}{10}\right)>0.
\]

If finite-dimensional unitaries \(U,V\) satisfy

\[
\|U-I\|\le c_a,
\qquad \delta=\|VUV^*-U^2\|<\delta_a,
\]

then

\[
\boxed{\|U^3-I\|\le6\arcsin(\delta/2).}
\tag{14.5}
\]

**Proof.** Write the eigenvalues of \(U\) as \(e^{2\pi i x_j}\), with
\(x_j\in[-a,a]\); the norm bound gives precisely this inclusion.
The eigenvalues of \(VUV^*\) are the same list, while those of \(U^2\)
are its squared list. The matching lemma provides a permutation \(\sigma\)
such that

\[
x_{\sigma(j)}\equiv2x_j+e_j\pmod1,
\qquad |e_j|\le\epsilon
:=\frac{2\arcsin(\delta/2)}{2\pi}.
\]

The defect threshold ensures \(\epsilon<(2-5a)/10\). Apply §14.2 to
each cycle of \(\sigma\). Every \(x_j\) is within \(\epsilon\) of
\(0,1/3\), or \(-1/3\). Thus

\[
|e^{6\pi i x_j}-1|\le6\pi\epsilon
=6\arcsin(\delta/2).
\]

The spectral theorem gives (14.5). ∎

For example, \(a=3/8\) gives
\(c_a=\sqrt{2+\sqrt2}\) and \(\delta_a=2\sin(\pi/80)\).
The theorem is a fixed-word, dimension-independent estimate. It does not
correct the whole pair to an exact Baumslag–Solitar representation.

The strict upper radius is sharp for this cubic conclusion. Let
\(\zeta=e^{2\pi i/5}\), put
\(U=\operatorname{diag}(\zeta,\zeta^2,\zeta^3,\zeta^4)\), and let the
permutation unitary \(V\) send the basis vector labelled \(j\) to the one
labelled \(3j\pmod5\). Then

\[
VUV^*=U^2,\quad \|U-I\|=2\sin(2\pi/5),\quad U^3\ne I.
\]

This is a counterexample only to extending the cubic theorem to its endpoint;
it is not a Higman four-cycle model.
