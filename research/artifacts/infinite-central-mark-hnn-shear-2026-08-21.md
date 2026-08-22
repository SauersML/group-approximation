# Infinite central mark by a torsion-free HNN shear

## Result

The open algebraic claim `infinite-order-central-mark-group` has a direct
construction.  It does not require an infinite Heisenberg lamp orbit.  The
compression defect is first protected as a Britton word of infinite order;
a second HNN extension then shears a new central coordinate by that word.

## 1. A torsion-free Kazhdan compression source

Let

\[
K=\ker\bigl(\mathrm{SL}_3(\mathbb Z)\to
             \mathrm{SL}_3(\mathbb Z/3\mathbb Z)\bigr),\qquad
\Gamma=\mathbb Z^3\rtimes K.
\]

The level-three principal congruence subgroup is torsion-free.  Since it is
finite index in \(\mathrm{SL}_3(\mathbb Z)\), it is finitely presented and
has property (T).  The affine group \(\Gamma\) is finite index in
\(\mathbb Z^3\rtimes\mathrm{SL}_3(\mathbb Z)\), so it too is finitely
presented and has property (T).  It is torsion-free: if
\((v,A)^n=1\), then \(A^n=1\), hence \(A=1\); then \(nv=0\), hence
\(v=0\).

Define

\[
\alpha(v,A)=(2v,A),\qquad a=(e_1,I).
\]

This is an injective endomorphism, and \(a\notin\alpha(\Gamma)\).

Set \(B=\Gamma\times\langle c\rangle\) and form the HNN extension

\[
P=\langle B,t\mid t\gamma t^{-1}=\alpha(\gamma),\ \gamma\in\Gamma\rangle.
\]

This is exactly Cairn's `concrete-compression-source`.  The word

\[
u=[tct^{-1},a]
 =tct^{-1}a t c^{-1}t^{-1}a^{-1}
\]

is Britton reduced: \(c^{\pm1}\notin\Gamma\), while
\(a\notin\alpha(\Gamma)\).  It is therefore nontrivial.  Since \(B\) is
torsion-free, the HNN torsion theorem makes \(P\) torsion-free, so \(u\)
has infinite order.  Finite presentability follows from finite
presentability of \(\Gamma\) and finite generation of the associated
subgroups.

## 2. The shear

Let \(z\) generate a new infinite cyclic direct factor and put

\[
B_1=P\times\langle z\rangle,
\qquad A=\langle u,z\rangle\le B_1.
\]

The map \(\mathbb Z^2\to A\), \((m,n)\mapsto u^m z^n\), is injective:
projection to the two direct factors and infinite order of \(u,z\) force
\(m=n=0\).  Thus \(A\cong\mathbb Z^2\).  The rule

\[
\phi(u)=uz,\qquad\phi(z)=z
\]

is the unimodular shear \((m,n)\mapsto(m,m+n)\), hence an automorphism of
\(A\).  Form

\[
H=\langle B_1,s\mid sus^{-1}=uz,\ szs^{-1}=z\rangle.
\]

Britton's lemma embeds \(B_1\) into \(H\), so \(z\) remains infinite.
The HNN torsion theorem makes \(H\) torsion-free.  The group is finitely
presented because \(B_1\) is and \(A\) has the two displayed generators.

The element \(z\) commutes with \(P\) in the base and with \(s\) by the
second HNN relation, hence is central in \(H\).  Moreover

\[
z=(sus^{-1})u^{-1}\in\langle\!\langle u\rangle\!\rangle_H.
\]

The first HNN base embedding preserves the Kazhdan subgroup, compressor,
and centralized witness.  The second preserves all of \(P\).  Thus \(H\)
has precisely the data demanded by `infinite-order-central-mark-group`.

## 3. Why the literal Heisenberg-lamp substitution failed

The original scale-two idea tries to put an invariant integral alternating
form on the coset lamps.  In the ascending HNN group put
\(r=t^{-1}at\).  Since \(\alpha(a)=a^2\),

\[
r^2=t^{-1}a^2t=t^{-1}\alpha(a)t=a\in\Gamma.
\]

Therefore \(r\) swaps \(\Gamma\) and \(r\Gamma\).  Invariance and
alternation force

\[
\beta(\Gamma,r\Gamma)=\beta(r\Gamma,\Gamma)
=-\beta(\Gamma,r\Gamma),
\]

so an integer-valued pairing vanishes.  This is not merely a missing finite
orbit argument: the desired torsion-free central phase is algebraically
forbidden on the exact marked pair.  The shear construction escapes because
it never asks the coset action to orient that pair.

## 4. Consequence boundary

This closes an algebraic input to three existing **operator-norm MF**
routes.  It does not itself prove non-MF: those routes still require one of
`commutant-projection-extraction`, `kazhdan-invariant-subspace-generates`, or
`exel-loring-mark-quantization`.  It is not on a live route to
`non-hyperlinear-group`.  Even completing one of the MF routes would not
imply non-hyperlinearity, because norm-matrix MF approximation is strictly
stronger than normalized-Hilbert--Schmidt approximation.  No HS conclusion
is claimed here.
