# Equivariant Steinberg globalization of square-zero curvature

## The basic mechanism

Let \(E\) be a perfect group and let

\[
1\longrightarrow K\longrightarrow\widetilde E
\xrightarrow{\pi}E\longrightarrow1
\]

be its universal central extension.  Thus

\[
K\cong H_2(E;\mathbb Z).
\]

Let a group \(A\) act on \(E\) by automorphisms.

### Theorem 1 (equivariant universal-central globalization)

The action of \(A\) lifts canonically to an action on \(\widetilde E\).  If

\[
K_A:=K/[A,K]
\]

is the coinvariant quotient, then

\[
1\longrightarrow K_A
\longrightarrow
(\widetilde E/[A,K])\rtimes A
\longrightarrow E\rtimes A
\longrightarrow1
\]

is a central extension.

#### Proof

Every automorphism of \(E\) lifts uniquely to the universal central
extension, by its universal property.  Uniqueness makes these lifts an action
of \(A\) on \(\widetilde E\), and the induced action on the kernel is the
natural action on \(H_2(E;\mathbb Z)\).

After quotienting \(\widetilde E\) by \([A,K]\), the external group \(A\)
acts trivially on the image \(K_A\).  That image was already central in
\(\widetilde E\), so it is central in the displayed semidirect product.  The
quotient is plainly \(E\rtimes A\). \(\square\)

The kernel is moreover contained in the commutator subgroup of the middle
group.  Indeed, \(\widetilde E\) is perfect, so its quotient
\(\widetilde E/[A,K]\) is perfect and contains \(K_A\).  The five-term
sequence of the displayed central extension therefore gives a surjection

\[
\boxed{
H_2(E\rtimes A;\mathbb Z)\twoheadrightarrow K_A.
}
\]

Thus an element of exact order \(p^k\) in \(K_A\) forces the Schur multiplier
of the full semidirect product to contain an element whose order is divisible
by \(p^k\).

### Corollary 2 (coinvariant characters are global multipliers)

Every character

\[
\chi:K_A\longrightarrow\mathbb T
\]

pushes out the extension in Theorem 1 to a projective multiplier class on
\(E\rtimes A\).  If \(E\rtimes A\) is finite, the associated twisted regular
representation is finite dimensional.

Thus the correct globalization test for a local square-zero class is not
simultaneous construction of matrices for all external generators.  It is
the finite abelian question whether that class remains nonzero, and with what
order, in the coinvariants \(H_2(E;\mathbb Z)_A\).

## Elementary groups and relative \(K_2\)

In stable elementary rank, the universal central extension is the Steinberg
extension

\[
1\longrightarrow K_2(R)
\longrightarrow\operatorname{St}_r(R)
\longrightarrow E_r(R)
\longrightarrow1.
\]

For a finite square-zero quotient

\[
R=A\oplus V,
\qquad V^2=0,
\]

the curvature sector relevant to the tangent construction lies in the
relative group

\[
K_2(R,V)
:=\ker\bigl(K_2(R)\to K_2(A)\bigr).
\]

Ring automorphisms act functorially on the Steinberg group and on relative
\(K_2\).  Therefore, if the finite image \(A_{m ext}\) of the external
\(Q\times L\)-action preserves a relative class \(\kappa_k\) in coinvariants,
then

\[
[\kappa_k]\in K_2(R_k,V_k)_{A_{\rm ext}}
\]

defines a global projective multiplier of

\[
E_r(R_k)\rtimes A_{\rm ext}.
\]

If \([\kappa_k]\) has order \(p^k\), its full growing order survives the
globalization.

## Induced-module order preservation

There is a particularly clean certificate for survival in external
coinvariants.

### Lemma 3 (coinvariants of an induced module)

Let \(H\leq A\) and let \(M\) be a left \(\mathbb Z[H]\)-module.  Then

\[
\boxed{
\left(\operatorname{Ind}_H^A M\right)_A
\cong M_H.
}
\]

#### Proof

Using coinvariants as tensor product,

\[
\begin{aligned}
\left(\mathbb Z[A]\otimes_{\mathbb Z[H]}M\right)_A
&=\mathbb Z\otimes_{\mathbb Z[A]}
\left(\mathbb Z[A]\otimes_{\mathbb Z[H]}M\right)\\
&\cong \mathbb Z\otimes_{\mathbb Z[H]}M
=M_H.
\end{aligned}
\]

\(\square\)

### Corollary 4 (induced summand certificate)

Suppose there is an \(A\)-equivariant split injection

\[
\operatorname{Ind}_H^A M
\longrightarrow K_2(R,V)
\]

and a local class \(\kappa\in M_H\) has exact order \(p^k\).  Then its image
in

\[
K_2(R,V)_A
\]

also has exact order \(p^k\).

More generally, it suffices to construct a retraction after taking
coinvariants.  Thus the external covariance problem can be closed by an
explicit module map and coinvariant decoder; no matrix optimization is
required.

## Relative version for the positive subgroup

Let \(E_+\leq E\) be perfect \(A\)-invariant groups, and suppose the inclusion
lifts to their universal central extensions.  Write

\[
K_+=H_2(E_+;\mathbb Z),
\qquad
K=H_2(E;\mathbb Z).
\]

### Proposition 5 (relative curvature character)

Suppose a character

\[
\chi:K_A\to\mathbb T
\]

vanishes on the image of \((K_+)_A\).  Then the global central extension of
\(E\rtimes A\) obtained from \(\chi\) has split curvature on

\[
E_+\rtimes A.
\]

#### Proof

The restriction of the pushed-out central extension to \(E_+\) is classified
by the composite

\[
K_+\longrightarrow K\longrightarrow K_A
\xrightarrow{\chi}\mathbb T,
\]

which is zero by assumption.  The chosen equivariant lift of \(A\) supplies
the same splitting on the semidirect product. \(\square\)

This is the cohomological compatibility required by the amalgam: curvature
may be nontrivial on the full vertex group while vanishing on the positive
edge group.

## Exact completion target for the current construction

For the finite square-zero quotients in the Kun--Thom double, it is enough to
establish the following statements.

1. The integral Baumslag--Solitar clock class is the image of a relative
   Steinberg class
   \[
   \kappa_k\in K_2(R_k,V_k).
   \]
2. Its image in the external coinvariants
   \[
   K_2(R_k,V_k)_{A_{{\rm ext},k}}
   \]
   has exact order \(p^k\).
3. A character detecting that class vanishes, or has asymptotically vanishing
   phase, on the image of the positive relative group.
4. After extending the curvature character to the full central relation
   module of the symmetric double, the paired discriminant gauge choice makes
   all fixed relator phases negligible while retaining the marked fold phase.

Items 1--3 replace the unresolved simultaneous Frobenius/principal-bundle
matrix covariance problem.  Item 4 is the already-isolated finite nonlinear
circle-repair problem.

## Relation to the Mackey route

The Mackey double-coset criterion and Theorem 1 are complementary.

- Mackey transfer globalizes a class from a finite subgroup.
- Equivariant Steinberg globalization globalizes a class from the perfect
  elementary normal subgroup.

For the square-zero construction, the Steinberg route is preferable whenever
the clock class can be identified in relative \(K_2\): external covariance is
then absorbed functorially, and only survival in coinvariants remains.
