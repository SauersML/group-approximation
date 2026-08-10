# A finite shear gadget for centralizing a sofic-radical involution

## 1. Abstract construction

For a group $H$, write

\[
 \operatorname{Rad}_{\mathrm{sof}}(H)
 =\bigcap_{\phi:H\to S, S\ \mathrm{sofic}}\ker\phi.
\]

Assume that $x\in\operatorname{Rad}_{\mathrm{sof}}(H)$ has order two and
$x\ne1$.  Introduce a new central involution $z$, and put

\[
 B=H\times\langle z\rangle,
 \qquad A=\langle x,z\rangle\cong C_2\times C_2.
\]

Let

\[
 \alpha(x)=xz,\qquad \alpha(z)=z.
\]

This is an involutive automorphism of $A$.  Form the finite group

\[
 K=A\rtimes_\alpha\langle s\rangle,
 \qquad s^2=1,\qquad sas^{-1}=\alpha(a),              \tag{1}
\]

and the group amalgam

\[
 J(H,x)=B*_A K.                                       \tag{2}
\]

Here both copies of $A$ are the displayed subgroups.  The group $K$
has order eight (it is a dihedral presentation, with a harmless choice of
names for its generators).

## 2. The central-radical theorem

**Theorem 1.**  The canonical map $H\to J(H,x)$ is injective, the element
$z$ is a nontrivial central involution of $J(H,x)$, and

\[
 z=[s,x]\in\operatorname{Rad}_{\mathrm{sof}}(J(H,x)). \tag{3}
\]

In particular $J(H,x)$ is nonsofic.

**Proof.**  Bass--Serre normal form makes both vertex maps in (2)
injective, so it keeps $H$ and $z$ nontrivial.  The element $z$ is
central in $B$.  It is also central in $K$, because $\alpha(z)=z$.
Since the two vertex groups generate the amalgam, $z$ is central in
$J(H,x)$.  Relation (1) gives

\[
 sxs^{-1}=xz,
\]

and $x^2=1$, so $[s,x]=z$.

Now let $\psi:J(H,x)\to S$ be a homomorphism to a sofic group.  Its
restriction to $H$ kills $x$ by the defining property of the sofic
radical.  Equation (3) then gives

\[
 \psi(z)=[\psi(s),\psi(x)]=1.
\]

Thus $z$ belongs to the full sofic radical of $J(H,x)$.  If $J(H,x)$
were sofic, its identity map would be one of the homomorphisms occurring in
the intersection defining that radical, contradicting $z\ne1$. $\square$

## 3. Weak MF would finish hyperlinear versus sofic

**Theorem 2.**  If $J(H,x)$ is weak/operator-norm MF, then a hyperlinear
nonsofic group exists.

**Proof.**  Embed $J(H,x)$ injectively in a norm matrix ultraproduct.
The central involution $z$ gives the nonzero central projection

\[
 q=(1-z)/2.
\]

Lift $q$ to matrix projections and compress the unitary lifts to their
ranges.  Centrality makes the compressed maps asymptotically
multiplicative in operator norm, hence in normalized Hilbert--Schmidt norm
after the corner traces are normalized.  On the corner, $z=-1$, so the
resulting tracial-ultraproduct image retains $z$.  It is hyperlinear.

It cannot be sofic.  Otherwise the quotient map from $J(H,x)$ to this
sofic image would have to kill $z$ by Theorem 1.  This contradicts the
corner construction. $\square$

The theorem is profile-free: the negative spectral space of $z$ may have
arbitrarily small rank in the original norm models, because the trace is
renormalized after compression.

## 4. Application to the Kun--Thom involution

For the binary Kun--Thom commuting-lamp group

\[
 W=\left(\bigoplus_{G/\Gamma}C_2\right)\rtimes G,
\]

the document `COMMUTING_WREATH_SOFIC_RADICAL.md` gives an explicit
involution

\[
 w=a_{h\Gamma}a_\Gamma
\]

which normally generates $\operatorname{Rad}_{\mathrm{sof}}(W)$.
The repaired symmetric-double argument in
`WEAK_MF_NONSOFIC_DOUBLE.md` proves that $W$ is weak-MF.  Hence the
single group

\[
 \boxed{J(W,w)=
   (W\times C_2)*_{C_2\times C_2}
   ((C_2\times C_2)\rtimes_\alpha C_2)}               \tag{4}
\]

is a nonsofic group with a central involution in its full sofic radical,
and weak MF of (4) would settle the main problem negatively.

This turns the Clifford-cover certificate into a finite graph-of-groups
certificate: one weak-MF vertex, one eight-element vertex, and a
four-element edge group.

## 5. Exact remaining permanence question

Weak MF of (4) does **not** follow formally from the current amalgamation
theorems.  Shulman's symmetric theorem proves $D*_C D$ MF when the two
embeddings of $C$ are the same.  Her general theorem characterizes
$D_1*_{C}D_2$ by the existence of compatible embeddings of both vertex
algebras into one MF algebra; it does not make that compatibility automatic.
The theorem for group amalgams with no extra hypothesis assumes both vertex
groups amenable.

Here the finite vertex $K$ forces the two elements $x$ and $xz$ to be
unitarily conjugate.  Consequently a finite-dimensional representation of
the edge group extends to $K$ only if its $(z=-1,x=+1)$ and
$(z=-1,x=-1)$ multiplicities agree.  A generic weak-MF model of $W$
need not have this balance.  That multiplicity equality is the precise
compatibility condition still to manufacture.

Thus the open subproblem is:

\[
 \boxed{
  (W\times C_2)*_{C_2\times C_2}K\text{ is weak-MF?}
 }                                                       \tag{5}
\]

It is strictly more structured than arbitrary finite-central-extension
closure: all new groups in the graph of groups are finite, the edge
embedding is explicit, and the desired central sign is already forced into
the sofic radical by (3).

## References

* T. Shulman, *The MF property for amalgamated free products*,
  arXiv:2603.13564, Theorems 10, 20, and 23.
* Q. Li, D. Hadwin, J. Li, X. Ma, J. Shen, *A note on unital full
  amalgamated free products of quasi-diagonal C*-algebras*,
  arXiv:1412.0120, for the finite-dimensional amalgam compatibility
  condition in the quasidiagonal setting.
