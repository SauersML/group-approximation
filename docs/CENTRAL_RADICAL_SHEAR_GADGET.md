# A shear gadget for centralizing a sofic-radical element

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

## 4. Conditional finite application to the Kun--Thom involution

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
Weak MF of $W$ is **not** known.  The repaired symmetric-double argument in
`WEAK_MF_NONSOFIC_DOUBLE.md` proves weak MF for the free-lamp amalgam, not
for this commuting-lamp wreath product.  Therefore the single group

\[
 \boxed{J(W,w)=
   (W\times C_2)*_{C_2\times C_2}
   ((C_2\times C_2)\rtimes_\alpha C_2)}               \tag{4}
\]

is a nonsofic group with a central involution in its full sofic radical,
and weak MF of (4) would settle the main problem negatively.  This is a
valid certificate, but it is stronger than the already-open assertion that
$W$ itself is weak-MF; it must not be advertised as a finite permanence
upgrade of a banked weak-MF input.

This turns the Clifford-cover certificate into a finite graph-of-groups
certificate, but its nonfinite vertex is not presently known to be weak-MF.

## 5. A banked weak-MF input and an infinite-order shear

There is a version which starts from an actually proved weak-MF nonsofic
group.  Let $x\in\operatorname{Rad}_{\mathrm{sof}}(H)$ have infinite order,
introduce the central involution $z$, and put

\[
 A=\langle x,z\rangle\cong\mathbb Z\times C_2,
 \qquad \alpha(x)=xz,\quad\alpha(z)=z.
\]

Again $\alpha$ is involutive.  Put

\[
 K_\infty=A\rtimes_\alpha \mathbb Z,
 \qquad J_\infty(H,x)=(H\times C_2)*_A K_\infty.       \tag{5}
\]

The proof of Theorems 1 and 2 applies verbatim: $z=[s,x]$ is central,
nontrivial, and belongs to the sofic radical, while weak MF of
$J_\infty(H,x)$ produces a hyperlinear nonsofic central corner.  Here
$K_\infty$ is virtually abelian, because the action of its infinite cyclic
factor on $A$ has order two.  Using an infinite cyclic stable letter avoids
an unnecessary finite-stage constraint $s^2=1$.

Now take

\[
 H=G*_{\Gamma}(\Gamma\times C_2).
\]

This free-lamp group is weak-MF by the repaired symmetric-double argument.
If $k$ denotes the nontrivial lamp, choose a strict compressor $t$ and
$\gamma\in\Gamma\setminus t\Gamma t^{-1}$, and set

\[
 x=[tkt^{-1},\gamma].                                  \tag{6}
\]

Every homomorphism $H\to S$ to a sofic group kills $x$: pair it with the
retraction $H\to G$, so that the restriction to $G$ becomes injective, and
apply Kun--Thom centralizer normalization.  Moreover $x$ has infinite
order.  Indeed, it is the product of the two distinct involutory lamps at
$t\Gamma$ and $\gamma t\Gamma$ in the free product of the lamp factors;
the product of the two canonical generators of $C_2*C_2$ has infinite
order.

Thus (5), with this explicit $(H,x)$, has a weak-MF nonsofic first vertex,
a virtually abelian second vertex, and an amenable edge
$\mathbb Z\times C_2$.  Its weak-MF status is a sharper live permanence
question than (4), because the only unbanked step is compatibility across
the edge.

## 6. Exact remaining permanence questions

Weak MF of either shear amalgam does **not** follow formally from the current amalgamation
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

The finite version is:

\[
 \boxed{
  (W\times C_2)*_{C_2\times C_2}K\text{ is weak-MF?}
 }                                                       \tag{7}
\]

The version with a banked weak-MF first vertex is:

\[
 \boxed{
 J_\infty\!\left(G*_{\Gamma}(\Gamma\times C_2),
 [tkt^{-1},\gamma]\right)\text{ is weak-MF?}
 }                                                       \tag{8}
\]

Question (8) is an explicit compatibility problem between one proved
weak-MF group and one virtually abelian group over an amenable subgroup.
On the $z=-1$ sector, its exact obstruction is spectral rather than merely
dimensional: the image of $x$ must be unitarily equivalent to its negative.
The desired central sign is already forced into the sofic radical by (3).

## 7. The exact antipodal-profile certificate

The compatibility in (8) has a concrete local form.  Call a norm-matrix
model $\phi_n$ of $H$ **antipodal at $x$** if there are unitaries $S_n$ such
that

\[
 \|S_n\phi_n(x)S_n^*+\phi_n(x)\|\longrightarrow0.       \tag{9}
\]

For the amalgam argument one also needs the same regular detector used in
the repaired symmetric-double proof: after the two vertex models are put
in compatible block form, their strong limits on the vertices and edge
must be the corresponding amplified left regular representations.  This
prevents the C*-amalgam from folding a Bass--Serre reduced word.  Merely
asking that the $H$-block have regular strong limit is not enough; the
$K_\infty$ block and the edge identifications must be part of the detector.

**Theorem 3 (antipodal regular compatible lift suffices).**  Suppose the
explicit free-lamp group $H$ above has an operator-norm asymptotic lift
which is antipodal at the witness $x$ in the sense of (9), and suppose the
compatible two-vertex block construction below has the regular detector
just specified.  Then $J_\infty(H,x)$ is weak-MF.  Consequently a
hyperlinear nonsofic group exists.

**Proof.**  Use two summands.  On the first, take the faithful weak-MF model
of $H$, put $z=1$, and let the stable generator of $K_\infty$ act by a
generic scalar.  Since $xz=x$ on this summand, all edge relations hold;
the scalar can be chosen outside the countable set which would create a
relation between the infinite-order image of $x$ and the stable generator.
This summand separates $H$ and the $z=1$ quotient of $K_\infty$.

On the second summand use $\phi_n$, put $z=-1$, and send the stable
generator to $S_n$.  Equation (9) is precisely

\[
 S_n\phi_n(x)S_n^*\simeq\phi_n(xz),
\]

while $z$ is fixed.  Thus the two vertex models agree on $A$ and give
compatible embeddings into one norm matrix ultraproduct.  Shulman's
general amalgamation criterion makes the associated C*-amalgam MF.  The
regular strong-limit representation of the two vertex models gives a
quotient onto the reduced group amalgam, exactly as in the repaired
symmetric-double argument; hence the abstract Bass--Serre copy of
$J_\infty(H,x)$ is not folded.  It is therefore weak-MF.  Theorem 2
finishes. $\square$

This isolates a local quantitative target together with a no-fold audit.
It does not ask for trace visibility or a dimension/error profile.  It asks
whether Shulman's regular asymptotic lift can be chosen so that the one
bilateral-shift word $x$ is antipodally symmetric in operator norm, while
retaining the regular detector on the completed graph of groups.  Arbitrary
weak-MF lifts do not have this property: full spectrum alone does not
control finite-stage spectral multiplicities.

## 8. Involutivization: the infinite stable letter gives no analytic gain

The use of an infinite cyclic stable letter above avoids writing $s^2=1$,
but it does not weaken the actual antipodal-profile requirement.

**Lemma 4 (involutivization by doubling).**  Let $U_n,S_n$ be unitaries and
suppose

\[
 \varepsilon_n=\|S_nU_nS_n^*+U_n\|\longrightarrow0.
\]

On the doubled space put

\[
 \widetilde U_n=U_n\oplus U_n,
 \qquad
 T_n=
 \begin{pmatrix}
 0&S_n^*\\ S_n&0
 \end{pmatrix}.
\]

Then $T_n=T_n^*$ and $T_n^2=1$, while

\[
 \|T_n\widetilde U_nT_n^*+\widetilde U_n\|
 \leq\varepsilon_n.                                  \tag{10}
\]

**Proof.**  The first two assertions are immediate.  Also

\[
 T_n\widetilde U_nT_n^*
 =S_n^*U_nS_n\oplus S_nU_nS_n^*.
\]

The second block has error $\varepsilon_n$ by hypothesis.  Conjugating the
hypothesis by $S_n^*$ shows
$\|S_n^*U_nS_n+U_n\|=\varepsilon_n$, proving (10).
$\square$

Consequently the $C_2$-stable-letter shear and the infinite-cyclic shear
have the same local matrix certificate after a harmless factor-two
amplification.  Combined with the finite-index calculation recorded as
(IS9)--(IS12) in `NOTEPAD.md`, this means the centralizer-twisted symmetric
double is the preferred endpoint: it loses no antipodal flexibility and is
the form closest to Shulman's symmetric-amalgam theorem.

## References

* T. Shulman, *The MF property for amalgamated free products*,
  arXiv:2603.13564, Theorems 10, 20, and 23.
* Q. Li, D. Hadwin, J. Li, X. Ma, J. Shen, *A note on unital full
  amalgamated free products of quasi-diagonal C*-algebras*,
  arXiv:1412.0120, for the finite-dimensional amalgam compatibility
  condition in the quasidiagonal setting.
