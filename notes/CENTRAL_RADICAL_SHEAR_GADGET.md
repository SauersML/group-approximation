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

The antipodal relation itself is already a trace detector.  The larger
shear amalgam and its Bass--Serre no-fold argument are unnecessary once
(9) has been produced.

**Theorem 3 (antipodal norm models suffice).**  Let $H$ be countable and
let $x$ belong to its full sofic radical.  Suppose there are maps
$\phi_n:H\to U(d_n)$ whose pointwise multiplicative defects tend to zero in
operator norm, and unitaries $S_n$ satisfying (9).  Then the tracial
ultraproduct image of $H$ is a hyperlinear nonsofic group.  In particular,
a hyperlinear nonsofic group exists.

**Proof.**  Operator-norm multiplicative defect bounds normalized
Hilbert--Schmidt defect, so

\[
 \Phi(h)=[\phi_n(h)]_2
\]

is a homomorphism into a tracial matrix ultraproduct.  Trace invariance
under conjugacy and (9) give

\[
 2\,|\operatorname{tr}_{d_n}(\phi_n(x))|\longrightarrow0.
\]

Consequently

\[
 \|\phi_n(x)-1\|_2^2
 =2-2\operatorname{Re}\operatorname{tr}_{d_n}(\phi_n(x))
 \longrightarrow2,
\]

so $\Phi(x)\ne1$.  The image $Q=\Phi(H)$ is hyperlinear.  If $Q$ were
sofic, the quotient homomorphism $H\to Q$ would kill $x$ by the definition
of the full sofic radical, contradicting $\Phi(x)\ne1$. $\square$

More generally, the same proof works with
$S_n\phi_n(x)S_n^*\simeq\omega\phi_n(x)$ for any fixed
$\omega\in\mathbb T\setminus\{1\}$.  Thus the precise remaining target is
only (9).  It needs neither norm-faithfulness, a regular strong-limit
detector, weak MF of the completed shear amalgam, nor control of its
Bass--Serre normal form.

### Relative-lifting audit

There is a canonical infinite-dimensional source of the desired symmetry.
If $x$ has infinite order, the quasi-regular representation on
$H/\langle x^2\rangle$ has an exact parity involution $S$ with
$S\pi(x)S=-\pi(x)$.  Equivalently, $(\pi(x),S)$ represents

\[
 C(\mathbb T)\rtimes_{z\mapsto-z}C_2\cong M_2(C(\mathbb T)).
\]

Shulman's MF lifting characterization does **not** by itself turn this
operator symmetry into (9).  It lifts a representation of an MF algebra
through the quotient from strongly convergent matrix sequences to
$B(\mathcal H)$.  An external lift of $S$ then makes the anticommutator
converge strongly to zero, whereas (9) requires norm convergence.  Her
homotopy-lifting theorem likewise does not prescribe the lift on the common
copy of $C^*(x)$.

Accordingly, the missing statement is a genuinely relative one: lift the
ambient representation and the $M_2(C(\mathbb T))$ representation so that
their two lifts of $C^*(x)$ agree in norm.  This is exactly Shulman's
compatible-embedding criterion for the corresponding amalgamated free
product; it is not a consequence of ordinary MF or homotopy invariance.

**Lemma 4 (the antipodal representation exists).**  Let a group $L$ act on
a tree and let $x\in L$ be hyperbolic.  In the quasi-regular representation
on $\ell^2(L/\langle x^2\rangle)$ there is a diagonal self-adjoint unitary
$S$ such that

\[
 S\pi(x)S=-\pi(x).                                   \tag{10}
\]

Moreover this representation is weakly contained in the left regular
representation of $L$.

**Proof.**  Consider the orbits of $x$ on $L/\langle x^2\rangle$.  If such
an orbit has finite length $m$, then for some $g\in L$ and $k\in\mathbb Z$

\[
 g^{-1}x^mg=x^{2k}.
\]

Translation length is invariant under conjugacy and satisfies
$\ell_T(x^j)=|j|\ell_T(x)$.  Since $x$ is hyperbolic, this equality forces
$|m|=2|k|$; hence every finite orbit has even length.  Color each finite or
infinite orbit alternately and let $S$ be multiplication by its
$\{1,-1\}$-valued coloring.  This proves (10).  Finally
$\langle x^2\rangle$ is amenable, so its induced trivial representation,
which is the displayed quasi-regular representation, is weakly contained
in $\lambda_L$. $\square$

For the primitive length-two radical word in the Kun--Thom symmetric
double, the Bass--Serre action supplies the hypothesis.  Thus the exact
antipodal representation factors through $C_r^*(L)$.  What remains open is
precisely whether its parity operator can survive an MF lift in norm.

## 8. Involutivization: the infinite stable letter gives no analytic gain

The use of an infinite cyclic stable letter above avoids writing $s^2=1$,
but it does not weaken the actual antipodal-profile requirement.

**Lemma 5 (involutivization by doubling).**  Let $U_n,S_n$ be unitaries and
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
 \leq\varepsilon_n.                                  \tag{11}
\]

**Proof.**  The first two assertions are immediate.  Also

\[
 T_n\widetilde U_nT_n^*
 =S_n^*U_nS_n\oplus S_nU_nS_n^*.
\]

The second block has error $\varepsilon_n$ by hypothesis.  Conjugating the
hypothesis by $S_n^*$ shows
$\|S_n^*U_nS_n+U_n\|=\varepsilon_n$, proving (11).
$\square$

Consequently the $C_2$-stable-letter shear and the infinite-cyclic shear
have the same local matrix certificate after a harmless factor-two
amplification.  Combined with the finite-index calculation recorded as
(IS9)--(IS12) in `notes/NOTEPAD.md`, this means the centralizer-twisted symmetric
double is the preferred endpoint: it loses no antipodal flexibility and is
the form closest to Shulman's symmetric-amalgam theorem.

## References

* T. Shulman, *The MF property for amalgamated free products*,
  arXiv:2603.13564, Theorems 10, 20, and 23.
* T. Shulman, *Homotopy lifting, asymptotic homomorphisms, and traces*,
  arXiv:2508.00125, especially the MF lifting characterization and the
  mapping-cylinder homotopy-lifting theorem.
* Q. Li, D. Hadwin, J. Li, X. Ma, J. Shen, *A note on unital full
  amalgamated free products of quasi-diagonal C*-algebras*,
  arXiv:1412.0120, for the finite-dimensional amalgam compatibility
  condition in the quasidiagonal setting.
