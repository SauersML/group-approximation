---
rg: 2
id: deligne-q8-amalgam-and-central-sector-equivalence-proof
kind: route
title: Identify the Deligne-Q8 amalgam and transfer its central HS sectors in both directions
target: deligne-q8-finite-edge-terminal-compiler-iff-source-gap
requires:
  - deligne-triple-cover-fd-central-invisibility
  - deligne-sector-gap-is-exactly-nonhyperlinearity
  - finite-central-hs-sector-decomposition
  - amenable-edge-cycles-cannot-create-an-lcs-gap
---

# Identify the Deligne-Q8 amalgam and transfer its central HS sectors in both directions

## 1. The order-three quaternion packet

Use

\[
 Q_8=\left\langle x,y,J\ \middle|\
 J^2=1,\ x^2=y^2=J,\ [J,x]=[J,y]=1,\ yx=Jxy
 \right\rangle .                                       \tag{1}
\]

Define

\[
 \alpha(x)=y,\qquad \alpha(y)=xy,\qquad \alpha(J)=J.     \tag{2}
\]

The relation \(yx=Jxy\) gives

\[
 \alpha(xy)=y(xy)=x.
\]

Thus (2) cycles \(x,y,xy\), fixes \(J\), preserves (1), and has order
three. Put

\[
 B=Q_8\rtimes_\alpha\langle r\rangle,
 \qquad r^3=1.                                          \tag{3}
\]

This is the binary tetrahedral group of order \(24\). In particular,

\[
 C_B=\langle r,J\rangle\cong C_3\times C_2.             \tag{4}
\]

There is a two-dimensional unitary representation
\(\sigma:B\to U(2)\) with

\[
 \sigma(J)=-I_2,\qquad
 \operatorname{spec}(\sigma(r))=\{\omega,\omega^2\},
 \quad \omega=e^{2\pi i/3}.                             \tag{5}
\]

One direct construction starts with the unique two-dimensional quaternion
representation, in which \(J=-I_2\). Since its equivalence class is fixed
by \(\alpha\), an intertwiner implements (2). Rescale that intertwiner by
a cubic scalar so that its cube is \(I\). It is non-scalar, and twisting
by a character of \(C_3\) arranges its two distinct eigenvalues to be
\(\omega,\omega^2\). This proves (5) without choosing coordinates.

## 2. The finite-edge normal form

Let \(E_3\) be Deligne's triple cover, and rename its central order-three
generator \(c\). Define

\[
 D=E_3\times\langle J\rangle,\qquad J^2=1.
\]

Because \(c\ne1\),

\[
 C_D=\langle c,J\rangle\cong C_3\times C_2.             \tag{6}
\]

Identify (4) and (6) by \(r\mapsto c\), \(J\mapsto J\), and form

\[
 P=B*_{C_3\times C_2}D.                                 \tag{7}
\]

The presentation theorem for amalgamated free products, followed by
elimination of \(r\), gives exactly presentation (1) in the claim.
Therefore

\[
 P\cong\Pi_D.                                            \tag{8}
\]

Both vertex groups inject into an amalgamated free product. Hence the
nontrivial \(J\in Q_8\leq B\) remains nontrivial in \(\Pi_D\). It is
central in both vertices and is identified across the edge, so it commutes
with every amalgam generator. Thus

\[
 J\in Z(\Pi_D),\qquad J\ne1.                             \tag{9}
\]

The group \(E_3\) is finitely presented because it is a finite central
extension of the finitely presented group \(Sp_4(\mathbb Z)\). Equations
(1)--(2) add only finitely many generators and relators, so \(\Pi_D\) is
finitely presented.

The splitting (7) also records a limitation of the construction. Both
edge embeddings are proper: the edge has index \(4\) in \(B\), and \(D\)
is infinite. Hence the Bass--Serre action has no global fixed point.
Property (T) implies property FA, so \(\Pi_D\) does not have property
(T), even though its vertex group \(E_3\times C_2\) does.

## 3. Exact finite-dimensional invisibility

Deligne's finite-residual theorem plus Mal'cev residual finiteness of
finitely generated linear groups gives

\[
 \rho(c)=I
 \quad\text{for every finite-dimensional }
 \rho:E_3\to U(d).                                      \tag{10}
\]

Let \(\pi:\Pi_D\to U(d)\) be a representation. Its restriction to
\(E_3\) satisfies (10). The relation \(cxc^{-1}=y\) then gives

\[
 \pi(x)=\pi(y)=X.
\]

Applying \(\pi\) to \(yx=Jxy\) and cancelling the unitary \(X^2\) gives

\[
 \pi(J)=I.                                               \tag{11}
\]

Together, (9) and (11) prove exact survival and exact matrix
invisibility.

## 4. Hyperlinearity is unchanged

If \(E_3\) is hyperlinear, then \(D=E_3\times C_2\) is hyperlinear and
\(B\) is finite. The edge in (7) is finite, hence amenable. The
amenable-edge permanence theorem of Fima--Freslon therefore makes
\(\Pi_D\) hyperlinear.

Conversely, (7) embeds \(E_3\) into \(\Pi_D\), and hyperlinearity passes
to subgroups. Consequently

\[
 E_3\text{ is hyperlinear}
 \quad\Longleftrightarrow\quad
 \Pi_D\text{ is hyperlinear}.                            \tag{12}
\]

Thus replacing the BS actor by a property-(T) actor does not evade the
permanence boundary. It merely changes the output from provably
hyperlinear to exactly as open as the source.

## 5. Collapse of \(c\) forces collapse of \(J\)

Fix the displayed finite presentation of \(\Pi_D\). Let a unitary tuple
have maximum normalized Hilbert--Schmidt relator defect at most
\(\delta\). Write \(C,X,Y,Z\) for the evaluated matrices corresponding
to \(c,x,y,J\).

The conjugacy relator gives

\[
 \|CXC^*-Y\|_2\leq\delta.
\]

Unitary invariance and the triangle inequality yield

\[
 \|X-Y\|_2
 \leq\|X-CXC^*\|_2+\delta
 \leq2\|C-I\|_2+\delta.                                 \tag{13}
\]

The quaternion relator gives \(\|YX-ZXY\|_2\leq\delta\). Therefore

\[
\begin{aligned}
 \|Z-I\|_2
 &=\|ZXY-XY\|_2\\
 &\leq\|ZXY-YX\|_2+\|YX-XY\|_2\\
 &\leq\delta+2\|X-Y\|_2\\
 &\leq4\|C-I\|_2+3\delta.                               \tag{14}
\end{aligned}
\]

Any sequence of \(\Pi_D\)-tuples with defect tending to zero restricts to
a sequence of \(E_3\)-tuples with defect tending to zero. Hence universal
HS collapse of \(c\) for \(E_3\), together with (14), implies universal
HS collapse of \(J\) for \(\Pi_D\).

## 6. A surviving \(c\)-sector gives a surviving \(J=-I\) packet

Assume conversely that collapse of \(c\) fails. There are \(E_3\)-tuples
with defects tending to zero and with \(c\) a fixed positive distance
from \(I\). Apply finite central HS sector decomposition to the
order-three, almost-central image of \(c\). After passing to a subsequence,
one obtains a positive-dimensional block and unitary tuples \(U_n\) on
that block such that

\[
 \operatorname{Def}_{E_3}(U_n)\longrightarrow0,\qquad
 U_n(c)=\omega^j I,\quad j\in\{1,2\}.                   \tag{15}
\]

The block is measured with its own normalized trace; positive ambient
density makes all compressed relator defects tend to zero in this
normalization.

Entrywise complex conjugation gives another \(E_3\)-tuple
\(\overline U_n\), with the same defect and central value
\(\omega^{-j}I\). On the direct sum

\[
 \widehat U_n=U_n\oplus\overline U_n,                    \tag{16}
\]

the image of \(c\) has two equal spectral blocks with eigenvalues
\(\omega,\omega^2\), up to their order. Choose a basis which identifies

\[
 \widehat U_n(c)=\sigma(r)\otimes I.                    \tag{17}
\]

On the same space define

\[
 X_n=\sigma(x)\otimes I,\qquad
 Y_n=\sigma(y)\otimes I,\qquad
 Z_n=\sigma(J)\otimes I=-I.                             \tag{18}
\]

Equations (5), (17), and (18) make every quaternion and cross-conjugacy
relation exact. The actor relations have precisely the vanishing defects
of (16), and \(Z_n\), being scalar, commutes exactly with all actor
generators. Thus (16)--(18) form \(\Pi_D\)-tuples with

\[
 \operatorname{Def}_{\Pi_D}\longrightarrow0,\qquad
 \|Z_n-I\|_2=2.                                         \tag{19}
\]

Therefore collapse of \(J\) implies collapse of \(c\). Combined with
Section 5,

\[
 \operatorname{Collapse}_{HS}(E_3,c)
 \quad\Longleftrightarrow\quad
 \operatorname{Collapse}_{HS}(\Pi_D,J).                 \tag{20}
\]

## 7. Exact residual gate

The established Deligne sector theorem says

\[
 \operatorname{Collapse}_{HS}(E_3,c)
 \quad\Longleftrightarrow\quad
 E_3\text{ is nonhyperlinear}.                           \tag{21}
\]

Equations (12), (20), and (21) show that each of the following is
equivalent:

- \(E_3\) is nonhyperlinear;
- \(\Pi_D\) is nonhyperlinear;
- the Deligne mark \(c\) collapses in every HS almost representation;
- the quaternion mark \(J\) collapses in every HS almost representation.

This is a strict no-progress theorem for the most natural
finitely-presented property-(T) replacement. The finite edge gives the
normal form needed for \(J\ne1\), but it also transports hyperlinearity in
the opposite direction. The fixed spin packet transfers every surviving
Deligne central sector back to \(J=-I\), so spectral gap at the actor
vertex creates no new estimate. A successful interface must be
non-Bass--Serre and quantitatively couple the actor sector to the selector
without admitting the two-line spin absorption (5). No nonhyperlinear
group is constructed here.
