---
rg: 2
id: kazhdan-edge-terminal-sign-remains-hyperlinear
kind: claim
title: A Kazhdan-edge iteration of the terminal sign still has a finite transverse splitting
artifacts:
  - research/finite-transverse-splitting-of-kazhdan-edge-sign.md
distinct_from:
  q8-bs23-terminal-mark-is-exactly-invisible-but-hyperlinear: that supplies one FD-invisible central sign across an amenable cyclic edge; this uses that sign as the actor of a second Q8 selector and makes the displayed edge itself property T.
  two-bs-edges-hide-an-amenable-q8-splitting: that obtains a genuinely nonamenable free edge by duplicating the BS actor; this obtains a Kazhdan edge but again exposes a transverse amenable decomposition.
  kazhdan-stabilizer-collapses-shared-pauli-sign: that gives a positive exact-actor collapse when a Kazhdan stabilizer acts on infinitely many sites; this shows that a Kazhdan direct factor acting trivially on a finite selector supplies no such robustness.
---

Let \(P\) be the five-generator Q8/\(BS(2,3)\) terminal group, and write
\(c\) for its central involution. Thus
\[
 c\ne1\text{ in }P,\qquad
 \pi(c)=I
\]
for every exact finite-dimensional unitary representation \(\pi\) of
\(P\), while \(P\) is hyperlinear.

Let \(T=SL_3(\mathbb Z)\), and put
\[
 H=T\times\langle c\rangle.
\]
Then \(H\) has property \((T)\). Let
\[
 K=\langle x,y,z\mid z^2=1,\ x^2=y^2=z,\
 [z,x]=[z,y]=1,\ yx=zxy\rangle\cong Q_8,
\]
and let \(H\) act on \(K\) as follows: \(T\) acts trivially, while \(c\)
interchanges \(x,y\) and fixes \(z\).

Define
\[
 B=K\rtimes H,\qquad
 D=(T\times P)\times\langle z\rangle,\qquad
 C=H\times\langle z\rangle,
\]
and form
\[
 \Omega=B*_C D.                                          \tag{KES1}
\]

Then:

1. \(C\cong SL_3(\mathbb Z)\times C_2\times C_2\) is a nonamenable
   property-\((T)\) edge group.
2. Bass--Serre normal form gives
   \[
   z\in Z(\Omega),\qquad z\ne1.                           \tag{KES2}
   \]
3. Every exact finite-dimensional unitary representation of \(\Omega\)
   kills \(z\).
4. Nevertheless
   \[
   \Omega\cong T\times\Omega_0,                           \tag{KES3}
   \]
   where
   \[
   \Omega_0=
   (K\rtimes\langle c\rangle)
   *_{\langle c\rangle\times\langle z\rangle}
   (P\times\langle z\rangle).                            \tag{KES4}
   \]
   The edge in (KES4) is finite. Both vertices are hyperlinear, so
   \(\Omega_0\), and hence \(\Omega\), are hyperlinear.

Thus \(\Omega\) has matrix almost-representations with defects tending to
zero and
\[
 \|Z-I\|_2\longrightarrow\sqrt2.                         \tag{KES5}
\]
Putting a Kazhdan group literally on the terminal edge does not robustify
finite-dimensional invisibility when the Kazhdan factor acts trivially on
the selector. It merely disguises a direct product and a finite transverse
edge.

A successful property-\((T)\) replacement must make the Kazhdan packet
itself act irreducibly on the marked structure. The normal-generation
fence for the compressed Kun--Thom vertex rules out doing this through a
finite packet action trivial on the compressed copy; the infinite-site
shared-center route remains open. No nonhyperlinear group is proved here.

DERIVATION
finite-transverse-splitting-of-kazhdan-edge-sign
