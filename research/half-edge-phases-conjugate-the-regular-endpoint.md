---
rg: 2
id: half-edge-phases-conjugate-the-regular-endpoint
kind: route
title: Lift half-edge intervals to a diagonal conjugator and count its parabolic commutator
target: mersenne-phases-have-explicit-exact-core-bend
requires:
  - link-thresholds-need-macroscopic-phase-frustration
  - fourth-power-mersenne-reynolds-levels-have-diagonal-crt-coupling
  - iwahori-square-free-bs14-presentation
  - mersenne-phases-refute-diagonal-iwahori-decoder
---

Let

\[
 H=\langle r\rangle,\qquad P=\langle r,t\rangle,\qquad
 N=\langle r,x\rangle
\]

inside \(Q\). The oriented half-edges of the graph are canonically

\[
 H\backslash Q\longrightarrow
 \{(v,e):v\text{ is an endpoint of }e\},\qquad
 Hg\longmapsto(Pg,Ng).                                  \tag{HEP1}
\]

This is a bijection because \(H=P\cap N\). Define a binary function on
group coordinates by

\[
 d_\eta(g)=\eta_{Pg}(Ng).                               \tag{HEP2}
\]

It is left \(H\)-invariant. Put

\[
 U_\eta=M_{(-1)^{d_\eta}}.
\]

For a basis vector \(\delta_g\),

\[
 U_\eta\lambda(x)U_\eta^*\delta_g
 =(-1)^{d_\eta(g)+d_\eta(xg)}\delta_{xg}.               \tag{HEP3}
\]

The two terms in the exponent are exactly the two half-edge indicators
at the endpoints of \(Ng\). Thus their sum is \(c_\eta(Ng)\). Since
\(c_\eta\) is left \(N\)-invariant and \(x\in N\),

\[
 c_\eta(Nxg)=c_\eta(Ng),
\]

so (HEP3) is precisely

\[
 U_\eta\lambda(x)U_\eta^*
 =M_{(-1)^{c_\eta}}\lambda(x).                          \tag{HEP4}
\]

Left \(H\)-invariance of \(d_\eta\) also gives

\[
 [U_\eta,\lambda(r)]=0.                                 \tag{HEP5}
\]

Conjugating the canonical regular endpoint by \(U_\eta\) now proves the
exact identities (ECB2)--(ECB3). It remains only to count the displacement
of \(T=\lambda(t)\).

Fix a vertex \(Pg_v\). Every group coordinate over this vertex has a unique
form

\[
 r^k t^z g_v,\qquad 0\leq k<2n,\quad z\in\mathbb Z/m\mathbb Z, \tag{HEP6}
\]

because \(|H|=2n\) and \(P=H U\). The associated half-edge label is \(z\).
The fourth-power relation gives

\[
 t r^k t^z
 =r^k t^{z+4^{-k}},                                     \tag{HEP7}
\]

with exponents read modulo \(m\). Hence left multiplication by \(t\)
shifts the interval label in the \(k\)-th \(H\)-layer by \(4^{-k}\).

For a cyclic interval of length \((m-1)/2\), translation by a nonzero step
whose least absolute residue is \(\ell\leq(m-1)/2\) changes exactly
\(2\ell\) indicator values. The powers \(4^{-k}\), for
\(0\leq k<2n\), run twice through the inverse of

\[
 1,4,\ldots,4^{n-1}.
\]

Inversion only permutes this cyclic subgroup. Moreover

\[
 4^{n-1}<m/2,\qquad
 \sum_{j=0}^{n-1}4^j=\frac{m}{3}.                       \tag{HEP8}
\]

Thus the number of group coordinates over one vertex on which
\(d_\eta(tg)\neq d_\eta(g)\) is exactly

\[
 2\cdot2\sum_{j=0}^{n-1}4^j=\frac{4m}{3}.               \tag{HEP9}
\]

There are \(|P|=2nm\) group coordinates over each vertex. Therefore

\[
 \frac{|\{g:d_\eta(tg)\neq d_\eta(g)\}|}{|Q|}
 =\frac{2}{3n}.                                         \tag{HEP10}
\]

Finally,

\[
 \begin{aligned}
 \|U_\eta T U_\eta^*-T\|_2^2
 &=\frac1{|Q|}\sum_{g\in Q}
   |(-1)^{d_\eta(g)+d_\eta(tg)}-1|^2\\
 &=4\frac{|\{g:d_\eta(tg)\neq d_\eta(g)\}|}{|Q|}
 =\frac{8}{3n}.                                         \tag{HEP11}
 \end{aligned}
\]

This proves (ECB4)--(ECB5). Notice that the corrected order
\(|H|=2n\) is used twice: it supplies the \(2n\) layers in (HEP6), and it
is exactly why every fourth-power step occurs twice in (HEP9).
