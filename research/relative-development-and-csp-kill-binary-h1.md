---
rg: 2
id: relative-development-and-csp-kill-binary-h1
kind: route
title: Pull flat cochains to the Iwahori development and kill their monodromy by one root power
target: binary-iwahori-h1-vanishes-at-odd-levels
requires:
  - iwahori-square-free-bs14-presentation
  - proper-torus-diagonal-code-is-incomplete-cover-curl
  - odd-principal-kernel-is-one-root-normal-closure
  - fourth-power-mersenne-reynolds-levels-have-diagonal-crt-coupling
---

Although the identifier records the earlier congruence-subgroup route, the
proof below uses the stronger exact Mennicke normal-generation theorem.

## 1. The relative development

Put

\[
 P_\infty=\langle r,t\mid rtr^{-1}=t^4\rangle.
\]

The exact square-free presentation can be written as the relative
presentation

\[
 \Gamma=\left\langle P_\infty,x\ \middle|\
 x^2,\ xrxr,\ (xt)^3,\ (xt^2r)^3\right\rangle.          \tag{RDP1}
\]

Let

\[
 N_\infty=\langle r,x\rangle,\qquad
 A_\infty=\langle a\rangle,\ a=xt,\qquad
 B_\infty=\langle b\rangle,\ b=xt^2r.
\]

The coset development \(X\) of (RDP1) has

\[
 \begin{aligned}
 X^{(0)}&=P_\infty\backslash\Gamma,\\
 X^{(1)}&=N_\infty\backslash\Gamma,\\
 X^{(2)}&=(A_\infty\backslash\Gamma)
          \sqcup(B_\infty\backslash\Gamma).             \tag{RDP2}
 \end{aligned}
\]

The edge \(N_\infty g\) has endpoints
\(P_\infty g,P_\infty xg\). The \(A_\infty g\)-face has boundary

\[
 N_\infty g,\quad N_\infty ag,\quad N_\infty a^2g,      \tag{RDP3}
\]

and the analogous formula with \(b\) gives the other face family.

For completeness, simple connectedness here is not an additional group
theorem. A path in the relative Cayley complex gives a word alternating
elements of \(P_\infty\) with \(x\). The relations \(x^2\) and \(xrxr\)
fold the oriented \(x\)-edges precisely to the
\(N_\infty\)-cosets in (RDP2). The two remaining relators give exactly the
triangles (RDP3). Since (RDP1) is an exact presentation of \(\Gamma\),
the relative van Kampen lemma reduces every closed relative word by these
cells. Hence

\[
 \pi_1(X)=1,\qquad H^1(X;\mathbb F_2)=0.                 \tag{RDP4}
\]

This is the standard simply connected development of an exact relative
presentation, spelled out to avoid assuming that a later nonfree quotient
is a covering space.

## 2. The finite quotient is the parity complex

Let \(K_m=\ker q_m\). The group \(K_m\) acts on the right of \(X\).
For each \(S_\infty\) among \(P_\infty,N_\infty,A_\infty,B_\infty\),
normality of \(K_m\) gives a boundary-compatible bijection

\[
 S_\infty\backslash\Gamma/K_m
 \longrightarrow S_m\backslash G_m,\qquad
 S_\infty gK_m\longmapsto S_mq_m(g).                    \tag{RDP5}
\]

Thus

\[
 Y_m=X/K_m
\]

is exactly \(K_{H,m}\), not merely a homotopy model of it.

This also audits the factor-two issue. For \(m=4^n-1\), let
\(c=q_m(r^n)\). The CRT signs show that \(c\) is a nonglobal central
involution and \(c\in H_m\subset N_m\). The cells \(A_mg\) and \(A_mcg\)
are distinct: equality would force the order-two element \(c\) into the
order-three group \(A_m\). Their three boundary edges agree because
\(c\) is central and lies in \(N_m\). The same holds for the \(B_m\)
cells. Both members of every pair occur in (RDP5), so the quotient keeps
the corrected face multiplicity.

## 3. Pullback gives a monodromy character

Let \(z\) be a cellular one-cocycle on \(Y_m\), and let
\(\pi:X\to Y_m\) be the quotient map. By (RDP4), there is a vertex
function \(F:X^{(0)}\to\mathbb F_2\) such that

\[
 \pi^*z=\delta F.                                       \tag{RDP6}
\]

For \(k\in K_m\), define

\[
 \chi_z(k)=F(vk)+F(v),                                  \tag{RDP7}
\]

where \(v\) is any vertex of \(X\). This does not depend on \(v\).
Indeed, for an edge from \(v\) to \(w\), the difference between the two
values in (RDP7) is

\[
 (\delta F)(ek)+(\delta F)(e)
 =(\pi^*z)(ek)+(\pi^*z)(e)=0,                           \tag{RDP8}
\]

and the one-skeleton is connected. Using \(vk\) as a new base vertex
shows

\[
 \chi_z(k\ell)=\chi_z(k)+\chi_z(\ell).                  \tag{RDP9}
\]

Thus \(\chi_z:K_m\to\mathbb F_2\) is a character. Changing \(z\) by a
coboundary changes \(F\) by a \(K_m\)-invariant function and does not
change \(\chi_z\). Conversely, if \(\chi_z=0\), then \(F\) is
\(K_m\)-invariant, descends to a vertex function on \(Y_m\), and (RDP6)
says that \(z\) is its coboundary. We have therefore proved the injection

\[
 H^1(Y_m;\mathbb F_2)
 \hookrightarrow\operatorname{Hom}(K_m,\mathbb F_2).    \tag{RDP10}
\]

No freeness of the action was used. In fact (RDP7) gives the exact
stabilizer rule

\[
 vk=v\quad\Longrightarrow\quad\chi_z(k)=0.              \tag{RDP11}
\]

## 4. Mennicke kills the monodromy

The element \(t^m\) belongs to \(K_m\cap P_\infty\), so it fixes the base
vertex \(P_\infty\) and (RDP11) gives \(\chi_z(t^m)=0\). More generally,
for every \(\gamma\in\Gamma\),

\[
 \gamma^{-1}t^m\gamma
\]

fixes the vertex \(P_\infty\gamma\), because

\[
 (P_\infty\gamma)(\gamma^{-1}t^m\gamma)
 =P_\infty t^m\gamma=P_\infty\gamma.                    \tag{RDP12}
\]

Hence \(\chi_z\) vanishes on every \(\Gamma\)-conjugate of \(t^m\).
The exact normal-generation identity gives

\[
 K_m=\langle\!\langle t^m\rangle\!\rangle_\Gamma.       \tag{RDP13}
\]

Therefore \(\chi_z=0\). By (RDP10), \(z\) is a coboundary, proving
(BIH2)--(BIH3).

Finally, \(P_\infty\) together with \(x\) generates \(\Gamma\), so the
one-skeleton of \(Y_m\) is connected. Its binary vertex-coboundary space
has dimension \(V_m-1\), and (BIH3) gives (BIH4).


## Independent prime-level corroboration

This is not used in the proof. Pedro H. Amorim, Isadora V. Picinini,
Bruno R. Ramos, and Thiago Verissimo, *On the abelianization of
congruence subgroups of SL2 over S-integers*, arXiv:2608.17763,
Theorem 3.4 and Corollary 3.7, compute for
\(A=\mathbb Z[1/2]\)

\[
 H_1(\Gamma(A,pA),\mathbb Z)\cong
 \begin{cases}
  (\mathbb Z/p)^3\oplus\mathbb Z/3,&p>3,\\
  (\mathbb Z/3)^3,&p=3.
 \end{cases}                                             \tag{RDP14}
\]

Thus the principal subgroup has no binary character at every odd prime
level, independently confirming the prime-level shadow of the argument
above. The exact normal-generation proof is what treats all composite odd
levels at once. Source: https://arxiv.org/html/2608.17763.
