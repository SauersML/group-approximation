# A retraction for the rotation-loop subgroup in STW L

Date: 2026-09-04.

## Precisely which question is answered

Immediately before Problem L, Schafhauser--Tikuisis--White,
[Nuclear C*-algebras: 99 problems, Section 14](https://arxiv.org/html/2506.10902v2#S14),
ask whether the two canonical rotation loops give a direct summand of
the fundamental group of the automorphism group of the irrational
rotation algebra. We prove that assertion by exhibiting a group
retraction. The same proof applies after tensoring with O-infinity.

This answers that explicit subsidiary question. It does not exhibit
the other four generators requested in Problem L, and the full
Problem L remains open in the graph. Targeted searches on 2026-09-04
found the question still stated in STW v2 and no later resolution of
this particular assertion; this is not a certification of priority.
The argument uses standard K-theory and makes no Lean-verification claim.

## A general torus-splitting lemma

Let A be a unital C*-algebra and let
\(\gamma:\mathbb T^r\longrightarrow\operatorname{Aut}(A)\)
be a point-norm continuous action. Suppose there are unitaries
\(u_1,\ldots,u_r\in A\) satisfying

\[
   \gamma_z(u_j)=z_j u_j
   \qquad(z=(z_1,\ldots,z_r)\in\mathbb T^r).
\]

Suppose also that the unit class splits in K-theory: there is an
abelian-group homomorphism

\[
   \varepsilon:K_0(A)\longrightarrow\mathbb Z,
   \qquad \varepsilon([1_A])=1.
\]

Then
\(\gamma_*:\mathbb Z^r=\pi_1(\mathbb T^r,1)
\longrightarrow\pi_1(\operatorname{Aut}(A),\mathrm{id})\)
is split injective.

### Proof, including basepoints and group laws

For a loop \(\alpha:[0,1]\longrightarrow\operatorname{Aut}(A)\)
based at the identity, put

\[
   v_j^\alpha(t)=\alpha_t(u_j)u_j^*.
\]

This is a norm-continuous unitary loop based at \(1_A\).
The map \(E_j:\alpha\mapsto\alpha(u_j)u_j^*\) is a continuous
based map from the automorphism group to \(U(A)\). In particular,
it induces a homomorphism on fundamental groups even though
\(E_j\) need not be a homomorphism of topological groups.

Stabilize the unitary loop and apply Bott periodicity. Denote the
result by

\[
   b_j([\alpha])=
   \operatorname{Bott}\bigl([v_j^\alpha]\bigr)\in K_0(A),
\]

with the sign convention
\(\operatorname{Bott}([t\mapsto e^{2\pi it}1_A])=[1_A]\).
Thus \(b_j\) is homotopy invariant and additive under loop
concatenation. No claim that \(U(A)\) is already in the stable
homotopy range is needed: stabilization always supplies this map.

Define the explicit homomorphism

\[
  \rho:\pi_1(\operatorname{Aut}(A),\mathrm{id})
       \longrightarrow\mathbb Z^r,\qquad
  \rho([\alpha])=
     \bigl(\varepsilon(b_1([\alpha])),\ldots,
           \varepsilon(b_r([\alpha]))\bigr).
\]

An integer vector \(n=(n_1,\ldots,n_r)\) represents the torus loop
\(z_n(t)=(e^{2\pi i n_1t},\ldots,e^{2\pi i n_rt})\).
For its image under the action,

\[
   v_j^{\gamma\circ z_n}(t)=e^{2\pi i n_jt}1_A,
   \qquad b_j(\gamma_*n)=n_j[1_A].
\]

Consequently \(\rho\circ\gamma_*=\mathrm{id}_{\mathbb Z^r}\).
The fundamental group of a topological group is abelian, so the
retraction gives the internal direct-sum decomposition

\[
   \pi_1(\operatorname{Aut}(A),\mathrm{id})
       =\gamma_*(\mathbb Z^r)\oplus\ker\rho .
\]

The decomposition is algebraic on fundamental groups. It asserts
neither a continuous retraction of automorphism groups nor a
deformation retraction of spaces.

## Application to the irrational rotation algebra

Write \(A_\theta=C(\mathbb T)\rtimes_{\sigma_\theta}\mathbb Z\),
where \(\theta\) is irrational, and use the canonical unitaries
U,V with the usual torus action

\[
   \gamma_{(z,w)}(U)=zU,\qquad
   \gamma_{(z,w)}(V)=wV.
\]

The rotation \(\sigma_\theta\) is homotopic to the identity on
\(C(\mathbb T)\), so its induced maps on both K-groups are the
identity. The Pimsner--Voiculescu exact sequence therefore gives

\[
  0\longrightarrow K_0(C(\mathbb T))\cong\mathbb Z
    \xrightarrow{\iota_*}K_0(A_\theta)
    \xrightarrow{\partial}K_1(C(\mathbb T))\cong\mathbb Z
    \longrightarrow0.
\]

Here \(\iota_*(1)=[1_{A_\theta}]\). Choose q with
\(\partial q=1\). Every x has a unique expression
\(x=m[1]+nq\): take \(n=\partial x\), then use exactness and
injectivity of \(\iota_*\). Hence

\[
   \varepsilon(m[1]+nq)=m
\]

is a homomorphism with \(\varepsilon([1])=1\). Applying the lemma
with r=2 proves that the canonical rotation-loop subgroup is a
\(\mathbb Z^2\) direct summand.

Equivalently, for \(0<\theta<1\), one may use the usual basis
\([1],[p_\theta]\) and take the coefficient of \([1]\).
Only the integral group structure is used. The coefficient map
need not be positive, and one must not replace it by the trace,
whose range on \(K_0(A_\theta)\) is \(\mathbb Z+\theta\mathbb Z\).

The source for the exact sequence is Pimsner--Voiculescu,
[Exact sequences for K-groups and Ext-groups of certain cross-product
C*-algebras, J. Operator Theory 4 (1980), 93--118](https://www.theta.ro/jot/archive/1980-004-001/1980-004-001-005.pdf).
Bott periodicity is the same stable loop-to-\(K_0\) map appearing
in the evaluation construction in STW Section 14, equation (15).

## The Kirchberg counterpart and the remaining task

For \(A_\theta\otimes\mathcal O_\infty\), the unital inclusion
\(A_\theta\to A_\theta\otimes\mathcal O_\infty\) identifies the
K-groups and the unit class, as also used in STW Section 14.
Transport \(\varepsilon\) across this identification and use
\(U\otimes1,V\otimes1\). The same formula for \(\rho\) splits the
two rotation loops there too. This conclusion does not require
the asserted weak homotopy equivalence of automorphism groups.

If one uses the computation \(\pi_1\cong\mathbb Z^6\) reported in
STW, then \(\ker\rho\cong\mathbb Z^4\). The retraction proves the
splitting without needing that computation. Explicit loops forming
a basis of this kernel are not constructed here.

For later searches, every candidate loop can now be normalized into
the kernel: subtract the rotation loop with winding vector
\(\rho([\alpha])\). This removes its two known coordinates but
does not prove that four proposed residual loops generate the kernel.
