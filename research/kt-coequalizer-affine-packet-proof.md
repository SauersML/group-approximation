---
rg: 2
id: kt-coequalizer-affine-packet-proof
kind: route
title: Reduce every finite-dimensional Kun-Thom coequalizer sector to one finite quotient
target: fd-invisible-coequalizers-have-only-affine-tv-packets
requires:
  - fd-invisibility-of-compression
  - tv-zero-noise-cell-is-an-abelian-torsor
---

# Reduce every finite-dimensional Kun-Thom coequalizer sector to one finite quotient

## 1. A literal finite presentation

Fix finite presentations

\[
 K=\langle T\mid R_K\rangle,
 \qquad
 G=\langle S\mid R_G\rangle.                            \tag{1}
\]

Let \(\Lambda\leq\Gamma\leq G\). Choose words
\(\ell_1,\ldots,\ell_a\in F(S)\) generating \(\Lambda\), and choose
words \(c_1,\ldots,c_m\in F(S)\) representing elements
\(\gamma_i\in\Gamma\). For each
\(\alpha_i\in\operatorname{Aut}(K)\) and \(t\in T\), choose a
\(T\)-word \(w_{i,t}\) representing \(\alpha_i(t)\).

The coequalizer group in the claim has the finite presentation

\[
 \Pi=
 \left\langle T,S\ \middle|\
 \begin{array}{l}
  R_K,\ R_G,\\
  [t,\ell_j]=1
    \quad(t\in T,\ 1\leq j\leq a),\\
  c_i t c_i^{-1}=w_{i,t}
    \quad(t\in T,\ 1\leq i\leq m)
 \end{array}
 \right\rangle .                                        \tag{2}
\]

Commuting the two finite generating sets gives
\([K,\Lambda]=1\), and the last line gives
\(\gamma_i k\gamma_i^{-1}=\alpha_i(k)\) for every \(k\in K\).

For the marked application, assume that \(z\in Z(K)\) is an involution
fixed by every \(\alpha_i\). One may add the finitely many relations

\[
 [z,s]=1\qquad(s\in S)                                  \tag{3}
\]

so that \(z\) is central in \(\Pi\). Everything below remains valid with
or without (3). We include (3) when interpreting \(z\) as an LCS mark.

Define the finite coinvariant quotient

\[
 K_\alpha
 =
 K\big/
 N_\alpha,\qquad
 N_\alpha=
 \left\langle\!\left\langle
  \alpha_i(k)k^{-1}:k\in K,\ 1\leq i\leq m
 \right\rangle\!\right\rangle_K.                        \tag{4}
\]

It is enough to use \(k\in T\) in (4).

## 2. Exact finite-dimensional restriction theorem

Assume that every finite-dimensional unitary representation
\(\rho:G\to U(d)\) satisfies

\[
 \rho(\Lambda)=\rho(\Gamma).                            \tag{5}
\]

This is the property proved for the pinned Kun-Thom compression in
\(fd\)-invisibility-of-compression.

Let \(\pi:\Pi\to U(d)\) be a finite-dimensional unitary
representation. The commutator relations in (2) give

\[
 [\pi(K),\pi(\Lambda)]=1.                               \tag{6}
\]

The restriction of \(\pi\) to \(G\) is a genuine representation of
\(G\), so (5) and (6) imply

\[
 [\pi(K),\pi(\Gamma)]=1.                                \tag{7}
\]

In particular \(\pi(\gamma_i)\) commutes with \(\pi(k)\). Applying
\(\pi\) to the last line of (2) therefore gives

\[
 \pi(\alpha_i(k))
 =\pi(\gamma_i)\pi(k)\pi(\gamma_i)^{-1}
 =\pi(k).                                               \tag{8}
\]

Thus \(N_\alpha\subseteq\ker(\pi|_K)\), and \(\pi|_K\) factors through
\(K_\alpha\).

Conversely, let \(\sigma:K_\alpha\to U(d)\) be any representation.
Define a representation on the generators of (2) by

\[
 \widetilde\sigma(t)=\sigma(\bar t)
 \quad(t\in T),
 \qquad
 \widetilde\sigma(s)=I
 \quad(s\in S).                                         \tag{9}
\]

The \(K\)- and \(G\)-relations hold. The commutator relations hold
because the \(G\)-image is trivial. The conjugacy relations become

\[
 \sigma(\bar t)=\sigma(\overline{\alpha_i(t)}),          \tag{10}
\]

which is exactly a relation in the quotient (4). Relations (3), when
present, also hold. Hence (9) extends \(\sigma\) to a representation of
\(\Pi\).

We have proved the exact equality

\[
 \{\pi|_K:\pi\in\operatorname{Rep}_{\rm fd}(\Pi)\}
 =
 \{\sigma\circ q:
   \sigma\in\operatorname{Rep}(K_\alpha)\},              \tag{11}
\]

where \(q:K\to K_\alpha\) is the quotient map. Notice that (11) is
stronger than a one-way soundness statement: every sector left by the
finite quotient really occurs in a finite-dimensional representation of
the full nonamenable interface.

## 3. Character packet on the TV torsor

Let

\[
 H=(C_2)^P\leq K
\]

be the finite abelian TV torsor group, and let \(z\in H\cap Z(K)\) be
the constant-minus-one element. Put

\[
 L=H\cap N_\alpha=\ker(H\longrightarrow K_\alpha),
 \qquad
 \bar H=H/L.                                            \tag{12}
\]

Assume first that \(\bar z\ne1\). Any character appearing in the
restriction to \(H\) of a representation which factors through
\(K_\alpha\) must be trivial on \(L\). If \(z\) acts as \(-I\), that
character must also satisfy \(\chi(z)=-1\). This proves one containment
in

\[
 {\cal P}_L
 =
 \{\chi\in\widehat H:
   \chi|_L=1,\ \chi(z)=-1\}.                            \tag{13}
\]

For the reverse containment, take \(\chi\in{\cal P}_L\). It descends to
a character \(\bar\chi\) of \(\bar H\). The finite-dimensional induced
representation

\[
 \operatorname{Ind}_{\bar H}^{K_\alpha}(\bar\chi)        \tag{14}
\]

is nonzero and contains \(\bar\chi\) on restriction to \(\bar H\).
Because \(\bar z\) is central in \(K_\alpha\), it acts as the scalar
\(\bar\chi(\bar z)=-1\) throughout (14). By Section 2, (14) extends to
a finite-dimensional representation of \(\Pi\). Thus every character
in (13) really occurs in a marked sector of \(\Pi\), proving that (13)
is the exact packet.

The annihilator

\[
 L^\perp=\{\chi\in\widehat H:\chi|_L=1\}                 \tag{15}
\]

is a linear subspace of \(\widehat H\). Equation (13) is its intersection
with one affine sign equation, so it is an affine packet.

## 4. Retaining every dictator forces every odd cheat

Identify \(\widehat H\) with subsets \(\beta\subseteq P\), with

\[
 \chi_\beta(h)=\prod_{p\in\beta}h(p).
\]

The honest dictator characters are the singletons
\(\chi_{\{p\}}\). Suppose each of them occurs in a finite-dimensional
\(z=-1\) representation of \(\Pi\). By (13),

\[
 \chi_{\{p\}}(\ell)=1
 \qquad(\ell\in L,\ p\in P).                            \tag{16}
\]

But \(\chi_{\{p\}}(\ell)=\ell(p)\). Equation (16) for every \(p\)
forces \(\ell=1\), and hence

\[
 L=1.                                                    \tag{17}
\]

Substituting (17) in (13) gives

\[
 {\cal P}_L
 =
 \{\chi_\beta:|\beta|\text{ is odd}\}.                  \tag{18}
\]

For \(|P|\geq3\), (18) contains the unwanted characters of every odd
degree at least three. The automorphic coequalizer has not produced the
dictator packet. It has reproduced the entire sign-compatible affine
slice.

In group-algebra language, let

\[
 p_-=\frac{1-\bar z}{2}\in\mathbb C[K_\alpha].           \tag{19}
\]

When all singleton characters survive, the restriction of the
\(p_-\)-sector to \(H\) contains every odd minimal Fourier projection.
It therefore cannot equal the signed-Hecke block whose \(H\)-spectrum is
only the singleton characters. This is exactly the missing
signed-corner-to-central-sign bridge needed for an LCS.

## 5. The all-or-terminal dichotomy

If \(\bar z=1\) in \(K_\alpha\), Section 2 implies

\[
 \pi(z)=I
 \quad\text{for every finite-dimensional }\pi:\Pi\to U(d). \tag{20}
\]

This is stronger exact soundness than pruning the nondictators: it deletes
every finite-dimensional \(z=-1\) sector, including all honest sectors.

Equation (20) does not by itself give a commuting-versus-quantum-
approximable gap. To obtain perfect commuting completeness, one must
first prove that \(z\ne1\) in \(\Pi\), or construct a tracial
representation with \(z\) nontrivial. To rule out
quantum-approximable perfect strategies, one must moreover prove that
\(z\) is trivial in all approximate representations. The image equality
(5) concerns genuine finite-dimensional representations only and supplies
neither assertion.

If both assertions were proved and \(\Pi\) were embedded mark-preservingly
in an LCS solution group without losing approximate triviality, the result
would be a finitely presented nonhyperlinear group. Thus the
\(\bar z=1\) branch is the terminal gate, not a completed compiler.

## 6. Scope of the no-go

The proof uses no amenability and no failure of property (T). It applies
precisely because the nonamenable interface has the very strong
finite-dimensional image-collapse property (5).

It rules out finite selector groups acted on through automorphic
coequalizer relations of the form (2). It does not rule out:

- genuinely nonnormal multi-double-coset Hecke operators;
- a nonautomorphic relation which does not preserve the finite selector
  group;
- a nonamenable operator-algebra edge which is not generated by a finite
  group; or
- the terminal \(\bar z=1\) construction supplemented by a quantitative
  approximate relative-commutant theorem.

These are the exact residual interfaces after the coequalizer
classification. No nonhyperlinear group is constructed here.
