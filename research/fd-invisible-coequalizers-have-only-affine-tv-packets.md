---
rg: 2
id: fd-invisible-coequalizers-have-only-affine-tv-packets
kind: claim
title: Finite-dimensionally invisible coequalizers have only affine TV packets
artifacts:
  - research/kt-coequalizer-affine-packet-proof.md
requires:
  - fd-invisibility-of-compression
distinct_from:
  canonical-sign-corners-maximally-mix-the-tv-odd-spectrum: that classifies canonical traces and ordinary quotients of the TV torsor; this derives the quotient itself from a nonamenable source-dependent Kun-Thom-style coequalizer and classifies all of its finite-dimensional restrictions.
  conjugacy-actions-cannot-prune-the-odd-tv-spectrum: that treats split semidirect actions and explicitly induces orbit representations; this allows a strict property-(T) compressor and arbitrary automorphic coequalizer relations.
  finite-selector-gadget-induction-barrier: that starts with one finite overgroup; this proves that the apparently infinite nonamenable interface reduces exactly to such a finite quotient in every finite-dimensional representation.
---

Let \(\Lambda\leq\Gamma\leq G\) be finitely generated groups with the
finite-dimensional image-collapse property

\[
 \rho(\Lambda)=\rho(\Gamma)                              \tag{1}
\]

for every finite-dimensional unitary representation \(\rho\) of \(G\).
The pinned Kun-Thom compressor has (1).

Let \(K\) be a finite group, let
\(\alpha_1,\ldots,\alpha_m\in\operatorname{Aut}(K)\), and choose
\(\gamma_i\in\Gamma\). Form the explicit source-dependent coequalizer

\[
 \Pi=
 \left\langle K,G\ \middle|\
 [K,\Lambda]=1,\quad
 \gamma_i k\gamma_i^{-1}=\alpha_i(k)
 \ (k\in K,\ 1\leq i\leq m)
 \right\rangle .                                        \tag{2}
\]

Finite generating sets suffice in (2), so \(\Pi\) is finitely presented
whenever \(G\) is. Put

\[
 K_{\alpha}
 =K\big/
 \left\langle\!\left\langle
   \alpha_i(k)k^{-1}:k\in K,\ 1\leq i\leq m
 \right\rangle\!\right\rangle_K .                       \tag{3}
\]

Then the restrictions to \(K\) of finite-dimensional representations of
\(\Pi\) are exactly the representations which factor through
\(K_{\alpha}\):

1. every finite-dimensional representation of \(\Pi\) factors on \(K\)
   through (3);
2. every representation of \(K_{\alpha}\) extends to \(\Pi\) by sending
   \(G\) to the identity.

Now let \(H=(C_2)^P\leq K\), and let \(z\in H\) be the
constant-minus-one element of a zero-noise Taller-Vidick cell. Let \(L\)
be the kernel of \(H\to K_{\alpha}\). If the image of \(z\) is nontrivial,
the \(H\)-characters occurring in finite-dimensional \(z=-1\) sectors of
\(\Pi\) are exactly

\[
 \{\chi\in\widehat H:\chi|_L=1,\ \chi(z)=-1\}.            \tag{4}
\]

This is an affine packet. In particular, if every honest singleton
character survives, then \(L=1\), and every odd character survives,
including every odd high-degree nondictator.

Thus a nonamenable property-(T) interface of the form (2) cannot turn the
central sign sector into the signed-Hecke dictator block. It has only two
outcomes:

- the finite quotient (3) retains the honest singleton sectors, in which
  case it also retains all odd cheats; or
- it kills at least one honest sector, possibly killing \(z\) and hence
  every finite-dimensional marked sector.

The second outcome can be useful only if one separately constructs a
perfect tracial representation with \(z\ne1\) and proves quantitative
collapse in all approximate finite-dimensional representations. That is
already the terminal nonhyperlinearity gate; the exact property-(T)
coequalizer alone does not prove it. The claim does not construct a
nonhyperlinear group.
