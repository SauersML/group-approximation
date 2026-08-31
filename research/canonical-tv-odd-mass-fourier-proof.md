---
rg: 2
id: canonical-tv-odd-mass-fourier-proof
kind: route
title: Fourier-compute the canonical mass of every TV character
target: canonical-sign-corners-maximally-mix-the-tv-odd-spectrum
requires:
  - tv-zero-noise-cell-is-an-abelian-torsor
---

# Fourier-compute the canonical mass of every TV character

## 1. Minimal projections of the torsor subgroup

Let

$$
H=(C_2)^P,
\qquad |P|=n,
$$

and identify its dual with the subsets \(\beta\subseteq P\).  The
corresponding character is

$$
\chi_\beta(h)=\prod_{p\in\beta}h(p).
$$

Its minimal Fourier projection in \(\mathbb C[H]\) is

$$
E_\beta
 =\frac{1}{|H|}
   \sum_{h\in H}\chi_\beta(h)h.                         \tag{1}
$$

Equivalently, if \(Q_p\) denotes the coordinate reflection, then

$$
E_\beta
 =\prod_{p\in\beta}\frac{1-Q_p}{2}
  \prod_{p\notin\beta}\frac{1+Q_p}{2}.                 \tag{2}
$$

The projections \(E_\beta\) are mutually orthogonal and sum to one.

## 2. Restriction of the canonical group trace

Suppose \(H\) embeds in a group \(G\).  The canonical group trace is

$$
\tau_G\left(\sum_{g\in G}a_gg\right)=a_1.              \tag{3}
$$

The identity coefficient in (1) is \(1/|H|\).  Faithfulness of the copy of
\(H\) ensures that no other \(h\in H\) becomes the identity in \(G\).
Therefore

$$
\tau_G(E_\beta)=\frac1{|H|}=2^{-n}                     \tag{4}
$$

for every \(\beta\).

Let \(z\in H\) be the constant-minus-one element.  It is nontrivial, so

$$
\tau_G\left(\frac{1-z}{2}\right)=\frac12.              \tag{5}
$$

Moreover,

$$
\chi_\beta(z)=(-1)^{|\beta|}.                           \tag{6}
$$

The negative spectral projection of \(z\) is consequently

$$
p_-=\frac{1-z}{2}
   =\sum_{|\beta|\ {\rm odd}}E_\beta.                  \tag{7}
$$

Assume \(z\) is central in \(G\).  Then \(p_-\) is central, so
\(p_-L(G)p_-\) is a reducing corner and the normalized corner trace is

$$
\tau_-(x)=2\tau_G(p_-xp_-).                            \tag{8}
$$

Equations (4), (7), and (8) give

$$
\tau_-(E_\beta)
 =\begin{cases}
   2^{1-n},&|\beta|\text{ odd},\\
   0,&|\beta|\text{ even}.
  \end{cases}                                          \tag{9}
$$

There are \(2^{n-1}\) odd subsets, of which exactly \(n\) are singletons.
Summing (9) over the two classes proves

$$
\tau_-\left(\sum_{|\beta|=1}E_\beta\right)
 =\frac{n}{2^{n-1}},                                   \tag{10}
$$

and

$$
\tau_-\left(\sum_{\substack{|\beta|\geq3\\|\beta|\ {\rm odd}}}E_\beta\right)
 =1-\frac{n}{2^{n-1}}.                                 \tag{11}
$$

The bad mass is therefore not a small artifact.  It tends to one as the
support size grows.

## 3. Quotients give only affine packets

Drop faithfulness and let the map from \(H\) into \(G\) have kernel
\(K\).  Its image is \(H/K\).  The characters which survive are exactly

$$
K^\perp
 =\{\chi\in\widehat H:\chi(k)=1\text{ for every }k\in K\}.  \tag{12}
$$

This is a linear subspace of \(\widehat H\).  If \(z\notin K\), imposing
the negative sign \(\chi(z)=-1\) cuts (12) by one affine equation.  The
canonical negative-corner trace is uniform on that affine packet by the
same identity-coefficient calculation in \(\mathbb C[H/K]\).

Suppose every singleton character \(\chi_{\{p\}}\) survives.  Then every
\(k\in K\) satisfies

$$
\chi_{\{p\}}(k)=k(p)=1
\qquad\text{for all }p\in P.                            \tag{13}
$$

Thus \(k=1\), so \(K\) is trivial and the full uniform law (9) returns.
A quotient cannot retain all honest atoms while deleting the
nondictators.

## 4. Quantitative moment form

The same obstruction appears in finite canonical microstates.  Let
\(\rho:H\to U(d)\) be an exact finite-dimensional representation, let
\(\operatorname{tr}_d\) be normalized trace, and assume

$$
\max_{1\neq h\in H}
 \left|\operatorname{tr}_d(\rho(h))\right|\leq\eta.     \tag{14}
$$

Let

$$
w_\beta
 :=\operatorname{tr}_d(\rho(E_\beta)).
$$

Fourier inversion gives

$$
w_\beta
 =\frac1{|H|}
   \sum_{h\in H}
    \chi_\beta(h)\operatorname{tr}_d(\rho(h)).          \tag{15}
$$

Hence

$$
\left|w_\beta-2^{-n}\right|
 \leq(1-2^{-n})\eta.                                   \tag{16}
$$

Put \(N_{\rm bad}=2^{n-1}-n\).  The raw weight of the odd nondictator
projections is at least

$$
N_{\rm bad}
 \left(2^{-n}-(1-2^{-n})\eta\right).                   \tag{17}
$$

The total negative-\(z\) weight is
\((1-\operatorname{tr}_d(\rho(z)))/2\), which is at most
\((1+\eta)/2\).  Whenever the right side below is positive, the
nondictator proportion after conditioning to the negative sector is at
least

$$
\frac{
  2N_{\rm bad}
  \left(2^{-n}-(1-2^{-n})\eta\right)
 }{1+\eta}.                                             \tag{18}
$$

As \(\eta\to0\), this converges to (11).  Thus canonical trace
approximation does not wash out the bad atoms; it forces their asymptotic
density.

## 5. Consequence for trace-selected cyclic networks

A group extension can add arbitrary cyclic relations outside \(H\), but
as long as \(H\) remains faithful, the canonical trace computation on
\(\mathbb C[H]\) is unchanged.  To retain only singleton spectra in the
\(J=-1\) sector one must introduce an additional reducing projection
\(p\) satisfying

$$
pE_\beta=0
\qquad
\text{for every odd }|\beta|\geq3.                     \tag{19}
$$

Relation (19) is the original BCS joint-spectral constraint in corner
form.  It is not supplied by the central sign projection \(p_-\), by a
group quotient retaining all singletons, or by the canonical group trace.

An augmentation-zero signed Hecke corner can in principle provide an
additional projection and is not ruled out here.  What this proof rules
out is treating the canonical \(J=-1\) corner of a source-dependent group
extension as if it already selected the desired non-CE TV trace.
