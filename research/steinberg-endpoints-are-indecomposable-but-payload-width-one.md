---
rg: 2
id: steinberg-endpoints-are-indecomposable-but-payload-width-one
kind: claim
title: Steinberg endpoints are uniformly indecomposable but have payload width one
artifacts:
  - research/crt-surjectivity-and-tau-give-steinberg-nonpeeling.md
distinct_from:
  modular-vertex-extension-does-not-force-congruence: that constructs high-dimensional infinite-image edge constituents and shows modular extension alone is not congruence; this constructs actual congruence endpoints whose vertex and edge restrictions are nevertheless uniformly indecomposable.
  quantum-expander-relative-commutant-rounding: that gives an abstract commutant estimate from a supplied quantum-expander channel; this obtains the estimate for the concrete Iwahori edge from congruence expansion.
  bounded-payload-congruence-tensors-have-uniform-capture: that repairs an authenticated tensor hull; this shows why payload dimension must be minimized after absorbing every congruence endpoint factor and cannot be read from vertex irreducible dimensions.
---

Let
\[
 A=\operatorname{PSL}_2(\mathbb Z[1/2]),\qquad
 G_p=\operatorname{PSL}_2(\mathbb F_p)
\]
for odd primes \(p\geq5\), and let
\[
 \eta_p=\operatorname{St}_p\circ\operatorname{red}_p:
 A\longrightarrow U(p)                                  \tag{SIP1}
\]
be the \(p\)-dimensional Steinberg representation after reduction modulo
\(p\). For either modular vertex \(V_\pm\) and for their common index-three
Iwahori edge \(B\), the reductions
\[
 V_\pm\longrightarrow G_p,\qquad B\longrightarrow G_p   \tag{SIP2}
\]
are onto. Consequently all three restrictions of \(\eta_p\) are irreducible.

More strongly, fix any finite symmetric generating set \(S_B\) of \(B\).
There is a constant \(\kappa_B>0\), independent of \(p\), such that every
\(T\in M_p(\mathbb C)\) satisfies
\[
 \sum_{s\in S_B}
 \|[T,\eta_p(s)]\|_{2,p}^2
 \geq
 \kappa_B\|T-\operatorname{tr}_p(T)1\|_{2,p}^2.          \tag{SIP3}
\]
In particular, if \(e\) is a projection of normalized rank \(t\), then
\[
 \max_{s\in S_B}\|[e,\eta_p(s)]\|_{2,p}
 \geq
 \sqrt{\frac{\kappa_B}{|S_B|}\,t(1-t)}.                 \tag{SIP4}
\]
Thus no positive-density proper carrier can even approximately peel these
representations into bounded cyclic, dihedral, or other common reducing
pieces.

Nevertheless the two vertex restrictions of \(\eta_p\) form an exact
compatible Iwahori endpoint. In the bounded-payload tensor hull they are the
single block
\[
 (\mathbf1,\mathbf1)\otimes\eta_p,                       \tag{SIP5}
\]
so their payload width is one and their congruence-capture distance is zero.

Therefore unbounded vertex dimension, edge irreducibility, and even a
uniform adjoint expansion gap do not characterize alternative (3) of
**approximate-central-tensor-coverage-forces-capture**. The relevant
quantity is the minimum payload width after every compatible congruence
endpoint factor has been absorbed. A genuine obstruction must retain
positive distance from all such absorptions; equivalently it must involve
noncongruence alignment of the two opposite extension structures, not
literal high-dimensional indecomposability alone. This does not construct
such a misaligned sequence, and the root remains open.

DERIVATION
crt-surjectivity-and-tau-give-steinberg-nonpeeling
