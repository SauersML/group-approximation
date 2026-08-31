---
rg: 2
id: embed-asymmetric-amalgam-in-a-symmetric-mf-double
kind: route
title: Preserve reduced words inside a symmetric MF double
target: common-mf-envelope-fences-asymmetric-amalgams
requires:
  - mf-is-invariant-under-symmetric-doubling
  - mf-positive-controls
---

# Preserve reduced words inside a symmetric MF double

## 1. Construct the map

Write
\[
D=M*_{j(H)}M
\]
and let \(\iota_i:M\hookrightarrow D\) denote its two canonical vertex
maps. Equation (CME1) gives
\[
\iota_0j_0\theta_0(h)=\iota_1j_1\theta_1(h)
\qquad(h\in H).
\]
The universal property of the amalgam therefore produces a homomorphism
\[
\Phi:G_0*_{H}G_1\longrightarrow D,\qquad
\Phi|_{G_i}=\iota_i j_i.                                 \tag{1}
\]

## 2. Check injectivity by normal form

Take a nontrivial reduced word
\[
g_1g_2\cdots g_r
\]
in \(G_0*_{H}G_1\). If \(r\geq2\), adjacent syllables lie in different
vertices and every \(g_k\) lies outside \(\theta_{\varepsilon(k)}(H)\).
We claim
\[
j_{\varepsilon(k)}(g_k)\notin j(H).                      \tag{2}
\]
Indeed, equality with \(j(h)=j_{\varepsilon(k)}
\theta_{\varepsilon(k)}(h)\) would contradict injectivity of
\(j_{\varepsilon(k)}\).

Thus (1) sends the word to an alternating word in the two copies of \(M\),
with every syllable outside their common subgroup \(j(H)\). It remains
reduced in \(D\), so the amalgam normal-form theorem makes its image
nontrivial. The case \(r=1\) follows directly from injectivity of
\(\iota_i j_i\). Hence \(\Phi\) is injective, proving (CME3).

Notice what is and is not used. No intersection condition beyond (CME1) is
missing: injectivity of each \(j_i\) itself gives (2). No amenability or
Kazhdan hypothesis on \(H\) enters the argument.

## 3. Apply the symmetric theorem

By **mf-is-invariant-under-symmetric-doubling**, operator MF of \(M\) implies
operator MF of \(D=M*_{j(H)}M\), for the arbitrary subgroup \(j(H)\leq M\).
By subgroup heredity in **mf-positive-controls**, the embedded group
\(\Phi(G_0*_H G_1)\) is operator MF. This proves (CME2).

This step uses Shulman's **group-level** symmetric-double corollary. It does
not assume that the full group C*-algebra \(C^*(M)\) is MF. Conversely, it
also supplies no trace on the double.

## 4. Exact asymmetric frontier

The theorem eliminates a broad class of cosmetic asymmetries:

- replacing one vertex of a symmetric double by a subgroup of the other;
- placing both vertices inside a common MF semidirect-product or matrix
  envelope with synchronized edge maps;
- decorating an arbitrary edge, even a property-\((T)\) edge, while retaining
  such a common envelope.

For C*-algebras, **shulman-amalgam-mf-criterion** gives the exact enlargement
of this sufficient condition: compatible embeddings of the two vertex
algebras into one norm matrix corona are necessary and sufficient for the
full amalgam to be MF. Therefore a genuinely new asymmetric operator-norm
attack must prove incompatibility of the edge restrictions, rather than
only non-isomorphism of the vertex presentations.

The normalized-Hilbert--Schmidt problem is orthogonal. Operator-norm MF
separation may live on vanishing-rank corners, so this route neither proves
nor refutes hyperlinearity of the asymmetric amalgam. The nonhyperlinear
root remains open.
