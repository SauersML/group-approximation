---
rg: 2
id: tv-zero-noise-cell-is-an-abelian-torsor
kind: claim
title: Each zero-noise Taller--Vidick cell is an abelian torsor times free involutions
artifacts:
  - research/tv-zero-noise-cell-torsor-elimination-proof.md
distinct_from:
  taller-vidick-positive-noise-collapses-central-sign: that proves every positive-noise presentation kills J; this classifies exactly the local presentation after the support discontinuously collapses at epsilon zero.
  linear-encoding-lcs-admits-odd-subset-cheats: that constructs cheating characters at strategy level under source hypotheses; this gives the exact universal group of one zero-noise outer cell.
  lcs-parity-gadgets-preserve-odd-dictator-affine-hull: that is a general scalar affine-hull closure theorem; this identifies the entire noncommutative local group, including the free coset involutions.
---

Fix one supported outer tuple \((W,U,C)\) in Taller--Vidick Definition 4.1,
with nonempty satisfying-assignment set \(S\).  At \(\epsilon=0\), the only
mask is \(\mu=1\), so \(g'=f^\uparrow g\).

After absorbing the folding signs into the generators, identify conditioned
\(W\)-queries by their restriction to \(S\).  Let

$$
K=\{+1,-1\}^{S}
$$

under pointwise multiplication, let \(H\leq K\) be the image of functions
lifted from \(U\), and let \(z\in H\) be the constant-minus-one function.
The exact local zero-noise presentation is

$$
A_hB_kB_{hk}=1
\qquad(h\in H,\ k\in K),                                \tag{1}
$$

with all three factors commuting and involutory, together with
\(A_z=J\).

Its universal group is

$$
\Gamma_{\rm cell}
 \cong H\times\left(*_{q\in K/H}C_2\right),             \tag{2}
$$

where

$$
A_h\longmapsto(h,1),
\qquad
B_{hq}\longmapsto(h,t_q),
\qquad
J\longmapsto(z,1).                                      \tag{3}
$$

Thus every local cell is residually finite and already has scalar
\(J=-1\) representations.  If
\(P=\{y|_U:y\in S\}\), then \(H\cong\{+1,-1\}^{P}\).
The possible scalar \(A\)-profiles with \(J=-1\) are exactly the odd
subsets of \(P\); there are \(2^{|P|-1}\), of which only the \(|P|\)
singleton profiles are dictators.  Each profile extends by choosing
arbitrary scalar signs for the free coset involutions.

Consequently the exact \(\epsilon=0\) support does preserve honest perfect
strategies, but no local relation distinguishes dictators from odd
high-degree characters.  Any perfect-completeness decoder or
infinite-dimensional seed must act through cross-cell identifications; it
cannot be hidden inside one long-code cell.

This is a local presentation theorem, not a global soundness claim.
