---
rg: 2
id: ghb7-degree-two-inflation-via-universal-rf
kind: route
title: Residual finiteness of every hyperbolic group already inflates every degree-two cyclic class on the index-7 kernel of GHB_2(7)
target: ghb7-finite-index-subgroup-has-degree-two-inflation-surjectivity
requires:
  - hyperbolic-finite-residual-is-torsion-free
  - universal-hyperbolic-vtf-iff-rf
  - cckw-ghb2-kms-group-structure
  - ghb7-normal-subgroup-b2-is-orbit-euler-count
  - degree-two-inflation-onto-makes-z-extension-centres-survive
artifacts:
  - research/artifacts/hyperbolic-goodness-rf-plus-high-degree-reduction-2026-09-16.md
---

This route weakens the hypothesis of `ghb7-degree-two-inflation-via-hyperbolic-goodness`
from universal goodness to universal residual finiteness. The argument is Section 6 of
the artifact.

**Lemma (RF central extensions are inflated).** Let `K` be a group, `n >= 1`, and
`x in H^2(K;Z/n)` with trivial action. Let `x` classify the central extension
`1 -> Z/n -> E -π-> K -> 1`. If `E` is residually finite, then `x` is inflated from a
finite quotient of `K`.

*Proof.* Since `E` is residually finite and `Z/n` is finite, there is a finite-index
normal `E_0 <= E` with `E_0 ∩ Z/n = 1`. Put `N = π(E_0)`, normal of finite index in `K`,
and `Q = E/E_0`. The map `E -> K/N` is onto with kernel `π^{-1}(N) = E_0·(Z/n)`. So
`1 -> Z/n -> Q -> K/N -> 1` is a central extension, with class `y` say. The homomorphism
`E -> Q ×_{K/N} K`, `e ↦ (eE_0, π(e))`, is the identity on `Z/n` and covers the identity
of `K`. By the short five lemma it is an isomorphism of extensions. The fibre product is
the pullback of `Q` along `K -> K/N`, and its class is `inf(y)`. Hence `x = inf(y)`.
`QED`

**Derivation.**

1. By `hyperbolic-finite-residual-is-torsion-free` and `universal-hyperbolic-vtf-iff-rf`
   (item 2 => item 1), every word-hyperbolic group is residually finite.
2. `G = G_{HB_2}(7)` is word-hyperbolic (`cckw-ghb2-kms-group-structure`, item 1). The
   subgroup `K_7 = Ker(G -> Z/7, a,b,c ↦ 1)` has finite index, so it is hyperbolic, and
   `b_2(K_7;Q) = 6 >= 1` (`ghb7-normal-subgroup-b2-is-orbit-euler-count`).
3. Let `n >= 1` and `x in H^2(K_7;Z/n)`. Its central extension `E` has finite kernel, so
   it is quasi-isometric to `K_7` and hyperbolic. By step 1 it is residually finite.
4. By the Lemma, `x` is inflated from a finite quotient of `K_7`. This is property (G2) of
   `degree-two-inflation-onto-makes-z-extension-centres-survive` for `K_7`. `QED`

**Reading.** A positive answer to Gromov's question would give
`ghb7-finite-index-subgroup-has-degree-two-inflation-surjectivity`. Through
`ghb7-centre-survival-via-degree-two-goodness` and
`ghb7-instability-via-visible-central-extension`, it would then show that `GHB_2(7)` is
not flexibly HS stable. Universal goodness is not needed.
