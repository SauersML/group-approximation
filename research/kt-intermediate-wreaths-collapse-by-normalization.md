---
rg: 2
id: kt-intermediate-wreaths-collapse-by-normalization
kind: route
title: Normalize the original Gamma commutant and collapse every normal-closure lamp orbit
target: kt-intermediate-wreaths-missing-normal-core-not-hl
requires:
  - kun-thom-nonsofic-wreath
  - kazhdan-compression-pairs-normalize-all-tracial-models
  - kun-thom-wreath-sofic-radical-is-fibre-parity-kernel
---

Let rho:W_K->U(M) be an arbitrary tracial matrix-ultraproduct
homomorphism and D=rho(Gamma)' cap M. The lamp a_K commutes with
Gamma since Gamma<=K. By the second premise rho(G) normalizes D,
so every lamp image rho(a_(gK)) lies in D.

It follows that each gamma in Gamma fixes every lamp image under
conjugation. Conjugating this assertion by any h in G shows that
h Gamma h^-1 also fixes every lamp image (the conjugation permutes
the whole set of lamps). Thus N=<<Gamma>> fixes every lamp image.
Consequently rho(a_(nx) a_x)=1 for every n in N and x in G/K.
Choose n in N\K and x=K. The two lamp sites are distinct, so their
product is nontrivial. No faithful rho exists. Composing any map
to a hyperlinear group with its ultraproduct embedding gives the
stronger universal-kernel assertion.

The first premise verifies the original pair's Kazhdan and compression
hypotheses, not any such hypothesis on K. The last premise identifies
the boundary W_N as residually finite. The analytic step is credited
to Jihao Liu (internality) and Andreas Thom (conditional normalization).
