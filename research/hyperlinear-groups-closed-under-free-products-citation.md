---
rg: 2
id: hyperlinear-groups-closed-under-free-products-citation
kind: route
title: Import Brown--Dykema--Jung amalgamated free product embeddability at scalar amalgam, with the Kirchberg--Radulescu group criterion
target: hyperlinear-groups-closed-under-free-products
requires: []
---

Two literature inputs, both read verbatim from the arXiv PDF text on
2026-09-12.

> **Corollary 4.5** (Brown--Dykema--Jung, *Free entropy dimension in
> amalgamated free products*, arXiv:math/0609080v5).  Let `M_1 *_B M_2` be the
> amalgamated free product of tracial von Neumann algebras `M_1` and `M_2`
> over a hyperfinite von Neumann algebra `B`, and assume each `M_i` has
> separable predual and is embeddable in `R^omega`.  Then `M_1 *_B M_2` is
> embeddable in `R^omega`.

> **Theorem 8.5** (Pestov, *Hyperlinear and sofic groups: a brief guide*,
> arXiv:0804.3968; attributed there to Kirchberg, Radulescu Prop. 2.5, and
> Ozawa Prop. 7.1).  Let `G` be a countable group.  Then `VN(G)` embeds into
> `R^omega` if and only if `G` is hyperlinear.

Derivation.  For countable `H_1, H_2`, `L(H_1 * H_2)` is the reduced free
product `L(H_1) * L(H_2)` with respect to the regular traces.  This is the
case `B = C` of Corollary 4.5, and `C` is hyperfinite.  Each `L(H_i)` has
separable predual and, by Theorem 8.5, embeds in `R^omega`.  So `L(H_1 * H_2)`
embeds in `R^omega`, and by Theorem 8.5 again `H_1 * H_2` is hyperlinear.
