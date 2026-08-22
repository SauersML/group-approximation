---
rg: 2
id: llp-implies-weak-ucp-citation
kind: route
title: Import Ioana-Spaas-Wiersma Corollary 1.7 as quoted by Dogon, with the lifting argument sketched
target: llp-implies-weak-ucp-stability
requires: []
---

**Citation.**  Ioana--Spaas--Wiersma, *Cohomological obstructions to
lifting properties for full C*-algebras of property (T) groups*, GAFA 30
(2020) 1402--1438, arXiv:2006.01874, Corollary 1.7, as quoted by Dogon
arXiv:2211.10492v3, p. 4 (paragraph after Theorem 1.6): "by Corollary 1.7
in [28] any group `Gamma` such that `C^*(Gamma)` possesses Kirchberg's
local lifting property (LLP) is weakly ucp-stable"; the same implication
is used by Fournier-Facio--Willett arXiv:2603.18456 (their Remark 7.7:
weak ucp stability "is implied by the LLP").

**Argument sketch** (as in `llp-non-rf-kazhdan-non-hyperlinear-citation`,
recorded for self-containment).  A hyperlinear approximation defines a
*-homomorphism `C^*(Gamma) -> prod_U M_(d_n) / I_tau` into a tracial
matrix ultraproduct, a quotient of the bounded product.  LLP lifts its
restriction to each finite-dimensional operator system
`span(F cup F^(-1) cup {e})` to a ucp map into `prod M_(d_n)`; Arveson
extends the lift to `C^*(Gamma)`; Stinespring dilates each component to a
genuine representation whose corner agrees with the approximation on `F`
up to `o(1)` in normalized HS norm; a diagonal argument over an exhaustion
of `Gamma` converts the ultrafilter form to Dogon's sequential Def 1.5.

**Source note (2026-08-21 audit).**  Ioana--Spaas--Wiersma Corollary 1.7
verbatim carries the extra hypothesis "and `M_n` embeds into `R^omega`
for every `n`" (or LP instead of LLP); Dogon's paraphrase drops it.  It is
harmless for Definition 1.5, which quantifies over `phi_n : Gamma -> U(d_n)`
with `M_n = M_(d_n)`, but any consumer applying this node to
non-matricial targets must restore it.  The sketch's "diagonal argument
over an exhaustion" is better replaced by working in the sequential
quotient `prod M_(d_n) / {(x_n) : lim_n || x_n ||_2 = 0}` directly, since
an asymptotic homomorphism already defines a homomorphism there.
