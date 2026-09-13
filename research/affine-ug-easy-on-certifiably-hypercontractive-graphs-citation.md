---
rg: 2
id: affine-ug-easy-on-certifiably-hypercontractive-graphs-citation
kind: route
title: Import Theorem 1.1, Corollaries 1.3--1.4 and Theorem 1.5 of Bafna--Barak--Kothari--Schramm--Steurer (arXiv:2006.09969)
target: affine-ug-easy-on-certifiably-hypercontractive-graphs
requires: []
---

Literature import, credited in full.

Mitali Bafna, Boaz Barak, Pravesh K. Kothari, Tselil Schramm, David Steurer,
*Playing Unique Games on Certified Small-Set Expanders*, arXiv:2006.09969v3
(26 June 2021); STOC 2021.

Verified from the arXiv PDF, pages 2--4, on 2026-09-12:

* The definitions of `V_lambda(G)`, `(lambda, C)` hypercontractive, and
  `(lambda, C, D)`-certifiably hypercontractive (page 2--3, Definition 4.1
  referenced).
* **Theorem 1.1** (Unique games on certifiable small-set expanders), as quoted
  in the claim: value `1 - eps` with `eps <= lambda^2/100` gives value at least
  `eps lambda^4/(64 C)`. The algorithm rounds the degree-`D'` SoS relaxation,
  where `D'` depends on `C, eps, lambda, D`.
* **Corollary 1.3** (noisy hypercube): "For every 0.001 > eps > 0 and
  1/4 > alpha > 0 there is a polynomial time algorithm A and a constant
  tau = tau(alpha, eps) > 0, such that if I is an affine unique games instance
  over the alpha-noisy hypercube with val(I) >= 1 - eps then A(I) outputs an
  assignment to I with value at least tau." The page also gives
  `tau = poly(eps) exp(-c sqrt(eps)/alpha)`.
* **Corollary 1.4** (noisy short code graph) and **Theorem 1.5** (Johnson
  graph), stated analogously.
* Page 4 notes that it is not known whether constant-degree SoS solves unique
  games on the standard Boolean cube.
