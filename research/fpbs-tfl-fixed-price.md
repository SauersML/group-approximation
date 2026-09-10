---
rg: 2
id: fpbs-tfl-fixed-price
kind: claim
title: Every infinite selected relator family has fixed price one
root: true
---

**Statement.** For i>=1 put r_i = product_{j=1..13} a b^(100i+j), of length 1300i+104, and for an
infinite J subset of the positive integers put G_J = <a,b | r_i=1, i in J>. Theorem A of the
torsion-free note: every G_J is torsion-free, contains <a^2,b^2> isomorphic to F_2, and has fixed
price one. Quantitatively, for every essentially free p.m.p. action alpha of G_J, every k distinct
indices in J and every eta>0 there is a measurable U with

    {T_b on X, T_a restricted to U} generating, and
    mu(U) <= I_k + eta,  I_k = integral_0^1 (1-t^12)^k dt = product_{j=1..k} 12j/(12j+1) <= k^(-1/12).

Since I_k tends to zero, every free action has cost exactly one. The J range gives continuum many
marked groups and continuum many isomorphism types, all infinitely presented. Torsion is not used:
this is the first construction in the archive whose detours come from relator tails rather than from
finite-order elements.

**Proof location.** `research/artifacts/fpbs/torsionfree-local.md`, Sections 1 and 4; response 46.

**Imported inputs.** Gaboriau, *What is... cost?*, arXiv:1011.2294v1 (cost definitions, infinite-class
lower bound one). Sapir, arXiv:1012.1325v4, Theorem 3.7 (classical Greendlinger lemma). Gruber-Sisto,
arXiv:1408.4488v3, Section 1.1, Lemmas 2.15 and 2.17, Theorem 1.3. Choi-Seo, arXiv:2508.08932v2, for
the separate percolation corollary only. All four identifiers resolve with matching titles and authors.

**Finite-replay evidence.** `research/artifacts/fpbs/torsionfree-local-checks.json` via
`scripts/replay_torsionfree_local.py`: status PASS, 68,833 assertions including 26,843 deletion
labelings for the connectivity of simultaneous priority deletion, plus the exact continuous-priority
integral and the Riemann error bound. The checks file states that it covers finite models only.

**Evidence level.** Written deduction with named published inputs and a passing finite replay of its
combinatorial core. Not refereed, not formally verified. The infinite steps the replay does not reach
are the measurable selection in an arbitrary free action and the cost infimum limit. This claim is the
archive's strongest positive fixed-price result, and `torsionfree-local-audit.json` records that it
assumes none of the earlier broad bounded-exponent or two-generator theorems.

Status records a written deduction or explicitly imported theorem, not independent validation.
