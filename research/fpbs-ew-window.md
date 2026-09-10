---
rg: 2
id: fpbs-ew-window
kind: claim
title: "All constructed standard Cayley graphs have infinitely many infinite clusters for 7/20<=p<=37/100"
root: true
---

**Statement.** Let J be any set of positive integers, for i in J choose a prime p_i>=13, put
Gamma = <a,b | (a b^i)^(p_i)=1, i in J> and let G = Cay(Gamma, {a,a^(-1),b,b^(-1)}), which is simple
and four-regular. The main theorem of the explicit-window note: for every p in [7/20, 37/100] the
graph G has infinitely many infinite clusters almost surely, theta(p) > 1/20, and for every k>=300 the
origin and the simple random walk at time k lie in different infinite clusters with probability
greater than 1/800. The thresholds are bounded explicitly:

    p_c(G) <= alpha_6, the positive root of p+2p^2+4p^3+8p^4+16p^5+32p^6 = 1,
    p_u(G) >= (sqrt(29)-sqrt(5))/(6 sqrt(2)).

The decimals 0.345997... and 0.371124... are evaluations; the polynomial and the radical are the
mathematical content. The claim is class-specific and generating-set-specific.

**Proof location.** `research/artifacts/fpbs/explicit-percolation-window.md`, Sections 5 and 6, on the
algebra of Section 2 and the branching and spectral estimates of Sections 3 and 4; response 42. This
route deliberately avoids Choi-Seo, Gruber-Sisto, acylindrical hyperbolicity and the cost-one property
of the same groups, so it is logically independent of `fpbs-sc-percolation-family`.

**Imported inputs.** Only the classical linear Greendlinger-Dehn criterion for C'(1/6), cited to
Lyndon-Schupp Chapter V Theorem 4.4 and presented diagrammatically in Sapir, arXiv:1012.1325v4,
Definition 3.6 and Theorem 3.7, together with elementary Galton-Watson, Bernoulli ergodicity, finite
energy and Harris positive association. The note states that previous broad cost claims are not
premises.

**Finite-replay evidence.** `research/artifacts/fpbs/explicit-window-checks.json` via
`scripts/replay_explicit_window.py`: status PASS, 150,032 exact arithmetic assertions, including
26,240 square-subgroup words, 26,240 cross-subgroup words, 90,480 cyclic free-product words, the
offspring generating function, the rational endpoints 7/20 and 37/100, and the critical root bracket.
Two families are seeded samples rather than exhaustive: 5,000 linear junction pairs and 1,981 cactus
boundaries, seed 20260909.

**Evidence level.** Written deduction from one classical import, with the largest exact finite replay
in the archive. Not refereed, not formally verified. It is a numerically explicit Benjamini-Schramm
statement for one presentation and one generating set, not a universal proof.

Status records a written deduction or imported result, not external or formal mathematical verification.
