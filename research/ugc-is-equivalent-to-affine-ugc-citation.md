---
rg: 2
id: ugc-is-equivalent-to-affine-ugc-citation
kind: route
title: Import KKMO Theorem 12, Corollaries 13 and 15 and the abelian-group remark, remove loops with fresh variables, and pass to bipartite shift games by the double cover at a factor-8 soundness cost
target: ugc-is-equivalent-to-affine-ugc
requires: []
---

Literature import, credited in full.

Subhash Khot, Guy Kindler, Elchanan Mossel, Ryan O'Donnell, *Optimal
Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?*, SIAM J.
Comput. 37(1):319--357 (2007). Verified on 2026-09-18 against the
author-hosted PDF `https://www.cs.cmu.edu/~odonnell/papers/maxcut.pdf`
(38 pages). Quotes are copied from a machine text extraction, so symbols are
normalized (`rho`, `eps`, `Lambda`).

* **Abstract (p. 1).** "For MAX-2LIN(q) we show hardness of distinguishing
  between instances which are (1-eps)-satisfiable and those which are not even,
  roughly, (q^(-eps/2))-satisfiable ... The hardness result holds even for
  instances in which all equations are of the form x_i - x_j = c. At a more
  qualitative level, this result also implies that 1-eps vs. eps hardness for
  MAX-2LIN(q) is equivalent to the Unique Games Conjecture."
* **Theorem 12 (p. 15).** "Assume the Unique Games Conjecture. Then for every
  q >= 2, rho in [0,1] and eps > 0, given an instance of MAX-2LIN(q), it is
  NP-hard to distinguish between the case where it is at least
  (rho + (1/q)(1-rho) - eps)-satisfiable and the case where it is at most
  (q Lambda_rho(1/q) + eps)-satisfiable. Furthermore, this holds even for
  instances in which all equations are of the form x_i - x_j = c."
* **Corollary 13 (p. 15).** "Assume the Unique Games Conjecture. Then for every
  fixed eps > 0 there exists q0 = q0(eps) such that for every fixed q > q0 the
  following holds. Given an instance of MAX-2LIN(q), it is NP-hard to
  distinguish between the case where the instance is at least
  (1 - eps)-satisfiable and the case where it is at most
  (1/q)^(eps/(2-eps))-satisfiable."
* **Corollary 15 (p. 15).** "The Unique Games Conjecture holds if and only if
  it holds as follows: For every eps > 0 and label set size q (sufficiently
  large as a function of eps), it is NP-hard to distinguish whether the Unique
  Label Cover problem with label set size q has optimum at least 1 - eps or at
  most (1/q)^(eps/(2-eps)). (The factor of 2 lost in soundness from passing to
  a bipartite version can be absorbed since the soundness obtained in the proof
  of Corollary 13 is actually stronger by a factor of (log q)^Omega(1).)"
* **Abelian groups (p. 27, Section 11.1).** After defining Gamma-MAX-2LIN(q),
  equations x_i - x_j = c_ij: "Our hardness results will hold even for
  Gamma-MAX-2LIN(q). The Gamma notation is essentially from Hastad [31]; we use
  it because our results actually hold equally well for the problem of
  satisfying equations of the form x_i x_j^(-1) = c_ij over any fixed abelian
  group Gamma of order q, not just Z_q."
* **Restatement by Bafna--Minzer** (arXiv:2304.07284v1, p. 3--4): "it is known
  [KKMO07] that the UGC is true if and only if it holds for the class of Affine
  UG", and footnote 2 (p. 4): "the reduction of [KKMO07] does not preserve the
  topology of the graph."

**Loop removal and bipartite double cover (new).** Let `I` be a weighted
system of equations `x_i - x_j = c` over an abelian group `A` of order `q`.
KKMO Definition 14 allows equations with "at most 2 variables", so loops
`x_i - x_i = c` must be handled first.

* *Loop removal.* Replace a loop with `c = 0` (always true) by `x_i - y = 0`
  with a fresh variable `y`, of the same weight. Replace a loop with `c != 0`
  (always false) of weight `w` by the `q` equations `x_i - y = d`, `d in A`,
  each of weight `w/q`, with a fresh `y`. Exactly one of these `q` holds for
  every value of `y`. The fresh variables are free, so the new loop-free system
  `I'` has `val(I') = val(I) + mu/q`, where `mu <= 1` is the weight of the false
  loops. So completeness does not drop and soundness rises by at most `1/q`.
* *Double cover.* `D(I')` has left vertices `i_L`, right vertices `j_R`, and
  for each equation the constraint `x_(j_R) = x_(i_L) - c`, with the same
  weight. This is a bipartite shift game over `A`. Copying an assignment of
  `I'` to both sides gives `val(D(I')) >= val(I')`. Conversely, from an
  assignment `(a^L, a^R)` of `D(I')`, set each `a_i` to `a^L_i` or `a^R_i`
  independently and uniformly. An equation `x_i - x_j = c` with `i != j` that
  is satisfied in `D(I')` is satisfied by `a` whenever `i` chose L and `j` chose
  R, which has probability `1/4`. So `val(I') >= val(D(I'))/4`.

Hence the UGC-conditional hardness of Corollary 13, over `Z_q` or over any fixed
abelian `Gamma` of order `q` by the page-27 remark, gives NP-hardness of
Gap-UG[`1 - eps`, `4 (s + 1/q)`] with `s = (1/q)^(eps/(2-eps)) >= 1/q`, so of
Gap-UG[`1 - eps`, `8 (1/q)^(eps/(2-eps))`], on bipartite shift games over that
group. The right-hand side tends to `0` as `q -> infinity` for fixed `eps`.
That is items (2) and (3) of the claim. The converse directions are
inclusions of subclasses.

*Reading of the page-27 remark.* The remark covers "our hardness results", and
Theorem 12's soundness `q Lambda_rho(1/q) + eps` depends on `Gamma` only
through `q`. Corollary 13 is derived from Theorem 12 by the asymptotics of
`Lambda_rho` alone. So Corollary 13 transfers verbatim to every abelian
`Gamma` of order `q`. This is the only interpretive step, and it is the
authors' own statement.
