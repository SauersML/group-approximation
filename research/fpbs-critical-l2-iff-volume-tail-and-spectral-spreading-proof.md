---
rg: 2
id: fpbs-critical-l2-iff-volume-tail-and-spectral-spreading-proof
kind: route
title: Hutchcroft's criterion with gamma at most delta minus one substituted for the susceptibility estimate
target: fpbs-critical-l2-iff-volume-tail-and-spectral-spreading
requires:
  - fpbs-hutchcroft-l2-gap-criterion
  - fpbs-critical-volume-tail-gives-mean-field-susceptibility
  - fpbs-triangle-condition-gives-mean-field-magnetization
  - fpbs-critical-l2-equivalent-to-dyadic-projection-estimate
---

Complete written proof. No computation is used. Notation is as in the claim.
Cite the imported items as

* [B1]-[B4]: items 1-4 of `fpbs-hutchcroft-l2-gap-criterion` (sharpness
  `p_c=p_(1->1)<=p_(2->2)`; l2 Aizenman-Barsky; two-sided Cheeger; criterion);
* [A]: `fpbs-critical-volume-tail-gives-mean-field-susceptibility`, (V) gives
  `chi_p <= C''/(p_c-p)` for `0<=p<p_c`;
* [Tri]: `fpbs-triangle-condition-gives-mean-field-magnetization`,
  `nabla_{p_c}<infinity` gives (V);
* [Dy]: item 3 of `fpbs-critical-l2-equivalent-to-dyadic-projection-estimate`.

**Preliminaries.**

* (P1) `1/d <= p_c`. The number of self-avoiding paths of length `n` from `o`
  is at most `d^n`. So `P_p(|K_o|=infinity) <= (dp)^n -> 0` for `p<1/d`.
* (P2) Monotonicity. For `p<=p'`, the standard monotone coupling gives
  `0 <= tau_p <= tau_(p')` entrywise. For nonnegative kernels
  `|<f,T_p g>| <= <|f|,T_(p')|g|>`, so `||T_p|| <= ||T_(p')||`. Hence
  `p -> ||T_p||` is nondecreasing and `||T_p||<infinity` for every `p<p_(2->2)`.
* (P3) Range of `s`. Taking `K={o}` gives `s(p) >= tau_p(o,o)/chi_p = 1/chi_p > 0`.
  For every finite `K`, `sum_{u,v in K} tau_p(u,v) <= |K| chi_p` by
  transitivity, so `s(p) <= 1`.
* (P4) `0 < ||A|| <= d`, since `A` is a nonzero nonnegative matrix with row
  sums `d`.
* (P5) `chi_p -> infinity` as `p ↑ p_c`. [B2] with `q=1`, `p_(1->1)=p_c` by
  [B1], and `||A||_(1->1)=d` give `chi_p >= (1-p)/(d(p_c-p))` for `0<=p<p_c`.
  Since `p_c <= 1`, `(1-p)/(p_c-p) >= 1` and the bound tends to infinity unless
  `p_c=1`. If `p_c=1`, fix `v` and a path of length `r` from `o` to `v`. Then
  `tau_p(o,v) >= p^r -> 1` as `p ↑ 1`, so by Fatou
  `liminf chi_p >= sum_v 1 = infinity`, because `G` is infinite. So
  `chi_p -> infinity` in all cases. (Only the case `p_c<1` is used below.)

**Item 1.** Suppose `p_c < p_(2->2)`. Pick `p'` in `(p_c, p_(2->2))`. By (P2),
`||T_{p_c}|| <= ||T_(p')|| < infinity`. Conversely, suppose
`||T_{p_c}||<infinity`. Then `p_c <= p_(2->2)` by definition of `p_(2->2)`. If
`p_c = p_(2->2)`, then [B2] with `q=2` gives `||T_(p_(2->2))|| = infinity`,
which is a contradiction. So `p_c < p_(2->2)`.

**Item 3.** Let `0<p<p_c=p_(1->1)` ([B1]). The lower half of [B3] is
`chi_p s(p) <= ||T_p||`. The upper half is
`||T_p|| <= chi_p sqrt(1-(1-s)^2) = chi_p sqrt(s(2-s)) <= chi_p sqrt(2s)`.
Divide by `chi_p`. In particular `s(p)->0` iff `||T_p||/chi_p -> 0`, and
`chi_p = ||T_p||_(1->1)` by [B1].

**Item 2, forward.** Assume `||T_{p_c}||<infinity`. By item 1,
`p_c < p_(2->2) <= 1`. Fix `p'` in `(p_c, p_(2->2))`.

* (V): [B4] (its "in particular" clause) gives `nabla_{p_c} < infinity`, and
  [Tri] gives (V).
* (S): for `max(0,p_c/2) < p < p_c`, item 3 and (P2) give
  `s(p) <= ||T_p||/chi_p <= ||T_(p')||/chi_p`. The numerator is a fixed finite
  number, and `chi_p -> infinity` by (P5). So `s(p) -> 0`.

**Item 2, backward.** Assume (V) and (S).

* `p_c < 1`. At `p=1` every edge is open, and `G` is infinite and connected,
  so `P_1(|K_o| >= n) = 1` for all `n`. This contradicts (V) for `n > C^2`.
* `p_c > 0` by (P1), so `p ↑ p_c` makes sense, and [A] applies.
* For `0<p<p_c`, [A] gives `(p_c-p) chi_p <= C''`, and `1-p >= 1-p_c > 0`.
  With `1-iota(T_p)^2 = s(2-s) <= 2s`,

      ((p_c-p)/(1-p)) chi_p sqrt(1-iota(T_p)^2) <= C'' sqrt(2 s(p)) / (1-p_c).

  By (S), the right side tends to `0`, so the liminf on the left is
  `0 < 1/||A||` by (P4). [B4] gives `p_c < p_(2->2)`, and item 1 gives
  `||T_{p_c}|| < infinity`.

**Item 4.** Assume (V). As in the backward half of item 2, `0<p_c<1`, and for
`0<p<p_c` the criterion quantity `Q(p)` on the left of the display there
satisfies `Q(p) <= C'' sqrt(2 s(p))/(1-p_c)`.

* If `||T_{p_c}||<infinity`, then `s(p)->0` by item 2.
* If `||T_{p_c}||=infinity`, then `p_c=p_(2->2)` by item 1, so [B4] gives
  `liminf Q(p) >= 1/||A||`. Hence
  `liminf sqrt(2s(p)) >= (1-p_c)/(C''||A||)`, that is,
  `liminf s(p) >= eps_0`.

The alternatives exclude each other because `eps_0>0`. If
`liminf s(p) < eps_0`, the second alternative is excluded, so the first holds.

**Item 5.** Let `G` be amenable, so there are finite `K_j` with
`|dK_j|/|K_j| -> 0`, where `dK` is the set of vertices of `K` with a neighbour
outside `K`. Fix `0<=p<p_c` and `R>=1`, and put `I = {u in K : B(u,R) ⊆ K}`.
Every `u` in `K \ I` lies within distance `R` of a vertex of `dK`, so
`|K \ I| <= |B(o,R)| |dK|`. All terms of `tau_p` are nonnegative, so by
transitivity

    sum_{u,v in K} tau_p(u,v) >= sum_{u in I} sum_{v in B(u,R)} tau_p(u,v) = |I| chi_p^(R),

where `chi_p^(R) = sum_{v in B(o,R)} tau_p(o,v)`. Along `K_j`,
`|I|/|K_j| -> 1`, so `s(p) >= chi_p^(R)/chi_p`. Let `R -> infinity`. Since
`chi_p<infinity` for `p<p_c` by [B1], `chi_p^(R) ↑ chi_p`, so `s(p) >= 1`.
With (P3), `s(p)=1`, and (S) fails. Item 2 then gives `||T_{p_c}||=infinity`,
a known consequence of amenability that is recovered here. The definition of
(V) involves no isoperimetry.

**Item 6.** Let `G` be the Cayley graph of `Gamma` for a finite symmetric
generating set `S`, with edges `g ~ gs`. Left multiplication is a graph
automorphism, so `tau_p(g,gh) = tau_p(e,h)`. Let `H<=Gamma` be amenable, fix
`0<=p<p_c`, a finite `L ⊆ H` and `eps>0`.

* Since `H` is amenable, it has finite sets `F ⊆ H` with
  `|Fl \ F| <= eps|F|/|L|` for all `l in L`. (Take a left Følner set for `L^(-1)`
  and invert it.)
* The set of `g in F` with `gl` outside `F` for some `l in L` has size at most
  `sum_l |Fl \ F| <= eps|F|`, since `g -> gl` is injective. So at least
  `(1-eps)|F|` points `g in F` satisfy `gL ⊆ F`.
* For such `g`, `sum_{v in F} tau_p(g,v) >= sum_{l in L} tau_p(g,gl) = sum_{l in L} tau_p(e,l)`.
  Hence

      sum_{u,v in F} tau_p(u,v) >= (1-eps) |F| sum_{l in L} tau_p(e,l).

Dividing by `chi_p|F|` gives `s(p) >= (1-eps) sum_{l in L} tau_p(e,l)/chi_p`.
Dividing by `|F| = ||1_F||^2` and using `<f,T_p f> <= ||T_p|| ||f||^2` gives
`||T_p|| >= (1-eps) sum_{l in L} tau_p(e,l)`. Let `eps -> 0` and `L ↑ H`.
This gives `s(p) >= chi^H_p/chi_p` and `chi^H_p <= ||T_p||`. So (S) forces
`chi^H_p/chi_p -> 0`, and item 2 shows critical l2 forces it too. For
`F_2 x Z` with its standard generators, take `H = {e} x Z`.

**Item 7.** By [Dy], on transitive graphs with a.s. finite critical clusters,
Q2, Q3 and `||T_{p_c}||<infinity` are equivalent. [Dy] also states that every
nonamenable Cayley graph is such a graph. Combine this with item 2.
