---
rg: 2
id: fpbs-critical-l2-iff-volume-tail-and-spectral-spreading
kind: claim
title: Critical l2 boundedness is equivalent to a mean-field critical volume tail plus vanishing normalized spectral radius of the subcritical two-point operator
distinct_from:
  fpbs-critical-l2-equivalent-to-dyadic-projection-estimate: that shows Q2, Q3 and critical l2 are each the same statement graph by graph; this splits critical l2 into two conditions of different nature, a critical volume exponent and a subcritical normalized spectral condition, and shows the second is exactly where nonamenability enters.
  fpbs-acylindrically-hyperbolic-critical-l2-gap: that proves the gap for one class from the Choi-Seo susceptibility and spreading estimates; this is a class-free equivalence, and it replaces the susceptibility input by the critical volume tail through gamma <= delta-1.
  fpbs-nonamenability-bounds-critical-connectivity-operator: that is the universal l2 conjecture; this proves nothing universal, it reduces the conjecture to two separately checkable universal statements.
  fpbs-critical-dyadic-projection-estimate: that is the universal OPEN hole Q2; this gives an equivalent graph-by-graph reformulation of it.
  fpbs-hutchcroft-l2-gap-criterion: that imports Hutchcroft's criterion with susceptibility and iota coupled in one liminf; this decouples them, removes the liminf in favour of a limit, and adds the amenable and relative-susceptibility obstructions.
---

Let `G=(V,E)` be an infinite, connected, locally finite, transitive graph of
degree `d`, with adjacency operator `A`. For `0<=p<p_c` let
`tau_p(u,v)=P_p(u<->v)`, `T_p` the operator with kernel `tau_p`,
`chi_p=E_p|K_o|=||T_p||_(1->1)`, `||.||=||.||_(2->2)`, and

    s(p) = 1 - iota(T_p) = sup_{K finite} sum_{u,v in K} tau_p(u,v) / (chi_p |K|)  in (0,1].

Consider the two conditions

* **(V)** there is `C<infinity` with `P_{p_c}(|K_o|>=n) <= C n^(-1/2)` for all `n>=1`;
* **(S)** `s(p) -> 0` as `p ↑ p_c`.

**Theorem.**

1. `||T_{p_c}|| < infinity` iff `p_c < p_(2->2)`.
2. `||T_{p_c}|| < infinity` iff (V) and (S) both hold.
3. For `0<p<p_c`, `s(p) <= ||T_p||/chi_p <= sqrt(2 s(p))`. So (S) is
   equivalent to `||T_p||_(2->2) = o(||T_p||_(1->1))` as `p ↑ p_c`.
4. *(Threshold.)* Assume (V), and let `C''` be the constant of
   `fpbs-critical-volume-tail-gives-mean-field-susceptibility`. Put
   `eps_0 = (1-p_c)^2 / (2 C''^2 ||A||^2) > 0`. Then either `s(p) -> 0` and
   `||T_{p_c}||<infinity`, or `liminf_{p↑p_c} s(p) >= eps_0` and
   `||T_{p_c}||=infinity`. Under (V), a single sequence `p_n ↑ p_c` with
   `s(p_n) < eps_0` therefore forces (S) and critical l2.
5. *(Amenable obstruction.)* If `G` is amenable, then `s(p)=1` for every
   `0<=p<p_c`. So (S) fails on every amenable transitive graph, while (V)
   uses no amenability hypothesis.
6. *(Relative susceptibility.)* Let `G` be a Cayley graph of a group `Gamma`,
   let `H<=Gamma` be an amenable subgroup and put
   `chi^H_p = sum_{h in H} tau_p(e,h)`. Then `chi^H_p <= ||T_p||` and
   `s(p) >= chi^H_p/chi_p` for `0<=p<p_c`. So (S), and hence critical l2,
   forces `chi^H_p = o(chi_p)` as `p ↑ p_c` for every amenable subgroup `H`.
   For example, on `F_2 x Z` the susceptibility along the central `Z` must
   be `o(chi_p)`.
7. *(Dyadic form.)* If moreover the critical clusters are a.s. finite, which
   holds on every nonamenable Cayley graph, then the dyadic projection
   estimates Q2 and Q3 of `fpbs-critical-dyadic-projection-estimate` are each
   equivalent to (V) and (S) together.

**Reading.** Critical l2 splits into a critical exponent statement (V), which
is a mean-field volume exponent and needs no nonamenability, and a subcritical
spectral statement (S), which fails on every amenable graph. All the
nonamenability in the l2 conjecture sits in (S). Under (V), (S) needs only one
sequence below an explicit threshold.
