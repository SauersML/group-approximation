---
rg: 2
id: simple-group-psl-width-is-finite-field-linear-soficity
kind: claim
title: A finitely presented simple group has bounded relator width over all special linear groups iff it is not linear sofic over finite fields
distinct_from:
  simple-group-relator-width-in-finite-simple-targets: that bounds relator width over symmetric, alternating, sporadic and bounded-rank Lie type groups under nonsoficity; this treats special and projective special linear groups of unbounded rank, where the exact hypothesis is non-linear-soficity over finite fields.
  non-linear-sofic-simple-groups-bounded-width-in-classical-groups: that is the open statement for all four classical families under a fixed-field hypothesis; this proves the special linear family with constants uniform in the field, and shows the hypothesis cannot be weakened.
  simple-group-support-and-semisimple-rank-models-collapse: that proves the rank collapse inequalities with a constant for one fixed field; this makes the constant uniform over finite fields and turns the collapse into bounded conjugacy width.
  linear-sofic-implies-weakly-sofic-over-every-field: that is the inclusion of linear sofic groups in weakly sofic groups; this shows that for finitely presented simple groups the special linear targets contribute exactly linear soficity over finite fields and nothing more.
---

**ESTABLISHED (unreviewed).** Let `G = <X | R>` be an infinite finitely presented simple group.
For a finite group `Q` and `a in Q^X`, `w_Q(a)` is the least `K` such that every `a_x` is a
product of at most `K` `Q`-conjugates of relator values `r(a)^(+-1)`, as in
`simple-group-relator-width-in-finite-simple-targets`. Put `rho(g) = min_(lambda in F) rk(g - lambda)`
for `g in GL_n(F)`, the rank distance to the scalars.

**Definition.** `G` is *linear sofic over finite fields* if `G` embeds in a metric ultraproduct
`prod_omega GL_(n_i)(F_(q_i)) / N_omega` with the normalized rank length `rk(g - 1)/n_i`, for some
sequence of finite fields `F_(q_i)`.
- `F_q`-linear sofic implies linear sofic over finite fields, which implies weakly sofic
  (`GL_n(F_q)` is finite and the normalized rank length is bi-invariant).
- The embedding can be taken with every `q_i` a power of one prime `p` iff `G` is `F_p`-linear
  sofic. Field extension does not change rank, and restriction of scalars
  `GL_n(F_(p^e)) <= GL_(ne)(F_p)` multiplies rank and dimension by `e`.

**Theorem.**
0. **Uniform collapse.** If `G` is not linear sofic over finite fields, there is `delta_0 > 0` such
   that every finite field `F`, every `n` and every `a in GL_n(F)^X` satisfy
   ```text
   max_r rk(r(a) - 1) >= delta_0 max_x rk(a_x - 1),
   max_r rho(r(a))    >= (delta_0/2) min(max_x rho(a_x), n/2).
   ```
   If `G` is not `F_p`-linear sofic, the same holds with `delta_0` uniform over all `F = F_(p^e)`.
1. **Dichotomy.** The following are equivalent:
   - (i) `G` is not linear sofic over finite fields;
   - (ii) there is `K = K(G)` with `w_Q(a) <= K` for every `Q = SL_n(q)/Z_0`, with `n >= 2`, `q`
     any prime power and `Z_0` any central subgroup, and every `a in Q^X`;
   - (iii) `G` has no sequence of weak models in the groups `PSL_n(q)` with bi-invariant lengths.
2. **Fixed characteristic.** The same equivalence holds with (i) replaced by "`G` is not
   `F_p`-linear sofic" and `Q` restricted to `SL_n(p^e)/Z_0`.

**What it settles.**
- Of the three missing pieces listed on `non-linear-sofic-simple-groups-bounded-width-in-classical-groups`,
  two are resolved for the linear family:
  - the commutator choice `rk([B, h]) >= c rk B`: a displacement `y` of the moved subspace gives rank
    exactly `2 rk B`;
  - the determinant bookkeeping in `PSL_n`: a fixed commutator template for the generators makes
    every scalar cancel, so no scalar matching is needed.
- Class-size bounds for `Sp`, `SU` and `Omega` remain open on that node.
- **The hypothesis is sharp.** A group linear sofic over finite fields has unbounded width over
  `PSL_n(q)` and has weak models there. So a counterexample to `fg-simple-weakly-sofic-groups-are-sofic`
  can get no room from special linear targets unless it is itself linear sofic over finite fields.
- **Restricted rigidity is a linear-sofic question.** For finitely presented simple groups, the rigidity
  claim restricted to special linear targets says: every such group that is linear sofic over finite
  fields is sofic. This is a finite-field analogue of Arzhantseva--Paunescu Question 8.5 ("Are all
  linear sofic groups indeed sofic?", recorded on `linear-sofic-nonsofic-group`), restricted to finitely
  presented simple groups.
- **Binary Leavitt unit group.** `R^x` has weak models in special linear groups over `F_(2^e)` iff it
  is `F_2`-linear sofic (`binary-leavitt-unit-group-is-f2-linear-sofic`).

**Mechanism.**
- **Template.** `G` is perfect, so in `F(X)` every generator is a product of `J` commutators of words
  times `J'` conjugates of relators, with `J`, `J'` and word lengths fixed. It suffices to cover each
  commutator `[u(a), v(a)]`.
- **Scalars cancel.** A commutator ignores central factors. If `u(a) in S^k Z`, then
  `[u(a), v(a)] = [s, v(a)]` with `s in S^k`, a product of `2k` conjugates.
- **Proportional case.** If some generator has `rho >= n/(8|X|)`, the projective collapse gives a
  relator value with `rho >= c n`. Its class is `q^(Omega(n^2))`, so Liebeck--Shalev covers
  `PSL_n(q)` in boundedly many steps.
- **Near-scalar case.**
  - Divide each generator by a nearest scalar. The resulting tuple `b` lives in `GL(W) x 1` with
    `dim W <= 2|X| P`, where `P = max_x rho(a_x)`.
  - The linear collapse gives a relator with `t = rk(r(b) - 1) >= delta_0 P`.
  - A displacement `y` carrying `W` off itself makes `h = [r(a), y]` equal `r(b)|_W (+) (copy of r(b)^-1) (+) 1`,
    of rank `2t`.
  - `h` sits in `SL(W''')` with `dim W''' = O(P)` and fixed space at least half. Cover there.

Derivation: `simple-group-psl-width-is-finite-field-linear-soficity-proof`.
