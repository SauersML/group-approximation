---
rg: 2
id: zero-row-controlled-inputs-are-outnumbered
kind: claim
title: Inputs of a torus map that are controlled by at most K null-homotopic outputs number at most c_K < 1 times those outputs, with c_3 = 8/9, and so null-homotopic small-fibre maps satisfy the linear form of LRSF without locality
distinct_from:
  local-rectangular-small-fibre-maps-lose-proportional-rank: that is the rank bound for every locally controlled map; this is the sector where all control rows vanish in H^1, where it proves the linear form for every K and d with no locality hypothesis.
  sofic-torus-c2-reduces-to-rectangular-small-fibres: that reduces sofic C2 to LRSF; this proves the null-homotopic sector of LRSF, and does not by itself give C2.
artifacts:
  - research/artifacts/zero-row-slice-count-2026-09-20.md
---

**Statement.** Let `g: T^n -> T^N` be continuous. Call output `j` a *zero row* if `g_j` is null-homotopic.
Suppose every input `i` in a set `B_0` has a control set `C_i` of at most `K >= 2` zero rows. Control means
that `eta`-closeness of the outputs on `C_i` forces `||u_i - u'_i|| < 1/16`. Put `P_0 = ∪_(i in B_0) C_i`. Then

    |B_0| <= c_K |P_0|,   1/c_K = max_(0<p<1) (1-p)^(K-2) (1 + (K-1)p),

attained at `p = 1/(K-1)^2`. So `c_2 = 1/2`, `c_3 = 8/9`, `c_4 = 243/256`, and `c_K = 1 - 1/(2(K-1)^2) + O(K^-3)`.

**Corollary.** Let `g: (T^d)^I -> (T^d)^J` satisfy (C) of LRSF with `|C_i| <= K`, and suppose `g^* = 0` on
`H^1`. Then `|J| - |I| >= (1/c_(dK) - 1)|I|`. No locality is assumed.

**Place in the graph.**
- It proves the null-homotopic case of `local-rectangular-small-fibre-maps-lose-proportional-rank`.
- It proves the zero-row sector of w19's reduction target (E_K), for every `K`.
- What is left of (E_K) is the sector of inputs whose control rows are nonzero but dependent. For `K = 3`
  these are the proportional rows `(v, av, bv)`.

**ESTABLISHED 2026-09-20** by [[zero-row-controlled-inputs-are-outnumbered-proof]].
