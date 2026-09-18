---
rg: 2
id: rips-segev-port-data-cannot-exclude-balanced-divisors-proof
kind: route
title: Read the sources and targets of the b-edges of Gamma on each a-coset; line endpoints are both, so top and bottom ports coincide
target: rips-segev-port-data-cannot-exclude-balanced-divisors
requires: [rips-segev-core-large-gap-two-layer-elements-are-regular]
---

**Conventions.**  As in `rips-segev-core-large-gap-two-layer-elements-are-regular-proof`.
- The lines of `Gamma` have vertices `v_{il}`, `0 <= l <= C_i`.  Every `b`-edge runs from a source position
  `q in S_i` to a target position `p in T_j`.
- `g : V(Gamma) -> K` sends a vertex to the image of the label of a path from a fixed base vertex.  It is well
  defined because cycle labels are relators.
- `g(v_{il}) = c_i a^l` with `c_i = g(v_{i0})`.  If `e` is a `b`-edge from `v` to `v'`, then `g(v') = g(v) b`.
- `a` has infinite order in `K` (Step 0 of `rips-segev-groups-embed-every-torsion-free-group-proof`), so each
  coset `x<a>` is ordered as a copy of `Z`.

## Part 1 (balanced realization)

Let `Src = {g(v) : v has an outgoing b-edge}` and `Tgt = {g(v) : v has an incoming b-edge}`.  Let `𝒞` be the set
of cosets `c_i <a>`.  For `T in 𝒞` put `Out_T = Src ∩ T` and `In_T = Tgt ∩ T`.

*Supports.*
- A vertex `v_{jl}` has `g(v_{jl}) in T` iff `c_j <a> = T`.  So `Src = ⊔_T Out_T` and `Tgt = ⊔_T In_T`.
- `Out_T` and `In_T` are nonempty: `T = c_i<a>` for some line `i`, and `g(v_{i0})` lies in both.

*(P1).*  `Src · b ⊆ Tgt`: if `v` has an outgoing `b`-edge to `v'`, then `g(v) b = g(v') in Tgt`.  Conversely every
`g(v') in Tgt` equals `g(v) b` for the source `v` of the incoming `b`-edge.  So `Src · b = Tgt`, which is (P1).

*(P2).*  Fix `T` and write `T = x<a>`.  Let `I(T)` be the set of lines `i` with `c_i<a> = T`, and write
`c_i = x a^{m_i}`.  Then

    Out_T = { x a^{m_i + q} : i in I(T), q in S_i },    In_T = { x a^{m_i + p} : i in I(T), p in T_i }.

By hypothesis `max S_i = max T_i = C_i` and `min S_i = min T_i = 0`.  So

    max Out_T = x a^{max_i (m_i + C_i)} = max In_T,      min Out_T = x a^{min_i m_i} = min In_T.

The offsets are `(0, 0)`. ∎

*Steenbock's explicit graphs satisfy the hypothesis.*  The labels are:
- `x_{i1} = b a^{-I_i1}`: source position `0`, target `I_i1`;
- `x_{i2} = a^{C_l} b a^{-I_i2}`: source `C_l`, target `I_i2`;
- `y_{i3} = a^{O_i1} b a^{-C_k}`: source `O_i1`, target `C_k`;
- `y_{i4} = a^{O_i2} b`: source `O_i2`, target `0`.

Each vertex of `Phi` carries one edge of each type in and one out, because `Phi` covers a bouquet of four circles.
So `S_i = {0, O_i1, O_i2, C_i}` and `T_i = {0, I_i1, I_i2, C_i}`, and both contain `0` and `C_i`.

*Why this kills the port method at offsets `(0, 0)`.*
- Let `P` be any statement derived only from (P1) and (P2) for a configuration with offsets `(0, 0)`: a cycle
  with some property, an extremal coset, a degree count.  Then `P` holds for the configuration above.
- A contradiction derived from (P1) and (P2) at offsets `(0, 0)` would therefore show that this configuration does
  not exist, which is false.
- Every `u + w b` with `u_± = w_±` produces, from a hypothetical `alpha`, only such data.  So no such argument
  shows it is regular.
- The data that are lost are the full supports `Out_T = supp(alpha_T w)`, `In_T = supp(alpha_T u)` and the
  coefficient identities.  For example, `1 + b` is regular because `In_T = Out_T` forces a finite
  `b`-invariant set, and that is invisible to (P1) and (P2).

## Part 2 (explicit relations)

`Phi` covers the bouquet of four circles, so the `x_2`-edges define a permutation `pi_2` of the vertex set, and
likewise `pi_1` for the `x_1`-edges.
- *`x_2`-cycles.*  Let `l_1 -> l_2 -> ... -> l_L -> l_1` be a cycle of `pi_2`.  Its label, a relator of `K`, is
  `prod_k a^{C_{l_k}} b a^{-I_{l_{k+1} 2}}`, with indices mod `L`.  A cyclic conjugate of it is
  `prod_k b a^{C_{l_{k+1}} - I_{l_{k+1} 2}}`, with exponents `10^{5l} - 10^{5l-3} >= 10^5 - 10^2 = 99900`.
- *`x_1`-cycles.*  Let `l_1 -> ... -> l_L -> l_1` be a cycle of `pi_1`.  Its label is
  `prod_k b a^{-I_{l_{k+1} 1}}`, with exponents `-10^{5l-4} <= -10`.

The walk lemma asks, for offsets `(d_+, d_-)`, for positive relations with:
- (i) all `n >= d_+`;
- (ii) all `n <= d_+`;
- (iii) all `n <= d_-`;
- (iv) all `n >= d_-`.

If `-10 <= d_± <= 99900`, the `x_2`-relation serves for (i) and (iv), and the `x_1`-relation for (ii) and (iii).
So the relation step of `rips-segev-core-large-gap-two-layer-elements-are-regular-proof` can yield no contradiction
for offsets in that box. ∎

**What remains.**
- For Steenbock's graphs, the theorem covers `max|delta_±| > N = 10^{5n}`.  Part 2 blocks the relation method
  inside `[-10, 99900]`.
- Offsets in `(-N, -10)` and `(99900, N)` are not settled by either result.
- The balanced case needs coefficient information: on each coset `f_T = alpha_T u` and `g_T = alpha_T w`, coupled by
  `f = -g · b` across cosets.
