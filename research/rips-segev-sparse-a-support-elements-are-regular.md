---
rg: 2
id: rips-segev-sparse-a-support-elements-are-regular
kind: claim
title: In a Rips--Segev core every element of k[a^S <b>] is a non-zero-divisor when the a-exponent differences S - S avoid the distinguished-position differences of the lines, for any number of b-layers
distinct_from:
  rips-segev-short-syllable-two-layer-elements-are-regular: that treats two b-layers (u(a) + w(a) b) with contiguous reduced span below m_Gamma; this allows any number of b-layers with arbitrary b-exponents and any a-exponent set whose difference set avoids Dist(Gamma), so spans far above m_Gamma are included.
  rips-segev-core-large-gap-two-layer-elements-are-regular: that needs two layers and an offset outside [Delta_-, Delta_+]; this has no offset condition and covers balanced elements of large span, provided the a-exponent differences miss Dist(Gamma).
  rips-segev-witness-divisors-need-saturated-supports: that reduces {1,a,b,ab} to saturated sets; this contains {1,a,b,ab} as the case S = {0,1}.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question for all elements; this settles it for the class k[a^S <b>] with (S - S) ∩ Dist(Gamma) empty.
artifacts:
  - experiments/rips-segev-multilayer-2026-09-17/neighbour_multilayer.py
  - experiments/rips-segev-multilayer-2026-09-17/results.txt
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-sparse-a-support-elements-are-regular-proof`.

**Setting.**
- `K = (<a> * <b>) / <<R>>` is the core of a generalized Rips--Segev graph `Gamma` whose labelling satisfies
  `Gr'_*(1/8)`.  `G(Gamma) = G_1 *_{<a>} K *_{<b>} G_2` for torsion-free `G_1 ∋ a`, `G_2 ∋ b`.
- A position `l` of line `i` is *distinguished* if `v_il` carries a `b`-edge.
- `Dist(Gamma)` is the finite set of differences `l' - l != 0` of two distinguished positions of one line.  Its
  least absolute value is `m_Gamma`.
- For Steenbock's table `(10^{5i-4}, ..., 10^{5i})`, every element of `Dist(Gamma)` is `± 10^e` or
  `± (10^e - 10^{e'})` with `1 <= e' < e`.  In particular it is a nonzero multiple of 10.

**Theorem.**  Let `k` be any field.  Let `S, J ⊂ Z` be finite and let
`beta = sum_{i in S, j in J} c_ij a^i b^j` be nonzero in `k[K]`.
If `(S - S) ∩ Dist(Gamma)` is empty, then `beta` is a non-zero-divisor in `k[K]` and in `k[G(Gamma)]`.

The same holds for `sum c_ij b^j a^i`, for `g(a) beta` with `g != 0`, and for every translate `x beta y` with
`x, y` in the group.

**Cases.**
- **Short a-span.**  If `S` lies in an interval of length `< m_Gamma`, the hypothesis holds.  For example every
  `u(a) + w(a) b + z(a) b^2` whose joint `a`-span is `< m_Gamma` (`<= 9` for Steenbock's graphs) is regular,
  with no condition on the coefficients.  This is the three-layer statement asked for in
  `rips-segev-short-syllable-two-layer-elements-are-regular`, for any number of layers.
- **Steenbock's graphs.**  It suffices that the exponents in `S` are pairwise incongruent mod 10.  Examples are
  `1 + a^{11} + (2 + a^{23}) b^5 + a^2 b^{-7}` and `(1 + a + a^{12}) + (1 - a^{12}) b`.  These have `a`-span far
  above `m_Gamma`, and their offsets lie in the balanced box of
  `rips-segev-core-large-gap-two-layer-elements-are-regular`.
- **Earlier results.**  `S = {0, 1}` with `1 ∉ Dist` is Theorem 1 of the short-syllable node
  (`k[<b>] + a k[<b>]`, including `{1, a, b, ab}`).  `S = [0, d]` after removing a left factor `g(a)` is its
  Theorem 2.

**Mechanism.**  Write `beta = sum_j u_j(a) b^j = sum_i a^i v_i(b)` and let `C = (c_ij)`.
1. If `rank C <= 1`, then `beta = h(a) v(b)`, a product of non-zero-divisors.
2. *Left annihilators.*  Suppose `rank C >= 2` and `alpha beta = 0` with `alpha != 0`.  Then
   `V = union_j supp(alpha u_j(a))` is finite and nonempty, and every `p in V` has:
   - a neighbour `p b^e` in `V` with `e in J - J`, `e != 0`, since the layers must cancel;
   - a neighbour `p a^n` in `V` with `n in S - S`, `n != 0`.  An isolated point would make all the `u_j`
     proportional.
3. *Walk.*  Alternating the two steps closes a relation `a^{n_1} b^{e_1} ... a^{n_L} b^{e_L} = 1`, with `L >= 1`,
   every `n_k in (S - S) \ {0}` and every `e_k != 0`.
4. *Small cancellation* (Lemma 5 of `rips-segev-short-syllable-two-layer-elements-are-regular-proof`, read
   exactly).  Such a relation has some `n_k in Dist(Gamma)`.  This is a contradiction.
5. *Right annihilators.*  Apply steps 2 to 4 to `alpha^* beta^* = 0`, with the roles of `a` and `b` exchanged:
   `beta^* = sum_i v_i^*(b) a^{-i}`.  Now the `a`-steps are the layer differences, again in `(S - S) \ {0}`.

**Calibration.**
- `F_2`: `Dist` is empty and no alternating relation exists, so all of `k[F_2]` is reproduced.
- `Z^2`: `[a, b] = 1` has `a`-exponents `±1`, so any `S` with `1 in S - S` is excluded, and the method is silent.
- `Z/2 × Z/2`: `(1 + a + b + ab)(1 + a + b - 3ab) = 0`, and the walk reads `abab = 1`.
- Finite groups (`experiments/rips-segev-multilayer-2026-09-17/results.txt`): full left kernels over
  `GF(2), GF(3), GF(5)` for random 2-generator permutation groups, both roles `(x, y) = (a, b), (b, a)`, 2 to 4
  layers with exponents such as `{0,1,3}` and `{-1,0,2}`, and contiguous and sparse `S` (`{0,3}`, `{0,1,4}`,
  `{0,2,3}`).  Seeds 1 to 3: 180 configurations (40 with sparse `S`), 3131 rank-`>= 2` elements, 34765 kernel
  vectors, 0 failures of the neighbour lemma or the walk.  In the rank-one control, `(X_S)` failed on 16526 of
  26600 kernel vectors, so the rank hypothesis is needed.

**Chain criterion (strict reduction, proof §6).**  Let `gamma` be the least syllable length of a cycle label
of `Gamma` and `q = floor((floor(5 gamma/8) - 3)/2)`.  If `Gamma` has no backtrack-free path reading
`b^{e_0} a^{n_1} b^{e_1} ... a^{n_q} b^{e_q}` with all `n_k in S - S` and all `e_k in J - J` (all nonzero), then
`beta` is a non-zero-divisor.  The theorem above is the case `q = 1`.
- For a given explicit `Gamma` this is a finite graph search.
- Example: for Steenbock's table, every `u(a) + w(a) b` of joint `a`-span `<= 89` (for instance `1 + a^{10} + b`)
  is regular if `gamma >= 12` and `Gamma` has no `b`-edge from `v_{1,0}` to `v_{1,10}`.  Both facts depend on the
  explicit gluing, which main does not record.

**What remains.**
- Elements for which `Gamma` has such chains, for example contiguous `S` of `a`-span above `max_i C_i`.  There
  every relator label is a chain, so the next input must be the coefficients along the walk.
