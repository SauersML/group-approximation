# RGR_p: twisted-cyclic reduction of nonsingular words to a cyclic scalar system (lane w5-rgr-p, 2026-09-12)

Target: `rank-ultraproduct-unit-groups-solve-nonsingular-equations` (RGR_p). Fix a prime `p`, an
algebraically closed field `Fbar` of characteristic `p`, a word
`w(t) = c_0 t^(e_1) c_1 ... t^(e_l) c_l` with coefficients `c_i in GL_d(Fbar)` and total exponent
`e = e_1 + ... + e_l != 0`, and `eps > 0`. RGR_p asks for `k`, `t in GL_(dk)` and `lambda in Fbar^x`
with `rank(w(t) - lambda 1) <= eps dk`, where each `c_i` is read as `c_i (x) 1_k`.

This note does three things, none of which decides RGR_p in general:
- Section 1: an **exact** amplification by `|e|` that makes `w(t)` block-diagonal, so that a solution of
  a finite **cyclic scalar system** in `|e|` matrix unknowns is an RGR_p witness; conversely, every
  witness gives a solution after one further amplification.
- Section 2: the scalar-target power word `t^e = lambda 1` is solvable **exactly**, in every
  characteristic, with no `p`-subtlety -- a companion matrix. This isolates the `p`-divisibility
  difficulty of the Attempts note as belonging to *general-matrix* targets only.
- Section 3: the two-syllable positive word `c_0 t c_1 t c_2` is solvable **exactly** (explicit `t`),
  and the equal-exponent two-syllable word reduces to power words. Section 4: where it stops.

## 1. The twisted-cyclic amplification

Amplify by `k = |e|`. Write `W = W_0 (+) ... (+) W_(|e|-1)`, each `W_j = Fbar^d`; so `dim W = d|e|` and
`c_i (x) 1_(|e|) = diag(c_i, ..., c_i)` acts as `c_i` on every block.

Define `t in GL(W)` as a **twisted cyclic shift**: choose `b_0, ..., b_(|e|-1) in GL_d` and set
`t|_(W_j) = b_j : W_j -> W_(j+1 mod |e|)`. Then `t` is invertible, and `t^(pm 1)` shifts block index by
`pm 1`, carrying the `Fbar^d` factor by `b_j^(pm 1)`.

**Lemma 1.1 (block-diagonality).** Because the total `t`-exponent of `w` is `e` and the cycle has length
`|e|`, `w(t)` maps each `W_m` back to `W_m`. Evaluating the interleaved product, the restriction to `W_m`
is

```text
P_m = c_0 . B_1(m) . c_1 . B_2(m) . ... . B_l(m) . c_l,
```

where `B_i(m)` is the ordered product of the `|e_i|` shift-twists (or their inverses, if `e_i < 0`)
met while the `i`-th syllable `t^(e_i)` runs, starting from block `m`. For a positive word the index sets
for `B_1(m), ..., B_l(m)` partition `{0, ..., e-1}` cyclically and rotate with `m`.

**Proposition 1.2 (reduction).** `w(t) = lambda 1_(d|e|)` **iff** `P_m = lambda 1_d` for every
`m in {0, ..., |e|-1}`. More generally `rank(w(t) - lambda 1) = sum_m rank(P_m - lambda 1_d)`, since `w(t)`
is block-diagonal. Hence a solution of the **cyclic system** -- *choose `b_0, ..., b_(|e|-1) in GL_d` and
`lambda` making the `|e|` cyclic products `P_m` simultaneously scalar, up to total rank `eps d|e|`* -- is an
RGR_p witness at amplification `k = |e|`.

For a **positive** word each `B_i(m)` is a product of `e_i >= 1` free invertibles, hence an arbitrary
element of `GL_d`; the coupling between the `|e|` equations is that the same `b_j` appear, cyclically
shifted, across the `P_m`.

**Correction (w4-vf-linear-b, Section 30.1 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`).**
An earlier version of this note called the cyclic system "the whole content of RGR_p, repackaged with no
loss", at amplification `k = e`. The converse needs one further amplification.
- A general witness need not be a twisted shift: for `c_0 t c_1 t c_2`, `t = diag(u, u)` with
  `u c_1 u = c_0^(-1) lambda c_2^(-1)` is a witness at amplification 2 but not a shift.
- If `t in GL_(dk)` is a witness and `S` is the cyclic permutation matrix on `|e|` blocks, then `t (x) S` is
  a twisted cyclic shift with every twist equal to `t`, over the coefficients `c_i (x) 1_k`, and
  `w(t (x) S) = w(t) (x) S^e = w(t) (x) 1`, with the same normalized error.
- So RGR_p holds for the word iff, for every `eps`, the cyclic system is `eps`-solvable over some
  amplification `c_i (x) 1_k` of the coefficients.

## 2. Scalar-target power words (no `p`-subtlety)

**Proposition 2.1.** For any field `K` and `e != 0`, `t^e = lambda 1` has a solution `t in GL_(|e|)(K)`,
hence `t (x) 1_d in GL_(|e|d)`. For `e > 0` take the companion matrix `C` of `x^e - lambda`:
`C e_i = e_(i+1)` (`i < e`), `C e_e = lambda e_1`. Then `C^e = lambda 1_e` and
`det C = (-1)^(e-1) lambda != 0`. For `e < 0`, `t^e = lambda 1` iff `(t^(-1))^|e| = lambda 1`, so take
`t = C^(-1)` with `C` the companion matrix of `x^|e| - lambda`; alternatively take `t` to be the companion
matrix of `x^|e| - lambda^(-1)`. (The `e < 0` case was added at the request of w4-vf-linear-b, Section 30.2.)

This is the `l = 1`, `c_0 = c_1 = 1` case of Section 1: `C (x) 1_d` is itself the twisted cyclic shift on
`|e|` blocks with twists `1, ..., 1, lambda 1_d` (for `e < 0`, the companion matrix of `x^|e| - lambda^(-1)`,
with last twist `lambda^(-1) 1_d`), and every rotation `P_m` equals `lambda 1_d`. (Corrected: an earlier
version described this as one block-equation `P_0 = lambda` solved by `b_0 = C`.) The `p | e` Jordan
subtlety recorded in the node's Attempts is therefore **not** about scalar targets: it arises only for
*general-matrix* targets `t^e = M`, where a unipotent block of `M` can fail to be a `p`-th power. RGR_p
produces a scalar target for pure powers, so pure powers are unconditionally clean.

## 3. Two-syllable positive words

**Proposition 3.1.** `w(t) = c_0 t c_1 t c_2` is solvable exactly: `w(t) = lambda 1_(2d)` with
`t in GL_(2d)`, for every `lambda != 0`.

*Proof.* Amplify by `e = 2`: `t = [[0, b_1], [b_0, 0]]` on `W_0 (+) W_1`. By Lemma 1.1,
`w(t) = diag(P_0, P_1)` with `P_0 = c_0 b_1 c_1 b_0 c_2` and `P_1 = c_0 b_0 c_1 b_1 c_2`. Put
`K = c_0^(-1) lambda c_2^(-1)`. Then `P_0 = P_1 = lambda 1` iff `b_1 c_1 b_0 = b_0 c_1 b_1 = K`. Set
`A = c_1 b_0, B = c_1 b_1`; the two equations become `B A = A B = c_1 K`. Take `A = 1`, `B = c_1 K`:
then `b_0 = c_1^(-1)`, `b_1 = K`. Check `b_1 c_1 b_0 = K c_1 c_1^(-1) = K`, `b_0 c_1 b_1 = c_1^(-1) c_1 K
= K`. Direct block computation gives `w(t) = diag(lambda, lambda) = lambda 1_(2d)`. `b_0, b_1 in GL_d`
so `t in GL_(2d)`. QED.

**Proposition 3.2 (equal exponents).** `c_0 t^(e') c_1 t^(e') c_2` reduces to power words: put
`u = t^(e')`; then `u c_1 u = K` iff `(c_1 u)^2 = c_1 K`, so `c_1 u = (c_1 K)^(1/2)` (a square root of an
invertible matrix, which exists over `Fbar` after amplification -- the `p = 2` unipotent case is the
established power-word result), then `t = u^(1/(e'))` is another power word. Both steps lie in the
established scalar/general power-word class.

## 4. Where it stops

- **General cyclic system.** For a general positive word the `|e|` equations `P_m = lambda` share the
  `b_j` under cyclic rotation, with the fixed `c_i` **not** rotating. The rotations are therefore not
  mutually conjugate (that holds only in the coefficient-free case), so the system does not collapse to
  one equation. By the Correction in Section 1 it is as hard as RGR_p itself.
- **Rank slack lives inside the blocks, not across them.** A twisted cyclic shift makes `w(t)`
  block-diagonal only when the number of blocks divides `e`, so that number is at most `|e|`, and the
  "solve on a big subspace, correct at small rank" telescoping along a long chain of blocks is unavailable.
  After the further amplification of Section 1, each block equation `P_m = lambda` is `(dk) x (dk)` and may
  carry rank error `eps dk`; that in-block slack remains available. (Corrected: an earlier version said
  slack only allows dropping a fixed number of blocks.)
- **First open shapes.** The general all-exponent-one word `c_0 t c_1 ... t c_l` for `l >= 3`, and the
  unequal-exponent two-syllable word `c_0 t^(e_1) c_1 t^(e_2) c_2` with `e_1 != e_2`, are the smallest
  words not settled by Sections 2-3. Deciding either would show whether the cyclic system is always
  solvable.
