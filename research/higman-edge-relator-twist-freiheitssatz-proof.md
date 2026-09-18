---
rg: 2
id: higman-edge-relator-twist-freiheitssatz-proof
kind: route
title: Conjugating by b rewrites [a,c] as a^-1 c^-lambda a c^3 with lambda = 3^(3^-1) = 3 mod 8; the square survives in a class-7 2-quotient of <a,c | a^8, c^8, [a,c]^2>, and its c-exponent sum of valuation 4 drags d^64 into <a,c>
target: higman-edge-relator-twist-breaks-tree-lattice-freiheitssatz
requires:
  - higman-edge-closure-absorbs-b-powers
artifacts:
  - experiments/higman-freiheitssatz-obstruction-2026-09-18/twist.g
  - experiments/higman-freiheitssatz-obstruction-2026-09-18/twist-output.txt
  - experiments/higman-freiheitssatz-obstruction-2026-09-18/valuations.py
  - experiments/higman-freiheitssatz-obstruction-2026-09-18/valuations-output.txt
---

Notation is as in the target. Throughout, `m = 2^e`, `t = 3^-1 mod m` and `lambda = 3^t mod m`.

## 0. Two 2-adic facts

**(V1)** `t = 3 mod 8`, `v_2(t - 1) = 1`, `lambda = 3 mod 8`, and `v_2(3 - lambda) = 3` whenever
`e >= 4`. Here `3 - lambda` is read as an integer in `(-m, m)`, and its valuation is taken
mod `m`.

*Proof.*
- The congruence `3t = 1 mod 8` gives `t = 3 mod 8`, so `t - 1 = 2 mod 8`.
- Lifting the exponent: for even `k`, `v_2(3^k - 1) = v_2(k) + 2`. Hence
  `v_2(3^(t-1) - 1) = 3`.
- `3 - lambda = 3 - 3^t = -3 (3^(t-1) - 1) mod m`. This has valuation 3 as soon as `m > 8`, and
  `lambda = 3 mod 8` in all cases.
- When `e = 3` we get `t = 3`, `lambda = 27 mod 8 = 3`, and `3 - lambda = 0`. ∎

**(V2)** Put `Y = 2 (3 - lambda)`. For `e >= 5`, `v_2(Y mod m) = 4`. For `e >= 7`,
`v_2(3^Y - 1 mod m) = 6`, and the same holds with `Y` replaced by `-Y`.

*Proof.* By (V1) and LTE again: `v_2(3^Y - 1) = v_2(Y) + 2 = 6`, and this is visible mod `m` once
`m > 64`. The case `-Y` follows from `3^-Y - 1 = -3^-Y (3^Y - 1)`. ∎

`valuations.py` checks (V1), (V2) and `lambda mod 8 = 3` for `e = 3..80`. It also checks the
exponent sums of the whole twisted orbit: `v_2(3^k - 3^(k t)) = 3 + v_2(k)`.

## 1. The twist identity

Let `a, b, c` satisfy `a^-1 b a = b^3`, `b^-1 c b = c^3` and `b^m = c^m = 1`.
- Since `3t = 1 mod m`, we get `a^-1 b^t a = b^(3t) = b`, that is, `a b = b^t a`.
- So `(a b)^-1 c (a b) = (b^t a)^-1 c (b^t a) = a^-1 (b^-t c b^t) a = a^-1 c^(3^t) a = a^-1 c^lambda a`.
- Since `b^-1 a^-1 c a b = a^-1 c^lambda a` and `b^-1 c b = c^3`, we get
  `b^-1 [a,c] b = b^-1 (a^-1 c^-1 a) b · b^-1 c b = a^-1 c^-lambda a · c^3`.

Squaring gives `S_e = b^-1 R b = (a^-1 c^-lambda a c^3)^2`. This is a word in `a, c`, so it lies in `A`,
and it is a conjugate of `R`. `twist.g` Part 1 checks the identity in 2-quotients of `K1(m)` for
`e = 2..5`. That check is a sanity test only; the proof is the computation above. ∎

## 2. S_e is not in <<R>>_A for e >= 3

Adding the relations `a^8 = c^8 = 1` gives a surjection `Abar_m -> Abar_8` for `e >= 3`. By (V1),
`lambda = 3 mod 8`, so `S_e` maps to `(a^-1 c^-3 a c^3)^2 = [a, c^3]^2`. This is `S_3` itself, because
`lambda_3 = 3`.

`twist.g` Part 2 computes the lower exponent-2 central quotients of
`Abar_8 = < a, c | a^8, c^8, [a,c]^2 >` with `EpimorphismPGroup`. In the class-7 quotient, of order
`2^43`, the image of `S_3` has order 2. So `S_3 != 1` in `Abar_8`, and therefore `S_e != 1` in
`Abar_m` for every `e >= 3`.

Part 2 also records the orders of `S_e` directly for `e = 4, 5, 6`:
- `e = 4`: order 2 at class 7;
- `e = 5`: order 2 from class 5 on;
- `e = 6`: order 4 at classes 6 and 7.

Since `S_e = 1` in `K1/<<R>>_{K1}` and `S_e != 1` in `A/<<R>>_A`, the map
`A/<<R>>_A -> K1/<<R>>_{K1}` is not injective.

For `e >= 5` there is a second, computation-free proof: `S_e` has exponent sums
`(e_a, e_c) = (0, Y)` with `v_2(Y) = 4 < e`, so it is already nontrivial in
`Abar_m^ab`. That group is `(Z/m)^2`, because `R` lies in `A'`.

The failure is exactly the failure of the Lemma 6.1 hypothesis in the tree-lattice node, which is
pending landing. That node proves the embedding for `m | n + 1` (Prop 6.3), which covers
`m = 2, 4`. There `lambda_2 = 3 = -1 mod 4`, so `S_2 = [a, c^-1]^2`, and by Prop 6.3 it lies in `<<R>>_A`.

A remark on why no choice of the other amalgam repairs this: `R` lies in the normal subgroup
`F = <<c>>_{K1}`, and `F` is contained in `A`. So `<<R>>_{K1}` is the normal closure in `A` of the
twists `b^-k R b^k`. The Freiheitssatz is therefore equivalent to `<<R>>_A` being invariant under the
twist, and item 2 shows that it is not. ∎

## 3. Abelian bound

Let `Q` be a quotient of `Gammabar_e` and let `Abar_Q` be the image of `A`. `Abar_Q^ab` is a quotient
of `A^ab = (Z/m)^2`, and the image of `S_e` there is `(0, Y)`. Since `S_e = 1` in `Q`, we get
`c^Y in [Abar_Q, Abar_Q]`.
- For `e >= 5`, `Y = 16 u` with `u` a unit mod `m/16`. As `c^m = 1`, this gives `c^16` in the derived
  subgroup.
- For `a`, use the `d`-twist. Item 1 with `(a, b, c)` replaced by `(c, d, a)` uses
  `d^c = d^3`, `a^d = a^3` and `d^m = a^m = 1`, and gives `d^-1 [c,a] d = c^-1 a^-lambda c a^3`.
  Since `[c,a]^2 = R^-1`, the element `S'_e = (c^-1 a^-lambda c a^3)^2` is trivial in `Q`. Its
  exponent sums are `(Y, 0)`, so `a^16` is in the derived subgroup. This is the image of item 1 under
  the symmetry `sigma^2 : a <-> c, b <-> d` of `H4(3)`, which sends `R` to `R^-1`.
- For `e <= 4`, `m <= 16` and there is nothing to prove.

In a finite 2-quotient `P` of `H4(3)/<<R>>`, choose `e` with `2^e >= exp(P)`. Then `P` is a quotient
of `Gammabar_e` by universality, and the bound applies. Passing to the inverse limit gives the bound
for the closure of `<a,c>` in the pro-2 completion.

`twist.g` Part 3 (`e = 4, 5`) and the w10 tower (classes 4 to 11) show `(Z/16)^2`, so the bound is
attained. ∎

## 4. Index bound

This is `higman-edge-closure-absorbs-b-powers` item 1 applied to the relation `S_e`, whose `c`-exponent
sum is `Y`. Here is the direct computation in `Gammabar_e`, since the group is infinite.
- Write `S_e = prod_s a^(i_s) c^(k_s)` and let `C_s` be the partial sums of the `k`.
- Then `S_e = prod_s (c^(C_(s-1)) a^(i_s) c^(-C_(s-1))) · c^Y`.
- From `c^-C d c^C = d^(3^C)` and `d^-k a d^k = a^(3^k)`:
  - `d^-1 (c^C a^i c^-C) d = c^C d^(-3^C) a^i d^(3^C) c^-C = c^C a^(i 3^(3^C)) c^-C`, which lies in `A`;
  - `d^-1 c^Y d = d^(3^-Y - 1) c^Y`.
- Hence `1 = d^-1 S_e d = alpha · d^(3^-Y - 1) c^Y` with `alpha in Abar`, so `d^(3^-Y - 1)` lies in
  `Abar`.
- By (V2), for `e >= 7` this is `d^(64 v)` with `v` odd, so `d^64` lies in `Abar`. For `e <= 6`,
  `d^64 = 1`.
- The same computation with `S'_e` conjugated by `b` shows that `b^64` lies in `Abar`. It uses
  `a^-k b a^k = b^(3^k)` and `b^-1 c b = c^3`, which are the images of the two relations above
  under `sigma^2`.

The tree-lattice node (normal forms in `K1 = G(a,b) *_<b> G(b,c)`) gives `K1 = A · <b>` and
`K2 = A · <d>` as sets. So `Kbar_1 = Abar <b>` and `Kbar_2 = Abar <d>`, and the indices are at most
`[<b> : <b> ∩ Abar] <= 64` and `[<d> : <d> ∩ Abar] <= 64`. ∎

## 5. The tree collapses for e >= 7

Suppose `<<R>>_{Gamma_e}` were contained in `A`.
- By section 4, `d^(64 v) alpha^-1 in <<R>> ⊆ A` for some `alpha in A`, so `d^(64 v) in A`.
- In `Gamma_e`, the subgroup `<d>` meets `A` trivially. This is the normal-form item of the
  tree-lattice node: `K2 = A <d>` has index `[K2:A] = m`, so the `m` cosets `d^j A` are distinct.
- For `e >= 7`, `d^(64 v) != 1`. This is a contradiction.

If `Gammabar_e = Kbar_1 *_Abar Kbar_2` held with edge index `m`, then `<d>` would meet `Abar` trivially,
since the `m` cosets `d^j Abar` would be distinct. That contradicts section 4. More generally, by
section 4 any splitting of `Gammabar_e` over `Abar` with vertex groups `Kbar_i` has edge index at most
64. ∎

## What is left

`ord(a) = m` in `Gammabar_e` is equivalent to `<a>` meeting `<<R>>` trivially. The twist gives no obstruction for the **B-splitting** `Gamma_e = L1 *_B L2`, where
`L1 = <d,a,b>`, `L2 = <b,c,d>` and `B = <b,d>`, because `R` is not in a factor there. In the
normal form over `B`, `[a,c] = a^-1 · c^-1 · a · c` alternates `L1, L2, L1, L2`, so `R` is cyclically
reduced of length 8.

A Freiheitssatz `L1 -> Gammabar_e` for this exponent-2 proper power would give `ord(a) = m` for all
`e`, and would close the target question via the reduction to infinitely many `m`. We know of no proper-power Freiheitssatz for one-relator quotients of amalgams that covers exponent
2 with finite-by-(virtually free) factors. The Howie and Duncan–Howie results need
locally indicable factors or a larger exponent, and the factors here have torsion. Section 4 also shows that such a Freiheitssatz must coexist with `d^64 in Abar`, which
involves `c`, so there is no contradiction.
