---
rg: 2
id: bmw-40-40-193-281-332-klein-chain-proof
kind: route
title: A hand proof, with no SAT, that the parity kernels of 40_40 #193, #281 and #332 are not left-orderable, via a cyclic chain of four Klein-bottle relations between two-letter words and their letter conjugates
target: bmw-40-40-193-281-332-parity-kernels-not-left-orderable
requires: []
artifacts:
  - experiments/bmw-klein-chains-2026-09-17/README.md
  - experiments/bmw-klein-chains-2026-09-17/chains_40_40.json
  - experiments/bmw-klein-chains-2026-09-17/verify_klein.py
  - experiments/bmw-klein-chains-2026-09-17/verify_klein.log
  - experiments/bmw-klein-chains-2026-09-17/kscan.py
  - experiments/bmw-census-left-orders-2026-09-17/census_40_40.json
---

This proof is readable and checkable by hand. It uses only the 16 squares of each class and one
elementary lemma about left orders. `verify_klein.py` repeats every group computation by rewriting to
normal form and prints the full rewriting traces (`verify_klein.log`). The proof itself does not depend
on that script.

## 1. Setting

For a class `c` of `census_40_40.json`, the group is
`Γ = ⟨v_0..v_3, h_0..h_3 | v_i^2, h_j^2, h v = v' h' for each square SQ_c(h, v) = (v', h')⟩`. The
parity kernel `Γ^+` is the index-4 subgroup of words with an even number of `v`-letters and an even
number of `h`-letters.

**Normal forms.** Every element of `Γ` has a unique normal form: a freely reduced `v`-word followed by
a freely reduced `h`-word. This comes from the confluent rewriting system
`{xx → 1, h v → v' h'}` (`bmw-40-40-193-281-332-subgroup-cone-certificate-proof`, §1). It is also
standard for BMW groups, because `⟨v_0..v_3⟩` and `⟨h_0..h_3⟩` act simply transitively on the
vertices of the two trees. The proof uses only one consequence: a nonempty freely reduced word in the
`v`-letters alone, or in the `h`-letters alone, is `≠ 1` in `Γ`.

**Notation.** All letters are involutions, so conjugation by a letter `p` is `w ↦ p w p`.
- For words `a` and `b`, "`a` inverts `b`" means `a b a^{-1} = b^{-1}`.
- For a letter `p` and a letter `r` of the other type, a square `p r = r' p` with the same `p` on both
  sides says that `p r p = r'`. So `p` acts on the opposite letters by conjugation.

## 2. The Klein lemma

For an element `g` of a left-ordered group, write `|g| = max(g, g^{-1})`, so `|g| ≥ 1`.

**Lemma 1.** Let `<` be a left order on a group `G`, and let `a, b ∈ G` with `b ≠ 1` and
`a b a^{-1} = b^{-1}`. Then `|b| < |a|`.

*Proof.*
1. **We may assume `b > 1` and `a > 1`.**
   - The hypothesis is unchanged if `b` is replaced by `b^{-1}`.
   - Inverting both sides gives `a b^{-1} a^{-1} = b`, that is `a^{-1} b a = b^{-1}`. So the
     hypothesis is also unchanged if `a` is replaced by `a^{-1}`.
   - `a ≠ 1`, because otherwise `b = b^{-1}`, so `b^2 = 1`. A left-ordered group is torsion-free
     (if `b > 1` then `b^2 > b > 1`), so `b = 1`, a contradiction.
2. **It suffices to show `a > b`.** Then `a > b > 1 > b^{-1}`, so `|b| = b < a = |a|`.
3. **`a ≠ b`.** If `a = b`, then `a` commutes with `b`, so `b = b^{-1}`, which is excluded as above.
4. **`a < b` is impossible.** Suppose `a < b`, and put `g = b^{-1} a`.
   - Left multiplication by `b^{-1}` gives `g < 1`.
   - Left multiplication of `g < 1` by `g` gives `g^2 < g < 1`.
   - The relation gives `a b^{-1} = b a`. Hence `g^2 = b^{-1} (a b^{-1}) a = b^{-1} b a a = a^2`.
   - But `a > 1` implies `a^2 > a > 1`, a contradiction. ∎

**Corollary 2 (Klein chains).** Suppose `x_1, …, x_m` are nontrivial elements of a group `G`, and
`k_1, …, k_m` are nonzero integers, such that `x_{i+1}` inverts `x_i^{k_i}` for every `i` (indices
mod `m`). Then `G` is not left-orderable.

*Proof.*
- Suppose `G` has a left order. It is then torsion-free, so `x_i^{k_i} ≠ 1`.
- If `g > 1`, then `g^{k+1} = g · g^k > g`, by induction and left multiplication. So `|g^k| ≥ |g|`
  for every `k ≠ 0`.
- Lemma 1 then gives `|x_1| ≤ |x_1^{k_1}| < |x_2| ≤ ⋯ < |x_m| ≤ |x_m^{k_m}| < |x_1|`. ∎

Remarks.
- **`m = 1` and `m = 2` with all `k_i = 1` cannot occur in a torsion-free group.**
  - `m = 1` would mean `x = x^{-1}`.
  - For `m = 2`, `x_1` inverting `x_2` gives that `x_1^2` commutes with `x_2`. But `x_2` inverting
    `x_1` gives `x_2 x_1^2 x_2^{-1} = x_1^{-2}`. So `x_1^4 = 1`.
- **Promislow's group** `⟨x, y | x y^2 x^{-1} = y^{-2}, y x^2 y^{-1} = x^{-2}⟩` is the case `m = 2`,
  `k_1 = k_2 = 2`. This is the classical reason it is not left-orderable. It is virtually `Z^3`, so it
  cannot embed in the two-dimensional CAT(0) group `Γ`. The search in `w6-107c` also found no pair of
  this kind among letter words of length at most 4.
- The chains below have `m = 4` and all `k_i = 1`. Each element is a two-letter word or a letter
  conjugate of one.

## 3. Two elementary moves

Everything below uses only two kinds of step, each read off from squares.

**(K) Klein pair from a centralizer and a swap.** Let `r s` be a two-letter word in one family.
Let `p` and `q` be letters of the other family such that:
- `p` commutes with `r` and with `s` (squares `p r = r p`, `p s = s p`);
- `q (r s) q = (r s)^{-1} = s r`.

Then `pq` inverts `rs`:
`(pq)(rs)(pq)^{-1} = p (q r s q) p = p (s r) p = s r`.

The second condition holds, for example, when `q r q = s` and `q s q = r`, that is, when `q`
swaps `r` and `s`. The word `pq` has two letters of the same family, so it lies in `Γ^+`.

**(C) Letter conjugation.** If a letter `p` acts on the opposite letters by a permutation (squares
`p r = r' p` for all four `r`), then conjugating by `p` maps a relation "`a` inverts `b`" to
"`p a p` inverts `p b p`". Here `p b p` is computed letter by letter when `b` is a word in the
opposite family.

In each class, the chain is built from two Klein pairs (K) and two letter conjugations (C).

## 4. Class #281

The squares that are not commutations are:
`h0v3=v3h1`, `h1v1=v2h2`, `h1v2=v1h2`, `h1v3=v3h0`, `h2v1=v2h1`, `h2v2=v1h1`, `h3v0=v1h3`, `h3v1=v0h3`.
The commuting pairs are `h0v0`, `h0v1`, `h0v2`, `h1v0`, `h2v0`, `h2v3`, `h3v2`, `h3v3`.

**Letter actions.**
- `h3` fixes `v2` and `v3` and swaps `v0 ↔ v1` (from `h3v0=v1h3` and `h3v1=v0h3`).
- `v3` fixes `h2` and `h3` and swaps `h0 ↔ h1`. Multiplying `h0v3=v3h1` on the left by `v3` gives
  `v3h0v3 = h1`, and likewise `h1v3=v3h0` gives `v3h1v3 = h0`.
- `h3` and `v3` commute.

**The two Klein pairs.** Put `A = h0h2`, `D = v1v2`, `E = v0v2` and `F = h1h2`.
- **(R1) `A` inverts `D`.**
  - `h0` commutes with `v1` and `v2`.
  - `h2 v1 v2 = v2 h1 v2 = v2 v1 h2`, using `h2v1=v2h1` and then `h1v2=v1h2`. So `h2 D h2 = D^{-1}`.
  - Apply (K).
- **(R2) `E` inverts `F`.**
  - `v0` commutes with `h1` and `h2`.
  - `h2v1=v2h1` gives `v2h1 = h2v1`, and `h1v2=v1h2` gives `v1h2 = h1v2`. So
    `v2 h1 h2 v2 = h2 v1 h2 v2 = h2 h1 v2 v2 = h2 h1`, that is `v2 F v2 = F^{-1}`.
  - Apply (K).

**The chain.** Put `B = v3 E v3 = v3v0v2v3` and `C = h3 F h3 = h3h1h2h3`. The chain is
`x_1 = A`, `x_2 = B`, `x_3 = C`, `x_4 = D`.
1. **`B` inverts `A`.** Conjugate by `v3`. `v3 B v3 = E`, and `v3 A v3 = h1h2 = F` (because `v3`
   swaps `h0, h1` and fixes `h2`). This is R2.
2. **`C` inverts `B`.** Conjugate by `t = v3h3 = h3v3`.
   - `t C t^{-1} = v3 h3 (h3 F h3) h3 v3 = v3 F v3 = v3 h1 h2 v3 = h0 h2 = A`.
   - `t B t^{-1} = h3 v3 (v3 E v3) v3 h3 = h3 E h3 = h3 v0 v2 h3 = v1 v2 = D`.
   - So this is R1.
3. **`D` inverts `C`.** Conjugate by `h3`. `h3 D h3 = v0v2 = E` and `h3 C h3 = F`. This is R2.
4. **`A` inverts `D`.** This is R1.

All four elements are nonempty reduced words in a single family, so they are nontrivial. All four have
even length in one family, so they lie in `Γ^+`. By Corollary 2, `Γ^+(#281)` is not left-orderable.

## 5. Class #332

The squares that are not commutations are:
`h0v3=v3h1`, `h1v0=v0h2`, `h1v1=v2h1`, `h1v2=v1h1`, `h1v3=v3h0`, `h2v0=v0h1`, `h2v1=v2h2`, `h2v2=v1h2`,
`h3v0=v1h3`, `h3v1=v0h3`.
The commuting pairs are `h0v0`, `h0v1`, `h0v2`, `h2v3`, `h3v2`, `h3v3`.

**Letter actions.** The actions of `h3` and `v3` are exactly as for #281:
- `h3` swaps `v0 ↔ v1` and fixes `v2`, `v3`;
- `v3` swaps `h0 ↔ h1` and fixes `h2`, `h3`;
- `h3` and `v3` commute.

**The two Klein pairs**, with the same `A`, `D`, `E`, `F`:
- **(R1) `A = h0h2` inverts `D = v1v2`.**
  - `h0` commutes with `v1` and `v2`.
  - `h2` swaps `v1 ↔ v2` (`h2v1=v2h2`, `h2v2=v1h2`).
  - Apply (K).
- **(R2) `E = v0v2` inverts `F = h1h2`.**
  - `v0` swaps `h1 ↔ h2`: `h2v0=v0h1` gives `v0h2v0 = h1`, and `h1v0=v0h2` gives `v0h1v0 = h2`.
    So `v0 F v0 = F^{-1}`.
  - `v2` centralizes `F`. `h1v1=v2h1` gives `v2h1 = h1v1`, and `h2v2=v1h2` gives `v1h2 = h2v2`. So
    `v2 h1 h2 v2 = h1 v1 h2 v2 = h1 h2 v2 v2 = h1 h2`.
  - Hence `E F E^{-1} = v0 (v2 F v2) v0 = v0 F v0 = F^{-1}`. This is (K) with the roles of the two
    letters exchanged.

**The chain.** It is word for word the chain of §4, `A, B = v3v0v2v3, C = h3h1h2h3, D`. Steps 1–4 of
§4 used only R1, R2 and the actions of `v3` and `h3`, and those are the same here. So
`Γ^+(#332)` is not left-orderable.

## 6. Class #193

The squares that are not commutations are:
`h0v3=v3h1`, `h1v2=v2h2`, `h1v3=v3h0`, `h2v0=v1h2`, `h2v1=v0h2`, `h2v2=v2h1`, `h3v1=v3h3`, `h3v3=v1h3`.
The commuting pairs are `h0v0`, `h0v1`, `h0v2`, `h1v0`, `h1v1`, `h2v3`, `h3v0`, `h3v2`.

**Letter actions.**
- `h3` swaps `v1 ↔ v3` and fixes `v0`, `v2`.
- `v2` swaps `h1 ↔ h2` and fixes `h0`, `h3`.
- `h2` swaps `v0 ↔ v1` and fixes `v3`.
- `v3` swaps `h0 ↔ h1`.
- `h3` and `v2` commute.

**The two Klein pairs.** Put `P = h0h1`, `Q = v0v3`, `R = h0h2` and `S = v0v1`.
- **(R1') `R` inverts `S`.** `h0` commutes with `v0` and `v1`, and `h2` swaps `v0 ↔ v1`. Apply (K).
- **(R2') `Q` inverts `P`.** `v0` commutes with `h0` and `h1`, and `v3` swaps `h0 ↔ h1`. Apply (K).

**The chain.** `x_1 = P`, `x_2 = Q`, `x_3 = h3 R h3 = h3h0h2h3`, `x_4 = v2 S v2 = v2v0v1v2`.
1. **`x_2` inverts `x_1`.** This is R2'.
2. **`x_3` inverts `x_2`.** Conjugate by `h3`. `h3 x_3 h3 = R`, and `h3 Q h3 = v0v1 = S`. This is R1'.
3. **`x_4` inverts `x_3`.** Conjugate by `t = v2h3 = h3v2`.
   - `t^{-1} x_4 t = h3 v2 (v2 S v2) v2 h3 = h3 S h3 = v0 v3 = Q`.
   - `t^{-1} x_3 t = v2 h3 (h3 R h3) h3 v2 = v2 R v2 = h0 h1 = P`.
   - This is R2'.
4. **`x_1` inverts `x_4`.** Conjugate by `v2`. `v2 P v2 = h0h2 = R` and `v2 x_4 v2 = S`. This is R1'.

So `Γ^+(#193)` is not left-orderable. ∎

## 7. What the proof shows about the certificate subgroup

- **The certificate subgroup `M`.** The subgroup `M = ⟨x, y, f x^{-1} f, g y^{-1} g⟩` of
  `bmw-40-40-193-281-332-subgroup-cone-certificate-proof` was an artefact of the search. For #281
  and #332, `x = v0v1` and `y = h0h1`. The chain elements `A, B, C, D` are instead the two-letter
  words `h0h2` and `v1v2`, and the `v3`- or `h3`-conjugates of `v0v2` and `h1h2`.
- **The mechanism is order-of-magnitude, not sign.** Each relation says one element is
  "infinitesimal" against the next, and the four comparisons close up. Each individual Klein relation
  holds in the Klein-bottle group, which is left-orderable. The contradiction comes only from the
  cycle.
- **Why the letter-ball SAT runs missed it.** The comparison `|x_i| < |x_{i+1}|` is a positive-cone
  statement about quotients like `x_i^{-1} x_{i+1}`, and closing the cycle multiplies such quotients.
  So a finite positive-cone refutation along these lines needs products in which both factors are long. The
  letter-ball instances bound one factor to length at most 2 or 4, and cannot contain them. This is
  consistent with the subgroup certificate, whose relations often have two factors of 6 or 8 letters.
- **The criterion needs no ball and no solver.** It is a finite search for a cycle in the directed
  graph "`a` inverts `b`" on short elements. In `census_40_40` the three survivors all have such a
  cycle among elements of letter length at most 4. The product class `#0` has no inverting pair at
  all at that length.
