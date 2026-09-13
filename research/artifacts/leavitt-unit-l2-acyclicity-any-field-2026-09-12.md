# L²-acyclicity of binary Leavitt unit groups over every field, 2026-09-12

Lane `ex-lueck-approximation`. Addendum to `research/artifacts/leavitt-unit-l2-acyclicity-2026-09-12.md`,
whose Theorem A (frame criterion) is used unchanged. Status: proved on paper, unreviewed.

**Theorem E.** For every field `K`, all L²-Betti numbers of `L_K(1,2)^x` vanish.

Here `S = L_K(1,2) = K<e, f, e*, f* | e*e = f*f = 1, e*f = f*e = 0, ee* + ff* = 1>`, Khanh's
notation for `s_0, s_1, t_0, t_1`. Positive words are words in `e, f`, and `μ*` is the starred
word of `μ`.

## 1. What Theorem A needs

1. `S` is infinite.
2. `H̃_d(X_r(S); Z) = 0` for `0 <= d <= r-3`.
3. `GL_r(S) ≅ S^x` for every `r`.

Item 3 is the prefix-code isomorphism `M_r(S) ≅ S`, and item 1 follows from (4.1) below;
neither uses the field. For item 2, Khanh's Corollary 4.3 (coning) uses only his
Proposition 4.2. Proposition 4.2 uses his Lemma 4.1 only through three outputs:
- an element `x`;
- left inverses `b_i` with `b_i y_i = 1` for `y_i = a_i x`;
- the kernel of `b_i` as the sibling summand `⊕_ℓ s_ℓ S`, his (4.2).

The rest of Proposition 4.2 (completions, the coordinate maps (4.4), the identification (4.5)
through leaf coordinates) is linear algebra over `S` with no scalar input. So it suffices to
prove Lemma 4.1 over `K`, with `b_i = c_i^(-1) η_i*` for some `c_i in K^x`.

## 2. Lemma 4.1 over K

**(4.1), field free.** If `μ_1, ..., μ_s` are distinct positive words of length at most `D` and
`M > D`, then the words `μ_i e^M f` are pairwise prefix-incomparable. So
`(μ_i e^M f)*(μ_j e^M f) = δ_ij`. Khanh's proof is combinatorics of words. Consequence: a
nonempty `K`-combination of distinct positive words, with nonzero coefficients, is nonzero.
Append `e^M f` and apply the starred form of one word, which returns its coefficient.

**Lemma 4.1_K.** Given nonzero `a_1, ..., a_s in S`, there are `x in S`, nonempty positive
words `η_i` and scalars `c_i in K^x` with `η_i* a_i x = c_i`. So `b_i = c_i^(-1) η_i*` satisfies
`b_i a_i x = 1`, and `ker(b_i ·) = ker(η_i* ·) = ⊕_ℓ s_ℓ S` by Khanh (4.2).

*Proof.* Khanh's proof, keeping track of coefficients.
1. Every element of `S` is a finite `K`-combination of monomials `α β*`: cancel every starred
   letter followed by an unstarred one. Fix such expressions for the `a_i`, and let `N` be at
   least every length `|β|` occurring.
2. Let `γ_1, ..., γ_t` be all words of length `N`, so `Σ_j γ_j γ_j* = 1`. Each `a_i γ_j` is a
   `K`-combination of positive words, since `β* γ_j` is a suffix of `γ_j` or `0`. Because
   `a_i = Σ_j (a_i γ_j) γ_j*` is nonzero, some `a_i γ_j` is nonzero. Collect identical words, and
   let `L` bound the lengths of the remaining words.
3. Put `t_j = e^(j(L+1)) f` and `x_0 = Σ_j γ_j t_j`.
   - The words of `(a_i γ_j) t_j` have lengths in `[j(L+1)+1, j(L+1)+1+L]`, which are disjoint
     for distinct `j`.
   - Right concatenation by `t_j` is injective on words.
   - So `P_i = a_i x_0` is a nonempty `K`-combination of distinct positive words, with nonzero
     coefficients.
4. Choose `M` above every word length in the `P_i` and put `x = x_0 e^M f`. By (4.1) the support
   of `P_i e^M f` is a prefix antichain. Choose `η_i` in it, with coefficient `c_i != 0`. By
   (4.1), `η_i* a_i x = η_i* P_i e^M f = c_i`, and every `η_i` is nonempty. ∎

Over `F_2` every nonzero coefficient is `1`, which is Khanh's statement.

## 3. Proof of Theorem E

- Proposition 4.2 over `S` holds verbatim with `b_i = c_i^(-1) η_i*`. Corollary 4.3 then gives
  `H̃_d(X_r(S); Z) = 0` for `0 <= d <= r-3`.
- Theorem A gives `β_n^(2)(GL_r(S)) = 0` for `n <= r-3`.
- Put `r = n+3` and use `GL_r(S) ≅ S^x`. ∎

**Remarks.**
- If `char K = p > 0`, then `L_(F_p)(1,2) ⊆ L_K(1,2)` unitally, so `L_K(1,2)^x` contains the
  nonsofic `L_(F_p)(1,2)^x` (`d-ary-leavitt-groups-nonsofic-over-finite-fields`) and is nonsofic.
  In characteristic zero, soficity is not addressed here.
- For `char K = 2`, Theorem E is also a case of Corollary C of the main artifact (`B = K`).
