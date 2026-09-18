# Referee report (gq-referee-a, proof-gap lens): the SL_3 Toeplitz harmonic ring R_T

**Reviewed:** `sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational` and its route `-proof` (lane gq-deep-adelic-1,
f9dbfcd34), read on origin/main. I read part 6 closely, as the author asked.

**Verdict: PASS for parts 1–6, as proof steps.** Two nits follow (§3).

The node's trust surfaces:
- T2, Fuglede–Kadison;
- T3, the Loday product;
- Lee–Szczarba;
- the Cecchi Bernales–Cortez–Gómez theorem (CBCG).

Two lane nodes I have not reviewed:
- `matricial-divisibility-kills-rational-k2-symbols`, used in parts 4 and 6.5;
- `q-algebra-elementary-quotients-contain-gl-n-q`, used in part 3.

## 1. Parts 1–5
- **Part 1.** The harmonic-elimination node applies (PASS, same landing): `Γ_0 = Γ`, the chain is strict and
  normal, and `π` is equivariant.
- **Part 2, local constancy.** This argument is neat and correct.
  - For a clopen `W`, `b(W) ⊆ Q` is compact and countable, so it has an isolated point `q`.
  - Then `b^{-1}(q) ∩ W` is open and nonempty.
  - So every coefficient is locally constant on a dense open set, with no appeal to the structure of the fibres
    of `π`.
- **Part 2, compression.**
  - Choose `W` inside the open set `{b_e ≠ 0}`. Then the isolated value `r` is nonzero.
  - Freeness comes from freeness on `K`: `Γ` embeds in the profinite group `K`, because `∩ Γ_n = 1`.
  - Minimality holds because `X` is a Toeplitz subshift.
  - So the steps (c)–(d) that I passed at c3b5eab28 apply.
- **Part 2, the centre.** Correct, by the same comparison of coefficients as in (d).
- **Part 3.** Correct.
  - `(X, ν) ≅ (K, Haar)`, and Haar measure is ergodic because `Γ` is dense in `K`. So `L^∞ ⋊ Γ` is a II_1
    factor.
  - `ψ([λ]) = |λ|`, so `λI_N ∈ E_N` forces `|λ|^N = 1`.
- **Part 4.**
  - `cl Γ(d)` is an open subgroup of `K`. Its `[Γ : Γ(d)]` cosets are the closures of the cosets of `Γ(d)`, so
    the matrix units work.
  - `n_d = |SL_3(Z/d)|`. The `p`-part of `|SL_3(Z/p^k)|` is `p^{8k−5}`, and `8k − 5 ≥ k`, so `d | n_d`.
- **Part 5.** Correct as stated. Hypothesis 4 of the corner-Laurent node fails for every `Γ(d)`.

## 2. Part 6
- **`v` is a unit.** `γC = C` because `Γ(d)` is normal. The cross terms vanish, and `v^{-1} = χ_C u_{γ^{-1}} + (1 − χ_C)`.
- **Step 1, the monomial form.** I recomputed the entry of `v` in the level-`d^2` matrix-unit picture.
  - For `bC' ⊆ C`, the entry `χ_{C'} u_a^{-1} v u_b χ_{C'}` is nonzero only for `aC' = γbC'`. There it equals
    `χ_{C'} u_{a^{-1}γb}`, with `a^{-1}γb` in the stabilizer `Γ(d^2)`.
  - Outside `C` the matrix is the identity.
  - `C` is the union of the sub-blocks `sC'`, because `t'Γ(d) = ∪_s s t' Γ(d^2)` by normality.
- **Step 2.** A monomial matrix factors as `D·P`, so its class is `[D] + [P]`.
  - `P·diag(sgn P, 1, …)` lies in `SL(Z) = E(Z)`, so `[P] = ε·[1]`.
  - Under Morita this class is the class of `1 − 2χ_{C'}` when `ε = −1`.
- **Step 3.** `h ↦ χ_{C'} u_h` is a homomorphism `Γ(d^2) → (S')^×`.
  - With representatives `s t'`, the entries are `u` of `t'^{-1} h_s t'`.
  - Their product is the transfer, up to the automorphism of `Γ(d^2)^ab` induced by `t'`. That automorphism
    does not affect vanishing.
- **Step 4.** The transfer node (PASS, same landing) makes the product zero. So `[v] = ε·[χ_{C'}]`.
- **Step 5.** Given T3 and the standard associativity and naturality of products,
  `[λ]·[v] = {λ, ε}·[χ_{C'}]`, which is the image of `{λ, ε} ∈ K_2(Q)` in `K_2(corner)`.
  - The corner is matricially divisible.
  - The indices `[Γ(d^2) : Γ(d^2 m)]` are divisible by `m`. The `p`-parts come from `|SL_3(Z/p^k)|` for
    `p ∤ d`, and from `p^{8b}` for `p | d`.
  - So the image vanishes, given the matricial-divisibility node.
- **Step 6.** `Γ^ab = 0`, so `[u_γ] = 0`. Symbols depend only on the `K_1` class of the second argument, again
  given T3.

## 3. Nits
1. **Part 3 says "for all `N`", but the proof covers only `N ≥ 3`**, through perfectness. For `N ≤ 2`, note that
   elementary matrices are unipotent, so `Δ(e_ij(r)) = 1`.
2. **Part 6.3.** Say that the entries are `u` of `t'^{-1} h_s t'` when the representatives are `s t'`, and that
   conjugation by `t'` preserves the vanishing of the transfer.
