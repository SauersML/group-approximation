---
rg: 2
id: rational-function-fields-embed-in-fp-simple-rings
kind: claim
title: For every k the rational function field Q(t_1..t_k) embeds unitally in an explicit simple ring finitely presented as a ring (over Z)
distinct_from:
  leavitt-resolvent-ring-is-fp-simple-of-char-zero: that is the case k = 0, with one register N and constants Q; this adds k central transcendentals and 2k+1 further registers, so the constants are Q(t_1..t_k).
  polynomially-representable-algebras-have-fp-simple-envelopes: that embeds polynomial and free K-algebras in finitely presented simple K-algebras over a field K; this is finite presentation as a ring over Z, and it contains the field Q(t_1..t_k), so every nonzero polynomial is inverted.
  char-zero-representable-rings-embed-in-fp-simple-rings: that is the consequence for all finitely generated fields of characteristic zero and all rings representable over them; this is the construction it rests on.
  countable-char-zero-fields-embed-in-fp-simple-rings: that asks for every countable field of characteristic zero; this settles the finitely generated purely transcendental ones.
---

**ESTABLISHED** through `rational-function-fields-embed-in-fp-simple-rings-proof`
(lane proof; refereed PASS by `gq-referee-a` (proof gaps, `gq-referee-a-rational-function-fields-embed-in-fp-simple-rings.md`, 69a3cc64f); `gq-referee-c` also checked the application of the completion criterion to `R_k` (`gq-referee-c-leavitt-nekrashevych-completion-simplicity-criterion.md`, 282b018d4) and `gq-referee-b` (citations and hypotheses, `gq-referee-b-rational-function-fields-embed-in-fp-simple-rings.md`, d7414d7a4; its report covers all four ring-envelope claims)). No priority is claimed beyond a bounded search.

**Known and credit.** Finitely presented simple *algebras over a field* of characteristic
zero are classical: the Weyl algebra `A_1(Q)`, the Leavitt algebras `L_Q(1,n)`, and
Nekrashevych algebras are finitely presented over `Q` and simple. The point here is finite
presentation *as a ring*, that is, as a `Z`-algebra, which forces all of `Q` to be generated
by finitely many elements. This is the characteristic-zero case of the algebra form of
Boone--Higman (`algebra-boone-higman-conjecture`, with finite presentation over `Z`) for
these inputs. No printed source asks this question, so it is not an answer to an open
problem. A bounded search (web and arXiv; no MathSciNet, zbMATH or Dniester Notebook;
`gq-gq-lit-arxiv-priority.md` §§6, 9) found no prior construction.

**Statement.** Fix `k >= 1` and write `F_k = Q(t_1, ..., t_k)`. There is a unital ring
`R_k`, given by an explicit finite presentation over `Z`, such that
1. `R_k` is simple;
2. `F_k` embeds in `R_k` as a unital central subfield;
3. the free algebra `F_k<x_1, ..., x_m>` embeds in `R_k` for every `m`.

**The presentation.** It has *registers* `P_1..P_k, M, C_1..C_k, N`, central generators
`t_1..t_k`, one resolvent `Γ`, and a Leavitt `(1,d)` family `s_x, t_x` indexed by
`d = 5k + 3` letters. Each letter `x` names a substitution `σ_x` of the registers, which
fixes the `t_j` and every register it does not mention:

| letter | substitution |
|---|---|
| `n` | `N ↦ N + 1` |
| `c_i^+`, `c_i^-` (1 <= i <= k) | `C_i ↦ C_i ± 1` |
| `m_j` (1 <= j <= k) | `M ↦ t_j M` |
| `r` | `M ↦ 1` |
| `p_i^+`, `p_i^-` (1 <= i <= k) | `P_i ↦ P_i ± M` |
| `v` (vacuum) | `P_i ↦ 0`, `C_i ↦ 0`, `N ↦ 0`, `M ↦ 1` |

Put `G = N + 1 + Σ_i (t_i − C_i) P_i`. The relations are:
- (L) `t_x s_y = δ_xy` and `Σ_x s_x t_x = 1`;
- (Z) the `t_j` and the registers commute pairwise, and each `t_j` commutes with every
  `s_x` and `t_x`;
- (Cov) `X s_x = s_x σ_x(X)` for every register `X` and every letter `x`, where `σ_x(X)`
  is the integer polynomial in the table;
- (Res) `Γ G = 1 = G Γ`.

That is `2d + 3k + 3` generators and finitely many relations. For `k = 1` it has 8 letters
and 22 generators.

**How it works.**
- **Values.** On a basis vector whose word begins `x_1 ... x_r v`, the registers take the
  values `σ_(x_1) ∘ ... ∘ σ_(x_r)` applied to the vacuum `(P, M, C, N) = (0, 1, 0, 0)`.
  These are all tuples with `P_i ∈ Z[t]`, `M` a monomial, `C_i ∈ Z` and `N ∈ Z_(>=0)`.
- **Never zero.** On such a tuple `G` takes the value `N + 1 + Σ (t_i − c_i) p_i`. It is
  never zero, because at `t = c` it equals `N + 1 >= 1`.
- **Every polynomial is a value.** Every nonzero `q ∈ Z[t]` has an integer point `c` with
  `q(c) ≠ 0`, and then `±q = |q(c)| + Σ (t_i − c_i) p_i` is a value of `G`. So the one
  resolvent `Γ`, transported along words and evaluated at the vacuum, inverts every
  nonzero polynomial.
- **Simplicity.** `R_k` is the Leavitt--Nekrashevych completion of the localization `B` of
  `Q[t, registers]` at the orbit of `G`. It is simple by
  `leavitt-nekrashevych-completion-simplicity-criterion`.

**Explicit model.** Let `X` be the infinite words over the `d` letters with infinitely
many `v`, and let `τ(ξ)` be the register tuple read from `ξ` as above. On `F_k^(X)`:
- `s_x` and `t_x` act by prepending and removing letters;
- `t_j` acts as the scalar `t_j`;
- each register `Y` acts diagonally by `Y(τ(ξ))`, and `Γ` by `1/G(τ(ξ))`.

This model is faithful on `B`, so `R_k ≠ 0` without the general embedding argument.
