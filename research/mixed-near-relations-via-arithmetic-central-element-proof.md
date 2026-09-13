---
rg: 2
id: mixed-near-relations-via-arithmetic-central-element-proof
kind: route
title: Split the input into cosets of the central element and reuse the residue-affine orbit enumeration
target: central-cyclic-inputs-have-computable-mixed-near-relations
requires:
  - route-form-shell-inputs-have-computable-mixed-near-relations
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
  - deligne-lattice-embeds-in-no-rover-nekrashevych-group
artifacts:
  - research/artifacts/solve-deligne-shell-singfix-2026-09-13.md
---

Use the notation of the target.

## 1. The enumeration

- **A model enumeration.** Apply `route-form-shell-inputs-have-computable-mixed-near-relations`
  to the input `Z x <t_0>`, with `t_0` of infinite order. Its item 1 gives a
  bijection `nu_0 : Z x <t_0> -> N` with `lambda_(t_0) = lambda'`. Its item 3
  makes `nu_0` and `nu_0^-1` computable, since `Z` has decidable word problem.
- **Cosets.** Let `T` be a transversal of `<t>` in `P`. It is countably infinite,
  because `|P : <t>|` is infinite. Choose a bijection `beta : T -> Z`.
- **The bijection.** Since `t` has infinite order, every `g` in `P` is uniquely
  `x t^k` with `x` in `T` and `k` in `Z`. Put `nu(x t^k) = nu_0(beta(x), t_0^k)`.
  This is a bijection `P -> N`.
- **The central element acts by `lambda'`.** Since `t` is central,
  `t x t^k = x t^(k+1)`. So

      lambda_t(nu(x t^k)) = nu(x t^(k+1))
                          = nu_0(beta(x), t_0^(k+1))
                          = lambda_(t_0)(nu_0(beta(x), t_0^k))
                          = lambda'(nu(x t^k)).

  Hence `lambda_t = lambda'`. This is item 1.

## 2. The relation

- **The identity.** Item 2 of the cited claim holds for the enumeration `nu_0`,
  where `lambda_(t_0) = lambda'`. So it is an identity about the permutation
  `lambda'` alone: `[lambda' s^4 lambda'^-1, s^8] = 1` in `NearSym(N)`. With
  `lambda_t = lambda'` it reads `[lambda_t s^4 lambda_t^-1, s^8] = 1` in `R_nu`.
- **A reduced word.** The word `t s^4 t^-1 s^8 t s^-4 t^-1 s^-8` alternates
  between nontrivial elements of `P` and of `<s>`, since `t != 1`. So it is reduced
  and nonidentity in `P*<s>`, and `R_nu != P*<s>`.
- **The obstruction does not apply.** `free-shift-shell-envelopes-are-not-finitely-presented`
  requires `R_nu = P*<s>`. This is item 2.

## 3. Computability

Assume `P` is finitely generated, has decidable word problem, and membership in
`<t>` is decidable.

- **The transversal.**
  - List the words `w_0, w_1, ...` in the generators.
  - Keep `w_i` when `w_j^-1 w_i` is not in `<t>` for every earlier kept `w_j`.
  - The kept words list a transversal `T` without repetition. Every coset appears,
    since every element is a word.
  - Let `beta` send the `m`-th kept word to the `m`-th integer in a fixed
    computable listing of `Z`.
- **Computing `nu`.**
  - Given a word `g = w_i`, find the kept word `x` with `x^-1 g` in `<t>`. It has
    index at most `i`: either `w_i` was kept, or it was discarded because of an
    earlier kept word. So the search terminates.
  - Find `k` with `x^-1 g = t^k` by testing `k = 0, 1, -1, 2, -2, ...` with the
    word problem. Some `k` works, so this also terminates.
  - Output `nu_0(beta(x), t_0^k)`.
- **Computing `nu^-1`.** Compute `nu_0^-1(n) = (m, t_0^k)`, and output the word
  `x t^k`, where `x` is the kept word with `beta(x) = m`.

This is item 3.

## 4. Deligne's lattice

- **Decidable word problem.** `Gamma~` is finitely presented and has decidable
  word problem, by item 1 of `deligne-lattice-embeds-in-no-rover-nekrashevych-group`.
- **The central element.** The generator `z` of `ker p` is central of infinite
  order, and `Gamma~/<z>` is `Sp_4(Z)`, which is infinite
  (`deligne-universal-cover-lattice-is-non-rf-kazhdan`, item 1).
- **Membership in `<z>`.** A word lies in `<z>` exactly when its image in
  `Sp_4(Z)`, a product of fixed integer matrices, is the identity. This is the
  first step of the word-problem algorithm in
  `deligne-lattice-embeds-in-no-rover-nekrashevych-group-proof`.

So items 1--3 hold for `P = Gamma~` and `t = z`.
