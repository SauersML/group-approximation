---
rg: 2
id: persistent-automata-rn-group-fp-iff-group-fp-proof
kind: route
title: At a persistent letter every word is its own section, so lift-closure adds nothing and Theorem A reduces to finite presentability of G
target: persistent-automata-rn-group-fp-iff-group-fp
requires:
  - rover-nekrashevych-fp-iff-finite-lift-presentation
---

Notation and conventions are those of `rover-nekrashevych-fp-iff-finite-lift-presentation`:
`g(xw) = g(x) g|_x(w)`, `(gh)|_x = g|_{h(x)} h|_x`, and word-level sections are computed letter by letter.

## 1. Sections at a fixed letter

Suppose `s(i) = i` for every `s in S`. Then `s^{-1}(i) = i` and `s^{-1}|_i = (s|_{s^{-1}(i)})^{-1} = (s|_i)^{-1}`.
Put `θ(s) = s|_i`, as a letter of `S` (if `s|_i = 1`, read `θ(s)` as the empty word). For a word `w = u_1 ··· u_ℓ`,
every suffix of `w` fixes `i`, so

`w(i) = i` and `w|_i = u_1|_i ··· u_ℓ|_i = θ(w)`,

where `θ` is extended to an endomorphism of `F`. If `θ` permutes `S`, it is an automorphism of `F` of finite
order `m` dividing `|S|!`.

- **Persistent case:** `θ = id`, so `w|_i = w` for every word `w`.
- **Twisted case:** `θ` is a permutation of `S` and `w|_i = θ(w)`.

## 2. Lift-closure is vacuous

**Lemma.** In the twisted case, every normal subgroup `M ⊴ F` with `θ(M) = M` is a lift ideal.

*Proof.* `M` is normal. Let `w` have trivial root permutation and `w|_x in M` for all `x`. Then `θ(w) = w|_i in M`,
so `w in θ^{-1}(M) = M`. So `M` is lift-closed. ∎

Consequences, for any `R ⊆ F`:

- `M_R := ⟨⟨∪_{0 ≤ j < m} θ^j(R)⟩⟩` is normal and `θ`-invariant, hence a lift ideal containing `R`. So
  `⟨⟨R⟩⟩ ⊆ ⟨⟨R⟩⟩_lift ⊆ M_R`.
- In the persistent case `m = 1`, so `⟨⟨R⟩⟩_lift = ⟨⟨R⟩⟩`.
- `R = ∅` gives `K_∞ = ⟨⟨∅⟩⟩_lift ⊆ M_∅ = 1`.

This proves (1) and (2) of the claim.

## 3. The equivalence

Assume the twisted case (the persistent case is `θ = id`).

- **If `G` is finitely presented**, then `N = ⟨⟨R⟩⟩` for a finite `R`, because `S` is a finite generating set and
  finite presentability does not depend on the finite generating set. Then `N = ⟨⟨R⟩⟩ ⊆ ⟨⟨R⟩⟩_lift ⊆ N`, since `N`
  is a lift ideal ((1a) of the Theorem A route). So `N` is a finitely generated lift ideal, and `V_d(G)` is finitely
  presented by Theorem A. (This direction is also Scott's theorem, FP1.)
- **If `V_d(G)` is finitely presented**, Theorem A gives a finite `R ⊆ N` with `N = ⟨⟨R⟩⟩_lift`. Every `θ^j(r)` is
  the iterated section `r|_{i^j}`, and `N` is closed under sections, so `θ^j(R) ⊆ N`. By §2,
  `N = ⟨⟨R⟩⟩_lift ⊆ M_R ⊆ N`. So `N` is the normal closure of the finite set `∪_{j<m} θ^j(R)`, and `G = F/N` is
  finitely presented.

This proves (3). ∎

## 4. Two actions of `Z/2 ≀ Z` on the same tree

Let `a = σ(a, b)`, `b = (a, b)` over `{0, 1}` be the lamplighter automaton, with relator kernel `N_2 ⊆ F(a, b)`
and `N_2 = K_∞` (`rover-nekrashevych-group-of-lamplighter-automaton-is-fp`).

**(4a) The squared action.** Read `{0,1}^*` as `({0,1}^2)^*`. The same `S = {a, b}^{±1}` is closed under sections at
two-letter words, so this is a finite-state self-similar action on the 4-regular tree, with the same kernel `N_2`.
Its `K_∞` (for the alphabet `{0,1}^2`) contains the `K_∞` for `{0,1}`. Indeed, if `w` has trivial permutation on
`{0,1}^n` and freely trivial sections there, the same holds at every level `n' ≥ n`, in particular at an even one.
So it is again all of `N_2`, and `V_4` of this action is finitely presented by Theorem A.

**(4b) The persistent extension.** Over `X = {0,1,2,3}` put `a' = σ(a', b', a', a')` and `b' = (a', b', b', b')`,
with `σ = (0 1)`. Then `S' = {a', b'}^{±1}` is persistent at `2` (and at `3`).

- **Same kernel.** Identify `F(a', b')` with `F(a, b)`. The subtree `{0,1}^*` is invariant, and restricting to it
  gives the lamplighter action. So `N_4 ⊆ N_2`.
- Conversely, let `w in N_2`. We show by induction on `n` that every `w in N_2` fixes `X^n` pointwise.
  - `w` fixes `0` and `1` (trivial root permutation on `{0,1}`), and `2` and `3` (fixed by all of `S'`).
  - For `x in {0,1}`, the word-level section `w|_x` is the same word in both automata, and it lies in `N_2`.
    For `x in {2,3}`, `w|_x = w in N_2` by §1.
  - So `w(xv) = x · w|_x(v) = xv` by induction.
  - Hence `N_4 = N_2`, and the group is `Z/2 ≀ Z` again.
- By §2, `K_∞ = 1` for this action, and by §3 `V_4` is finitely presented iff `Z/2 ≀ Z` is. It is not (Baumslag:
  `A ≀ Z` with `A ≠ 1` is never finitely presented).

The three-letter extension `a' = σ(a', b', a')`, `b' = (a', b', b')` is handled by the same argument, giving `V_3`
not finitely presented. The lamplighter's own `V_2` is finitely presented by Theorem B.

## 5. Machine check

`experiments/affine-lamplighter-rn-2026-09-17/afflamp.py p a K --persist` builds the persistent extension of the
affine lamplighter automaton of `rn-groups-of-affine-lamplighters-f-q-wr-z-are-fp`. For `p = 2, a = 1`, that
automaton is the lamplighter, up to relabelling letters by `x ↦ 1 - x`. The script tests the relators `τ^p` and
`[τ, A^k τ A^{-k}]`.

- Runs `2 1 4 --persist` and `3 2 3 --persist`: every relator is `in N: True`, `in K_inf: False`, as §2 predicts.
- Without `--persist`, the same relators are all in `K_∞` (see `results.txt`).
