---
rg: 2
id: fp-central-simple-host-with-nonzero-leavitt-k1-proof
kind: route
title: Extend the boundary Leavitt path algebra by the letterwise involution c_2 -> c_2^(-1); the fixed boundary point c_1^∞ gives a trace nonzero on the square-zero element 1 + u_σ
target: fp-central-simple-host-with-nonzero-leavitt-k1
requires:
  - boundary-crossed-product-is-a-leavitt-path-algebra
  - free-minimal-cantor-crossed-products-are-central-simple
  - crossed-product-fixed-point-traces-detect-leavitt-k1
  - leavitt-tensor-k1-sees-traces-of-nilpotent-matrices
---

Notation as in the target. Letters are `c_1^(±1), c_2^(±1)`. `C(w)` is the
cylinder of infinite reduced words beginning with the reduced word `w`. A word
`x ∈ ∂N` is *admissible after `w`* if its first letter is not `w_last^(-1)`, so
`wx` is reduced. There are 3 admissible first letters.

**Step 0 (it is an action).** `α` sends letters to letters and satisfies
`α(a^(-1)) = α(a)^(-1)`. So it commutes with free reduction and maps reduced
words to reduced words of the same length. Hence
`σ · (n · (σ · ξ)) = α(red(n α(ξ))) = red(α(n) ξ) = α(n) · ξ`. The `N`-action and
the involution `σ` therefore define an action of `Γ = N ⋊ <σ>` by
homeomorphisms of the Cantor set `∂N`.

**Step 1 (finite presentation).** Let `A = LC(∂N, F_2) ⋊ N ⊂ B`. By
`boundary-crossed-product-is-a-leavitt-path-algebra` (d = 2),
`A ≅ L_(F_2)(E_2)`, the Leavitt path algebra of a finite graph. So `A = <S | R>`
with `S` and `R` finite. Conjugation by `u_σ` preserves `A`:

- `u_σ P_U u_σ^(-1) = P_(α(U))`, and `α(C(w)) = C(α(w))`;
- `u_σ u_n u_σ^(-1) = u_(α(n))`.

Call the restriction `α̃ ∈ Aut(A)`. For each `s ∈ S` fix a noncommutative
polynomial `p_s` in `S` representing `α̃(s)`. Let `C` be the algebra with
generators `S ∪ {t}` and relations `R`, `t^2 = 1` and `t s t = p_s` for `s ∈ S`.
This is a finite presentation.

- *Surjection.* `s ↦ s`, `t ↦ u_σ` respects the relations, so it defines
  `π : C -> B`. Every `γ ∈ Γ` is `n` or `nσ`, so `B = A + A u_σ`, and `π` is onto.
- *Spanning.* Let `φ : A -> C` be induced by `S ⊂ C`. The set
  `D = {y ∈ A : t φ(y) t = φ(α̃ y)}` contains `1` and `S`. It is closed under
  products because `t^2 = 1`, so `D = A`. Hence `t φ(y) = φ(α̃ y) t`, and
  `φ(A) + φ(A) t` is a subalgebra containing the generators. It equals `C`.
- *Injectivity.* `B = ⊕_γ LC(∂N) u_γ` and `N`, `Nσ` are disjoint cosets. So
  `B = A ⊕ A u_σ`, and `π(φ(a) + φ(a') t) = a + a' u_σ` vanishes only if
  `a = a' = 0`.

So `π` is an isomorphism, and `B` is finitely presented.

**Step 2 (topological freeness).** Cylinders form a basis, and every cylinder
contains longer ones. So it suffices to show that no `γ ≠ e` fixes a cylinder
`C(w)` pointwise with `|w| > |n|`, where `γ = n` or `γ = nσ`.

Let `w' = w` if `γ = n`, and `w' = α(w)` if `γ = nσ`, so `|w'| = |w|`. Reducing
`n w'` cancels at most `|n| < |w'|` letters of `w'`. So `m = red(n w')` ends with
the last letter of `w'`, and for `x` admissible after `w` (equivalently,
`α(x)` admissible after `α(w)`),

- `γ · (w x) = m x` if `γ = n`;
- `γ · (w x) = m α(x)` if `γ = nσ`.

Both are reduced. Suppose `γ` fixes `C(w)` pointwise, so this equals `w x` for
every admissible `x`.

- *If `|m| ≠ |w|`.* Compare the letter in position `min(|m|, |w|) + 1`. It forces
  the first letter of `x` (or of `α(x)`, and `α` is injective on letters) to be
  one fixed letter. But there are 3 admissible first letters. Contradiction.
- *If `|m| = |w|` and `γ = n`.* Then `m = w`, so `n w = w` in `N` and `n = e`.
  Contradiction.
- *If `|m| = |w|` and `γ = nσ`.* Then `m = w` and `α(x) = x` for all admissible
  `x`. At most one letter is excluded, so some admissible `x` begins with
  `c_2^(±1)`. Since `α(c_2^(±1)) = c_2^(∓1)`, this `x` is not fixed.
  Contradiction.

**Step 3 (minimality).** Let `ξ ∈ ∂N` and `w` a nonempty reduced word. Choose a
letter `y ∉ {w_last^(-1), ξ_1^(-1)}`; there are 4 letters, so one exists. Then
`w y ξ` is reduced, and `(wy) · ξ = w y ξ ∈ C(w)`. Every orbit meets every
cylinder, so every orbit is dense.

**Step 4 (central simplicity and the group algebra).** `Γ` is countable and
`∂N` is compact, Hausdorff and zero-dimensional. The action is minimal (Step 3)
and topologically free (Step 2), so
`free-minimal-cantor-crossed-products-are-central-simple` gives that `B` is
simple and `Z(B) = F_2`. The `u_γ` are linearly independent, since
`B = ⊕_γ LC(∂N) u_γ` and `u_γ = 1 · u_γ`. Also `u_γ u_δ = u_(γδ)` and
`u_e = 1`, so `γ ↦ u_γ` is a unital embedding `F_2[Γ] -> B`.

**Step 5 (the fixed-point trace).** `σ` has order `2 = char F_2`, and fixes
`ξ_0 = c_1 c_1 c_1 ... = c_1^∞`.

- *Centralizer.* `n σ^ε` commutes with `σ` iff `α(n) = n`. A reduced word
  `a_1 ... a_r` is fixed by the letterwise `α` iff every `a_i ∈ {c_1^(±1)}`. So
  `C_Γ(σ) = <c_1> × <σ>`.
- *Invariance.* Both `c_1` and `σ` fix `ξ_0`. So `S = {ξ_0} ⊂ Fix(σ)` is
  `C_Γ(σ)`-invariant, with `|S| = 1` odd.

Apply the easiest instance of (F) in `crossed-product-fixed-point-traces-detect-leavitt-k1`
with `ν = δ_(ξ_0)`. Explicitly, the trace is
`τ(f u_γ) = f(k ξ_0)` if `γ = k σ k^(-1)`, and `0` otherwise.

Then `x = 1 - u_σ = 1 + u_σ` satisfies `x^2 = 1 + u_σ^2 = 0`, and
`τ(x) = 1 ≠ 0` in `F_2`. By
`leavitt-tensor-k1-sees-traces-of-nilpotent-matrices` with `m = 1`, `n = 1`,
`χ_(τ,1)[1 + x ⊗ e_1] = 1 ≠ 0`. Hence `K_1(B ⊗ L) ≠ 0`. ∎

**Robustness remark (not part of the claim).** Steps 0–5 use only the
following: `char k = 2`; `α` is an involution of `F_d` (`d >= 2`) that permutes
the letters with `α(a^(-1)) = α(a)^(-1)`; `α` fixes some letter `a_0`; and `α`
moves at least 2 letters. The last condition leaves an admissible moved first
letter in Step 2. Then `a_0^∞` plays the role of `ξ_0`, provided its stabilizer
contains `C(σ)`, which must be checked for each `α`.
