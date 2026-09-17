---
rg: 2
id: plane-constant-minimal-sft-factors-are-effective-minimal-proof
kind: route
title: Local rule, pull back invariant sets through the plane-invariant map, then two compactness searches over locally admissible ball patterns
target: plane-constant-minimal-sft-factors-are-effective-minimal
requires: []
---

**Route. COMPLETE.** This is a self-contained hand proof in the setting of the
target.

**Notation.**
- Fix a finite symmetric generating set of `Λ = Λ_0 x Z^2`. `B(n)` is the word
  ball of radius `n` in `Λ`, and `|g|` is word length.
- `Λ` has solvable word problem, since a word splits into its `Λ_0` part and
  its `Z^2` part. So `B(n)` is computable as a finite list of distinct elements,
  with membership and products of listed elements decidable.
- `X` is the set of `x ∈ A^Λ` avoiding a finite list `ℱ` of forbidden patterns,
  each on a shape inside `B(r)`.
- The algorithms below use finitely many fixed data: `ℱ`, `W`, `φ`, and
  generators. The theorem asserts only that algorithms exist.

**Step 1: local rule.** `x ↦ Φ(x)(1)` is continuous from `X` into the finite
discrete set `B`. By compactness it factors through `x|_W` for some finite
`W ⊆ Λ`, say `W ⊆ B(w)`. Let `φ : A^W -> B` be the induced map, extended
arbitrarily to patterns that are not restrictions of points of `X`. For
`μ ∈ Λ_0` and `x ∈ X`, equivariance gives

```text
Φ(x)(μ) = (μ·Φ(x))(1) = Φ((μ,0)·x)(1) = φ( v ↦ x(v(μ,0)) ),  v ∈ W.
```

So `Φ(x)(μ)` depends only on `x` on `W(μ,0) ⊆ B(w + |μ|)`.

**Step 2: `Y` is a nonempty subshift.**
- `Y = Φ(X)` is compact, hence closed.
- It is nonempty.
- It is `Λ_0`-invariant, since `λ·Φ(x) = Φ((λ,0)·x)`.

**Step 3: `Y` is minimal.** Let `∅ ≠ Z ⊆ Y` be closed and `Λ_0`-invariant, and
put `P = X ∩ Φ^{-1}(Z)`.
- `P` is closed and nonempty.
- `P` is `Λ`-invariant: for `x ∈ P`,
  `Φ((λ,z)·x) = Φ((1,z)·((λ,0)·x)) = Φ((λ,0)·x) = λ·Φ(x) ∈ Z`, using that
  `(λ,z) = (1,z)(λ,0)`, the action rule and plane invariance.
- Minimality of `X` gives `P = X`, so `Z = Y`.

**Step 4: locally admissible patterns and König.** For `n ≥ r`, let `L_n` be
the set of `q ∈ A^{B(n)}` containing no occurrence of a pattern of `ℱ` whose
translated shape lies inside `B(n)`.
- `L_n` is finite and computable.
- `x|_{B(n)} ∈ L_n` for every `x ∈ X`.
- **(K)** Let `L'_n ⊆ L_n` for `n ≥ n_0`, each nonempty, with
  `q|_{B(n)} ∈ L'_n` whenever `q ∈ L'_{n+1}`. Then some `x ∈ X` has
  `x|_{B(n)} ∈ L'_n` for all `n ≥ n_0`.
  - The union of the `L'_n`, ordered by restriction, is an infinite finitely
    branching tree, so it has an infinite branch.
  - The branch defines `x ∈ A^Λ`. Every occurrence of a pattern of `ℱ` lies in
    some `B(n)`, and there is none, so `x ∈ X`.

**Step 5: reading a factor pattern from a ball pattern.** Let `F ⊆ Λ_0` be
finite, given as words. Let `m(F)` be a computable `m` with `W(μ,0) ⊆ B(m)` for
all `μ ∈ F`; `m = w + max_{μ∈F} |μ|` works. For `n ≥ m(F)` and `q ∈ A^{B(n)}`,
set

```text
Φ_F(q)(μ) = φ( v ↦ q(v(μ,0)) ),  μ ∈ F.
```

- This is computable.
- It depends only on `q|_{B(m(F))}`.
- `Φ_F(x|_{B(n)}) = Φ(x)|_F` for `x ∈ X`, by Step 1.

**Step 6: non-occurrence in `Y` is r.e.** A pattern `p ∈ B^F` occurs in `Y`
when some `y ∈ Y` has `y|_F = p`. Translates need no separate treatment:
patterns on `Fλ` are handled by `Λ_0`-invariance of `Y`.

*Claim:* `p` does not occur in `Y` iff there is `n ≥ m(F)` such that no
`q ∈ L_n` has `Φ_F(q) = p`.
- *(⇐)* If `x ∈ X` has `Φ(x)|_F = p`, then for every `n`, `q = x|_{B(n)} ∈ L_n`
  and `Φ_F(q) = p`, by Step 5.
- *(⇒)* Suppose that for every `n ≥ m(F)` some `q ∈ L_n` has `Φ_F(q) = p`. Put
  `L'_n = { q ∈ L_n : Φ_F(q) = p }`.
  - The sets are nonempty.
  - They are closed under restriction, because restriction preserves local
    admissibility and `Φ_F` depends only on the ball of radius `m(F)`.
  - (K) gives `x ∈ X` with `Φ_F(x|_{B(m(F))}) = p`, that is `Φ(x)|_F = p` by
    Step 5. So `p` occurs.

Searching over `n` enumerates the non-occurring patterns. So `Y` is
effectively closed, with the r.e. forbidden set consisting of these patterns.

**Step 7: occurrence in `Y` is r.e., using minimality.** Let `F_0(R) = B_{Λ_0}(R)`
be the word ball of `Λ_0`.

*Claim:* `p ∈ B^F` occurs in `Y` iff there are `R` and `n ≥ m(F·F_0(R))` such
that every `q ∈ L_n` shows `p` at some `λ ∈ F_0(R)`. Here "`q` shows `p` at
`λ`" means `Φ_{Fλ}(q)(μλ) = p(μ)` for all `μ ∈ F`.
- *(⇐)* Since `X ≠ ∅`, pick `x ∈ X`. Then `x|_{B(n)}` shows `p` at some `λ`.
  By Step 5, `Φ(x)(μλ) = p(μ)` for `μ ∈ F`. So `λ·Φ(x) ∈ Y` has `p` on `F`.
- *(⇒)* Suppose `p` occurs in `Y`.
  - The cylinder `U = {y ∈ Y : y|_F = p}` is nonempty and open in `Y`.
  - By Step 3, every `y ∈ Y` has dense orbit, so some `λ` has `λ·y ∈ U`, that
    is `y(μλ) = p(μ)` for `μ ∈ F`.
  - The open sets `V_R = { x ∈ X : Φ(x) shows p at some λ ∈ F_0(R) }` therefore
    cover `X`. By compactness some `V_R = X`.
  - Now suppose that for every `n` some `q ∈ L_n` fails to show `p` anywhere on
    `F_0(R)`. These sets are closed under restriction for
    `n ≥ m(F·F_0(R))`, because showing depends only on `B(m(F·F_0(R)))`.
  - (K) then gives `x ∈ X` not in `V_R`, a contradiction.

Searching over `(R, n)` enumerates the occurring patterns. With Step 6, the
language of `Y` is decidable.

**Step 8: corollary.**
- If `Λ_0` is infinite and finitely presented and acts freely on `Y`, then
  Steps 2, 3 and 6 say that `Y` is a nonempty, effectively closed, minimal,
  free `Λ_0`-subshift.
- That is exactly the conclusion of
  `decidable-fp-groups-have-effective-minimal-free-subshifts` for `Λ_0`.
- Solvable word problem of `Λ_0` was assumed; finite presentability is only
  carried along.
