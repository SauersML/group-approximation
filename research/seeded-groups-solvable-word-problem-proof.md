---
rg: 2
id: seeded-groups-solvable-word-problem-proof
kind: route
title: Lift the seed to the free group, where it is the unique member of an effectively closed class; a Π^0_1 singleton is computable, and trivial stabilizer turns the word problem into one evaluation of it
target: seeded-recursively-presented-groups-have-solvable-word-problem
requires: []
---

Notation is that of the target. `F` is the free group on `S` and `π : F -> Γ` the quotient map. `N = ker π` is
recursively enumerable, since `R` is. `B_m^F` is the ball of radius `m` in `F`. The data of part 3 fix the finitely
many words of length `≤ 2 max(r, R_0)` that are trivial in `Γ`, so a Γ-pattern on a ball can be written on words.

## 1. The lifted class

Let `X̃ ⊆ A^F` be the set of `x̃` with three properties:
- (i) `x̃(u) = x̃(un)` for all `u ∈ F` and `n ∈ N`;
- (ii) for every `u ∈ F` and every forbidden pattern `φ` on `B_ρ` (any radius `ρ`), the pattern `f ↦ x̃(uf)`,
  read on words of length `≤ ρ`, is not `φ`;
- (iii) `x̃(f) = p(π f)` for all words `f` of length `≤ R_0`.

By (i), the pattern in (ii) is a well-defined Γ-pattern, since two words of length `≤ ρ` with the same image differ
by an element of `N`.

**`X̃` is effectively closed.** Each instance of (i), (ii) and (iii) is a clopen condition on finitely many
coordinates. The instances of (i) are enumerated from an enumeration of `N`, those of (ii) from an enumeration of
the forbidden patterns, and (iii) is finite.

**`X̃ = {y_* ∘ π}`.**
- If `x̃ ∈ X̃`, then (i) gives `x̃ = x ∘ π` for a unique `x ∈ A^Γ`. Here `N` is normal, so right and left cosets
  agree.
- (ii) says that `x` avoids every forbidden pattern, so `x ∈ Y`.
- (iii) says `x|_(B_(R_0)) = p`. By (S1), `x = y_*`.
- Conversely `y_* ∘ π` satisfies (i)–(iii).

## 2. A Π^0_1 singleton is computable

Fix an enumeration of the instances of (i)–(iii). For `n ≥ 0` let `𝒜_n` be the finite set of maps
`a : B_n^F -> A` that violate none of the first `n` instances lying entirely inside `B_n^F`.
- Restriction maps `𝒜_(n+1)` into `𝒜_n`, and `(y_* ∘ π)|_(B_n^F) ∈ 𝒜_n` for all `n`.

**To compute `y_*(ū)` for a word `u`.** Search for `n ≥ |u|` such that all members of `𝒜_n` take the same value
at `u`, and output that value.
- **Correctness.** The output agrees with the member `y_* ∘ π` of `𝒜_n`.
- **Termination.** Suppose instead that for every `n` two members of `𝒜_n` disagree at `u`.
  - Some value `b ≠ y_*(ū)` is then taken at `u` by members of `𝒜_n` for infinitely many `n`, and hence for all
    `n`, since restrictions of members are members.
  - By König's lemma, the finitely branching tree of these members has an infinite branch `x̃`, a map `F -> A`
    with `x̃(u) = b`.
  - Every instance of (i)–(iii) lies inside some `B_n^F` and among the first `n` instances for large `n`, so `x̃`
    violates none. So `x̃ ∈ X̃`, and `x̃ ≠ y_* ∘ π`, a contradiction with Section 1.

This proves part 1. The procedure uses only the data listed in part 3, so it is uniform.

## 3. The word problem

Let `w` be a word and `g = π(w)`.
- `g.y_*` lies in `Y`, and `(g.y_*)(f) = y_*(g^(-1) f)`.
- By (S1), `g.y_* = y_*` iff `(g.y_*)|_(B_(R_0)) = p`. By (S2), `g.y_* = y_*` iff `g = 1`.
- So `w =_Γ 1` iff `y_*(π(w^(-1) f̂)) = p(π f̂)` for every word `f̂` of length `≤ R_0`.

That is finitely many evaluations of part 1, which proves part 2.

**Certificates.**
- `w = 1` is certified by finding `w` in the enumeration of `N`.
- `w ≠ 1` is certified by a stage `n` at which every member of `𝒜_n` differs from `p` at some `w^(-1) f̂`.

## 4. Decidable language under (C2)

Let `α` be a Γ-pattern on a ball `B_ρ`, written on words.
- **`α ∈ L(Y)` is recursively enumerable.** By (C2), `α ∈ L(Y)` iff `α` occurs in `y_*`, that is,
  `y_*(π(v f̂)) = α(π f̂)` for all `f̂`, for some word `v`. Search over `v`, using part 1.
- **`α ∉ L(Y)` is recursively enumerable.** By part 2, the balls of `Γ` can be computed.
  - `α ∉ L(Y)` iff for some `m`, every map `B_m -> A` extending `α` on `B_ρ` contains, somewhere inside `B_m`,
    a translate of one of the first `m` forbidden patterns (compactness).
  - That is a finite check for each `m`.

So `L(Y)` is decidable. `∎`

**Where each hypothesis enters.**
- Recursive enumerability of `R` and of the forbidden patterns: `X̃` is effectively closed.
- (S1): `X̃` is a singleton.
- (S2): the word problem is read off one evaluation.
- (C2): only in Section 4.
