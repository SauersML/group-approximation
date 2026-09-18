---
rg: 2
id: perron-substitution-finiteness-proof
kind: route
title: Proof that the Perron substitution condition yields Li F_n finiteness, by substituting a Perron-weighted height function for Li's diagonal condition (t<d)
target: perron-substitution-finiteness-for-garside-full-groups
requires:
  - perron-substitution-finiteness-for-garside-full-groups
---

**Lane proof, not independently reviewed.** Li's proof of `thm:Fn`
(arXiv:2110.04505v2) is used as a black box **except** at the one lemma where `(t<d)`
enters, which is replaced. All section/lemma labels below are Li's, read at source in
`$GQ/src/kep/li-garside-II-2110.04505v2.tex`.

## 1. Exactly where (t<d) is used in Li

In Li's proof of `thm:Fn` the condition `(t<d)` appears in a single place: the lemma
immediately after `thm:Wit` ("`ρ` is a height function; for all `R`,
`#{x : ρ(x) ≤ R} < ∞`"). There the sentence *"condition (t<d) implies that
`ρ'(x) < ρ'(𝐝(α))`"* is the only use. Everything downstream — the Morse function `h` on
`E(x)`, the descending-link splitting into up-link and down-link, and
Lemmas `lem:link:n-conn_1/2/3`, `cor:link:n-conn`, `lem:Stab` — uses `ρ` **only** through
two properties:
- (H1) `ρ` is a height function: `ρ(x) = ρ(y)` when `ℭ*(x,y) ≠ ∅`, and `ρ(x) < ρ(y)`
  when `ℭ(x,y) ≠ ∅` but `ℭ*(x,y) = ∅`;
- (H2) finite sublevels `#{x ∈ 𝐗(*) : ρ(x) ≤ R} < ∞`, together with the consequence used
  in `lem:link:n-conn_3` that `ρ'(x_p) → ∞` forces some multiplicity
  `𝐦_{ξ_{p,l}}(U) → ∞`.

We supply a function `ρ_w` with (H1) and (H2) from **(Perron)** and substitute it for
Li's `ρ`; his topology arguments then run unchanged.

## 2. The Perron weight and the height function

By **(Perron)**, `M` is primitive with Perron eigenvalue `λ > 1`. Perron--Frobenius
gives a strictly positive **left** eigenvector `w ∈ ℝ^𝔗_{>0}`, `w M = λ w`, i.e.
`Σ_{τ'} w_{τ'} M[τ', τ] = λ w_τ` for every type `τ`.

For `𝐔 = (U_i)_{i∈I} ∈ 𝐗(*)` set the multiplicity `𝐦_𝐔(τ) = #{i : U_i = τ}` and

  `ρ_w(𝐔) := ⟨w, 𝐦_𝐔⟩ = Σ_{i∈I} w_{type(U_i)}`.

For `x ∈ 𝐗(*)` set `ρ_w(x) := max{ ρ_w(𝐔) : 𝐔 ∈ 𝐗(*), ℭ*(x,𝐔) ≠ ∅ }`, exactly mirroring
Li's `ρ(x) = max{ρ'(𝐔) : ℭ*(x,𝐔)≠∅}`.

## 3. (H1): ρ_w is a height function

*Unit invariance.* If `ℭ*(x,y) ≠ ∅` then `x` and `y` have equal `max`, so `ρ_w(x)=ρ_w(y)`,
by the definition as a max over the `=*`-class, identical to Li's argument for `ρ`.

*Strict increase.* Let `ℭ(x,y) ≠ ∅`, `ℭ*(x,y) = ∅`. As in Li we may assume
`ρ_w(x) = ρ_w(𝐦_x)` and pick `α ∈ ⟨𝚪⟩` and a unit `u` with `x = 𝐭(αu)`, `y = 𝐝(αu)`,
`α ∈ 𝚪` a single generator. `α` is one of Li's expansions `γ(𝔢, 𝔰)`; its effect on the
multiplicity vector is: it removes the expanded cylinders and inserts their one-step
pieces. Writing the expanded types as a sub-multiset `J`, we have
`𝐦_y = 𝐦_x − Σ_{τ∈J} e_τ + Σ_{τ∈J} M[·,τ]` (each expanded `τ`-cylinder replaced by its
`M[·,τ]` children; the leftover is empty because `X ⊆ Ω_∞`, and partial expansions
`γ(𝔢,𝔰)` expand a nonempty sub-multiset since `α` is not a unit). Hence

  `ρ_w(y) − ρ_w(x) = Σ_{τ∈J} ( ⟨w, M[·,τ]⟩ − w_τ ) = Σ_{τ∈J} (λ − 1) w_τ ≥ (λ−1) w_min · |J| > 0`,

using `⟨w, M[·,τ]⟩ = Σ_{τ'} w_{τ'} M[τ',τ] = λ w_τ`. So `ρ_w(𝐦_x) < ρ_w(𝐦_y) ≤ ρ_w(y)`,
and by unit invariance `ρ_w(x) < ρ_w(y)`. This is Li's height-function lemma with
`(t<d)` replaced by **(Perron)**; the constant `(λ−1)w_min > 0` plays the role Li's
`+1` played.

## 4. (H2): finite sublevels

Each generator increases `ρ_w` by at least `δ := (λ−1) w_min > 0`. So if `x = 𝐝(αu)`
with `α` a product of `ℓ_Γ(α)` generators, then `ρ_w(x) ≥ δ · ℓ_Γ(α)`, hence
`ρ_w(x) ≤ R ⟹ ℓ_Γ(α) ≤ R/δ`. As in Li's lemma, for each bounded factor length there are
finitely many `𝐝(αu)` because `𝐭(α) = *`, `#𝔠⁰ < ∞`, and `𝔖` locally finite gives
finitely many `𝔢, 𝔰 ⊆ 𝔳𝔖`. So `#{x : ρ_w(x) ≤ R} < ∞`. Moreover `ρ_w(x_p) → ∞` forces
`Σ_τ 𝐦_{x_p}(τ) ≥ ρ_w(x_p)/w_max → ∞`, so some type's multiplicity blows up: this is
precisely the input `lem:link:n-conn_3` extracts from `ρ'(x_p) → ∞` (Li uses that a
subsequence makes `𝐦_{ξ_{p,l}}(U)` strictly increasing; the pigeonhole needs only that
the total, hence some coordinate, is unbounded).

## 5. Conclusion

Substituting `ρ_w` for `ρ` in Li's proof of `thm:Fn`: `lem:Stab` is unchanged (it uses
(F) only); `cor:link:n-conn` and `prop:link:n-conn` are unchanged (they quote `ρ` only
via (H1),(H2)); the Morse function `h` and Lemmas `lem:link:n-conn_1/2/3` are unchanged
(they use `ρ` only through (H1),(H2)). Hence `|E(x)|` is `(n−1)`-connected for
`ρ_w(x) ≥ R`, and by `thm:Wit`, `𝒬(*,*)` is of type `F_n` whenever the `𝔠*(𝔳,𝔳)` are.
The second (topological-full-group) statement follows as in Li via
`lem:QbfC=bmF`, `lem:QbfCYY=QbfCYvYv`, `prop:GarsideTFG`. ∎

## Trust surface

- Li's descending-link connectivity machinery (`s:Fn`) is used verbatim, with `ρ`
  replaced by `ρ_w`; the replacement is legitimate because §1 pins the *sole* use of
  `(t<d)` to the height-function lemma, and §§3–4 re-establish (H1),(H2) for `ρ_w`.
- Perron--Frobenius (a positive left eigenvector for a primitive nonnegative matrix) is
  standard and recalled, not re-derived.
- The identity `𝐦_y = 𝐦_x − Σ e_τ + Σ M[·,τ]` uses Li's `lem:gamma`(i) that a full
  expansion's codomain is the disjoint family of children; the empty-leftover step uses
  `X ⊆ Ω_∞` (Li, same lemma (iii)).
