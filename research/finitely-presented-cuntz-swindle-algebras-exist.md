---
rg: 2
id: finitely-presented-cuntz-swindle-algebras-exist
kind: claim
title: Over every field there is a nonzero finitely presented algebra carrying a Cuntz swindle, the universal one whose swindle endomorphism satisfies sigma^2 = Ad(u) sigma for a unit u, so the swindle factor of the central-simple host route is reduced to simplicity and centre of a quotient
distinct_from:
  leavitt-nekrashevych-completion-embeds-and-is-fp: that makes completions O_psi(B) finitely presented through one covariance relator per generator; this makes a swindle algebra finitely presented through a Brin--Thompson style closure of an endomorphism under sigma^2 = Ad(u) sigma, and needs no matrix recursion.
  noninjective-ln-completions-have-self-similar-bases: that is the finite-presentation machine for self-similar completions; the swindle endomorphism here has recursion psi(sigma(a)) = diag(a, sigma(a)), which does not stay inside a degree-zero base, so that machine does not apply directly.
---

**ESTABLISHED** through `finitely-presented-cuntz-swindle-algebras-exist-proof` (lane proof,
bh-algebra, elementary, not reviewed).

**Definitions.** A *Cuntz swindle structure* on a unital `K`-algebra `A` consists of two things:
- elements `s_1, s_2, s_1*, s_2*` with `s_i* s_j = δ_ij` and `s_1 s_1* + s_2 s_2* = 1`;
- a unital endomorphism `σ` with `σ(a) = s_1 a s_1* + s_2 σ(a) s_2*` for every `a`.

Given the Cuntz relations, the swindle identity is equivalent to `σ(a) s_1 = s_1 a` together with
`σ(a) s_2 = s_2 σ(a)`.

**Claim.** Let `K` be any field (for example `F_2`) and let `F` be the free algebra on the twelve
letters `s_i, s_i*, t_i, t_i*` (`i = 1, 2`) and `u, ū, v, v̄`. Let `σ̃ : F -> F` be the
homomorphism
`s_i ↦ t_i`, `s_i* ↦ t_i*`, `t_i ↦ u t_i ū`, `t_i* ↦ u t_i* ū`, `u ↦ v`, `ū ↦ v̄`,
`v ↦ u v ū`, `v̄ ↦ u v̄ ū`.

Let `R` consist of three families:
- (C) the Cuntz relators for `s`;
- (U) `uū − 1, ūu − 1, vv̄ − 1, v̄v − 1`;
- (W) `σ̃(x) s_1 − s_1 x` and `σ̃(x) s_2 − s_2 σ̃(x)` for each of the twelve letters `x`.

Let `Q = {σ̃²(x) − u σ̃(x) ū : x a letter}`. Put `A_sw = F / ⟨R ∪ σ̃(R) ∪ Q ∪ σ̃(Q)⟩`, a finitely
presented algebra. Then:

1. `σ̃` descends to a unital endomorphism `σ` of `A_sw`, and `(s, σ)` is a Cuntz swindle structure on
   `A_sw`.
2. `σ² = Ad(u) ∘ σ` on all of `A_sw`, with `u` a unit. In particular `σ(s_i) = t_i` and
   `σ(u) = v`.
3. `A_sw ≠ 0`. It maps unitally, compatibly with `σ`, into `End_K(V)` for `V` of countable
   dimension, with the swindle `σ(a) = ⊕_n a`.
4. **Universality.** Let `(A', s', σ')` be a swindle algebra with a unit `u'` such that
   `σ'² = Ad(u') σ'`. Then there is a unique unital map `A_sw -> A'` intertwining the swindles and
   sending `u ↦ u'`.
5. **Reduction.** Let `M` be an ideal of `A_sw` that is finitely generated as a two-sided ideal and
   has `σ(M) ⊆ M`. Then `A_sw / M` is finitely presented and carries a Cuntz swindle. Hence the
   statement "fp central simple Cuntz swindle algebras exist" (node
   `fp-central-simple-cuntz-swindle-algebra-exists` on the wave-18 branch) follows as soon as some
   such `M` has `A_sw / M` simple with centre `K`.

   By part 4 it is enough to find **one** simple algebra with centre `K` that has two properties. It
   carries a swindle `(s', σ')` and a unit `u'` with `σ'² = Ad(u') σ'`. And the kernel of
   `A_sw -> A'` is finitely generated. Such a kernel is automatically `σ`-invariant, because the
   map intertwines the swindles. The image is then a finitely presented simple swindle algebra,
   **provided the map is onto a simple algebra**. See Attempts for why this last proviso is the whole
   remaining difficulty.

## Attempts

**Attempt 1: the countable-dimension witness does not descend to a simple quotient.**
`End_K(V)` has exactly three ideals: `0`, the finite-rank ideal `Fin`, and `End_K(V)`. So
`End_K(V)/Fin` is simple with centre `K`. But `σ(a) = ⊕_n a` has infinite rank when `a ≠ 0`, so
`σ(Fin) ⊄ Fin`, and the swindle does not pass to the Calkin-type quotient. It is not known whether
the image of `A_sw` in `End_K(V)` is simple.

**Attempt 2: invariant ideals.**
- For any ideal `I`, the set `I^σ = {a : σ^n(a) ∈ I for all n}` is a `σ`-invariant ideal.
- Zorn's lemma gives a maximal proper `σ`-invariant ideal `M`, and `A_sw / M` is `σ`-simple.
- In a `σ`-simple swindle algebra, every proper ideal `I` has `I^σ = 0`. That does not force
  `I = 0`, because `σ(a)` is an "infinite multiple" of `a` and is not in general in `⟨a⟩`.

So `σ`-simplicity falls short of simplicity, and `M` need not be finitely generated. The open step
is exactly one of two things:
- a finitely generated `σ`-invariant `M` with `A_sw/M` simple and central;
- a simple central model, for example a Steinberg algebra of a minimal effective Hausdorff ample
  groupoid on `Ξ^N` with `Ξ ≅ {*} ⊔ Ξ ≅ Ξ × Ξ`, whose kernel from `A_sw` is finitely generated.

**Attempt 3: why `σ` is not a matrix recursion.**
- The swindle reads `ψ(σ(a)) = diag(a, σ(a))` in the matrix-unit picture of `s`.
- Because `σ(s_i)` has degree 1 for the gauge grading `deg s = 1`, no base `B` of degree 0 inside
  `A` contains `σ(A)`.
- So `A_sw` is not visibly of the form `O_ψ(B)` with `s` as the Leavitt letters.
- The simplicity criterion `leavitt-nekrashevych-completion-simplicity-criterion` therefore does not
  apply off the shelf. To use it one needs a second Cuntz pair as completion letters.
