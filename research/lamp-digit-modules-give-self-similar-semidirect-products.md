---
rg: 2
id: lamp-digit-modules-give-self-similar-semidirect-products
kind: claim
title: A module over a self-similar group with restriction-closed lamp functions on tree vertices gives a self-similar semidirect product on the enlarged tree
distinct_from:
  boundary-orbit-cyclic-wreath-has-fp-simple-envelope: that realizes infinite cyclic lamps on a constant boundary orbit of a contracting group, by adjoining one alphabet letter, and then builds a finitely presented simple envelope; this is a general criterion for any finite abelian lamp group, any self-similar group and any restriction-closed module, on the product alphabet, and says nothing about finite presentation.
  virtually-endomorphic-self-similar-actions-have-finite-image: that excludes a class of virtual endomorphisms of finite image; this constructs faithful self-similar actions from module data and is not of that shape.
  fp-self-similar-groups-with-arbitrarily-hard-word-problem: that is the open existence question for hard finitely presented self-similar groups; this is a tool that reduces self-similarity of an extension M semidirect Q to data on the module M.
---

**ESTABLISHED** by the proof below (lane bh-free-25, 2026-09-18; elementary, not
reviewed). No novelty is claimed: this is the standard lamp-digit realization of
lamplighter-type groups, written for arbitrary modules.

## Setting

- `X` is a finite alphabet, `T_X` the rooted tree with vertex set `X^*`, and
  `Q ≤ Aut(T_X)` a self-similar group: `q(xw) = q(x) q|_x(w)` with `q|_x ∈ Q`.
- `L` is a finite abelian group, and `L^{X^*}` is the group of all functions
  `f: X^* → L` (arbitrary support), a `Q`-module under `(q·f)(v) = f(q^{-1}v)`.
- For `x ∈ X`, the restriction `ρ_x: L^{X^*} → L^{X^*}` is `(ρ_x f)(w) = f(xw)`.

## Statement

1. **Criterion.** Let `M ≤ L^{X^*}` be a `Q`-submodule with `ρ_x(M) ⊆ M` for all
   `x`. Then `M ⋊ Q` embeds in `Aut(T_{X×L})` as a self-similar group whose
   restriction to the `X`-coordinates is the given action of `Q`.
2. **Abstract form.** Let `M` be any `Q`-module. The following data are
   equivalent to an injective restriction-closed `Q`-map `ι: M → L^{X^*}`:
   additive maps `ρ_x: M → M` (`x ∈ X`) and a `Q`-invariant additive
   `λ: M → L` such that
   - (S1) `ρ_{q(x)}(q·m) = q|_x·ρ_x(m)` for all `q, x, m`;
   - (S2) for every `m ≠ 0` there is a word `w = x_0 ⋯ x_{n−1}` with
     `λ(ρ_{x_{n−1}} ⋯ ρ_{x_0} m) ≠ 0`.

   Call such `(ρ, λ)` a *self-similar module structure* on `M`. So `M ⋊ Q` is
   self-similar on `T_{X×L}` as soon as `M` carries one.
3. **Boundary-orbit wreaths.** Let `ξ = 0^∞` for a letter `0 ∈ X`. Then the
   permutational wreath product `L ≀_{Q·ξ} Q` is self-similar on `T_{X×L}`, for
   every self-similar `Q` and every finite abelian `L`.
4. **Word problem of those wreaths.** With `H = Stab_Q(ξ)` and `L ≠ 1`, the word
   problem of `L ≀_{Q·ξ} Q` and the pair (word problem of `Q`, membership problem
   of `H` in `Q`) reduce to each other in polynomial time.

## Proof

**1.** For `f ∈ L^{X^*}` define `τ_f` on `(X×L)^ℕ` by `(x, e) ↦ (x, e')`,
`e'_n = e_n + f(x_0 ⋯ x_{n−1})` (so `e_0` moves by `f(∅)`). Coordinate `n` of the
image depends only on coordinates `≤ n`, so `τ_f` is a tree automorphism, and
`τ_f τ_g = τ_{f+g}`. If `f(v) ≠ 0` then `τ_f` moves any sequence with
`x_{<|v|} = v`, so `f ↦ τ_f` is injective. Let `q ∈ Q` act by `(x, e) ↦ (q(x), e)`,
a tree automorphism with sections `q|_{x_0}` acting the same way. Since a tree
automorphism preserves prefixes, `(q^{-1}x)_{<n} = q^{-1}(x_{<n})`, so
`q τ_f q^{-1} = τ_{q·f}`. An element `τ_f` fixes the `X`-coordinates and an element
`q` fixes the `L`-coordinates, so `τ(M) ∩ Q = 1`, and `⟨τ(M), Q⟩ = τ(M) ⋊ Q ≅ M ⋊ Q`.
Sections: the section of `τ_f` at the letter `(x_0, e_0)` is `τ_{ρ_{x_0} f}`, because
`e_n` moves by `f(x_0 · x_1 ⋯ x_{n−1}) = (ρ_{x_0}f)(x_1 ⋯ x_{n−1})`. Hence
`(τ_f q)|_{(x_0,e_0)} = τ_{ρ_{q(x_0)} f} · q|_{x_0}`. This lies in `τ(M) ⋊ Q` since
`ρ_x(M) ⊆ M`.

**2.** Given `ι`, put `λ(m) = ι(m)(∅)` and `ρ_x = ι^{-1} ∘ ρ_x ∘ ι`. Invariance of
`λ` holds because `q` fixes the root. For (S1),
`(q·f)(q(x)w) = f(q^{-1}(q(x)w)) = f(x (q|_x)^{-1}(w))`, so
`ρ_{q(x)}(q·f) = q|_x·ρ_x(f)`. (S2) is injectivity. Conversely, given `(ρ, λ)`, put
`ρ_w = ρ_{x_{n−1}} ∘ ⋯ ∘ ρ_{x_0}` for `w = x_0 ⋯ x_{n−1}` and `ι(m)(w) = λ(ρ_w m)`.
- Additivity and (by (S2)) injectivity are immediate.
- Restriction-closed: `ι(m)(xw) = λ(ρ_w ρ_x m) = ι(ρ_x m)(w)`.
- Equivariance: claim `λ(ρ_{q(u)}(q·m)) = λ(ρ_u m)` for all `q, u, m`. By induction on
  `|u|`: the case `u = ∅` is `λ∘q = λ`. For `u = xu'`, `q(u) = q(x) q|_x(u')`, so
  `ρ_{q(u)}(q·m) = ρ_{q|_x(u')}(q|_x·ρ_x m)` by (S1), and induction for `q|_x` gives
  `λ(ρ_{u'} ρ_x m) = λ(ρ_u m)`. Taking `u = q^{-1}v` gives
  `ι(q·m)(v) = ι(m)(q^{-1}v) = (q·ι(m))(v)`.

**3.** For a point `η ∈ Q·ξ` and `l ∈ L` let `l·1_η ∈ L^{X^*}` be `l` on the prefixes
of `η` and `0` elsewhere. Let `M` be the span of these. Then `q·1_η = 1_{qη}`, and
`ρ_x 1_η = [η_0 = x]·1_{σ(η)}` with `σ` the shift. For `η = qξ`,
`σ(qξ) = q|_0(σξ) = q|_0(ξ) ∈ Q·ξ`, since `ξ = 0^∞` is shift-invariant. So `M` is
restriction-closed. Distinct points of `Q·ξ` have distinct prefixes at deep levels,
so the map `L^{(Q·ξ)} → M` is injective and `M ≅ L^{(Q·ξ)}` as `Q`-modules. Apply 1.

**4.** An element `(Σ_i l_i δ_{q_i ξ}, q)` is trivial iff `q = 1` and, for each class
of equal points, the coefficients sum to `0`. Moreover `q_iξ = q_jξ` iff
`q_j^{-1} q_i ∈ H`. Conversely, for `l ≠ 0` and `a = l·δ_ξ`, `q ∈ H` iff
`q a q^{-1} a^{-1} = 1`. ∎

## Calibration

`Q = ⟨a⟩` with `a` the binary odometer (`X = {0,1}`), `L = Z/2`, `ξ = 0^∞`. The
stabilizer is trivial, so item 3 is the lamplighter `Z/2 ≀ Z` acting on the 4-ary
tree. This is the known automaton realization up to a change of alphabet.

## Scope

- Item 1 gives self-similarity, not finite presentation. For item 3 with `Q·ξ`
  infinite the wreath product is never finitely presented, by
  `boundary-orbit-wreaths-over-tree-groups-are-not-fp`.
- The use intended in this lane is the finitely presented Kharlampovich--Myasnikov--Sapir
  groups `T ⋊ Q`: by item 2 they are self-similar as soon as `Q` is and the
  configuration module `T` carries a self-similar module structure. That is recorded
  as the OPEN claim `kms-configuration-modules-carry-self-similar-structures`.
- **Necessary condition.** `λ` is `Q`-invariant, so it vanishes on `I_Q·M`. If
  `M = I_Q·M`, the only restriction-closed equivariant map to `L^{X^*}` is zero. Every KMS
  configuration module has this property (`kms-configuration-modules-have-trivial-coinvariants`),
  and so does every lamp ring in which `u − 1` is a unit for some `u ∈ Q`.
