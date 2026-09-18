---
rg: 2
id: last-section-ascending-hnns-embed-in-rover-nekrashevych-groups
kind: claim
title: An ascending HNN extension along an endomorphism that keeps each element as its own last section embeds in a Röver–Nekrashevych group, by a single element of Thompson's F
distinct_from:
  grigorchuk-fp-amenable-group-satisfies-boone-higman: that is the first application, to Lysenok's endomorphism of the first Grigorchuk group; this is the general embedding lemma, with no finiteness or contraction hypothesis.
  ascending-hnn-of-free-groups-satisfy-boone-higman: that embeds F*_phi in a generalized Baumslag–Solitar class through M. Hall's theorem (BLIW Theorem C); this embeds G*_sigma for self-similar-type endomorphisms of tree groups in a Röver–Nekrashevych group, with no tree of groups.
  odometer-2v-is-fp-simple-and-contains-bs12: that realizes BS(1,2) with a baker map on two Cantor coordinates; this stays on one Cantor coordinate and realizes the stable letter by an element of F.
---

**ESTABLISHED** (lane proof, elementary, written below; not reviewed; no priority
claimed).

## Statement

Let `C = {0,1}^N` be the boundary of the binary tree, `G ≤ Aut(T_2)` a group, and
`σ: G → G` an injective endomorphism such that, in the wreath recursion,

```text
σ(g) = (ψ(g), g)      for every g in G   (no root swap; last section = g),
```

for a map `ψ: G → Aut(T_2)`. Then `ψ` is a homomorphism (the first-section map is a
homomorphism on the level-1 stabilizer). Put `h_k = ψ ∘ σ^k` (k ≥ 0), a sequence of
homomorphisms `G → Aut(T_2)`. For `g ∈ G` define `ĝ ∈ Homeo(C)` by

```text
ĝ(1u)          = 1 g(u),
ĝ(0^{k+1}1v)   = 0^{k+1}1 h_k(g)(v)     (k ≥ 0),
ĝ(0^∞)         = 0^∞,
```

and let `s ∈ F ≤ V` be the prefix replacement

```text
s(1u) = 11u,   s(01v) = 10v,   s(00w) = 0w.
```

1. `g ↦ ĝ` is an injective homomorphism `G → Homeo(C)`, and `s ĝ s^{-1} = \widehat{σ(g)}`
   for every `g`.
2. Let `G*_σ = ⟨G, t | t^{-1} g t = σ(g)⟩`. Then `g ↦ ĝ`, `t ↦ s^{-1}` is an injective
   homomorphism `G*_σ → ⟨s, ĝ : g ∈ G⟩ ≤ ⟨F, Ĝ⟩`.
3. In wreath recursion `ĝ = (E_g, g)` and `E_g = (E_{σ(g)}, ψ(g))`, where `E_g` acts on
   `0^k1v` by `h_k(g)` and fixes `0^∞`. So if `G` and every `h_k(G)` lie in a self-similar
   group `S_0`, the group `S = ⟨S_0, ĝ, E_g : g ∈ G⟩` is self-similar and `G*_σ` embeds
   in the Röver–Nekrashevych group `V_2(S)`.

## Proof

**Homomorphism and faithfulness.** On `1C` the map is `g`; on each cone `0^{k+1}1C` it is
`h_k(g)`, a homomorphism in `g`; `0^∞` is fixed. So `g ↦ ĝ` is a homomorphism, and it is
injective because its restriction to `1C` is the given action of `G`.

**The conjugation identity.** Check `s ĝ s^{-1} = \widehat{σ(g)}` on the partition
`11C, 10C, 0C` of `C`:
- `11u`: `s^{-1}(11u) = 1u`, `ĝ(1u) = 1g(u)`, `s(1g(u)) = 11g(u)`; and
  `\widehat{σ(g)}(11u) = 1σ(g)(1u) = 11 g(u)`, since `σ(g)` has last section `g`.
- `10v`: `s^{-1}(10v) = 01v`, `ĝ(01v) = 01 h_0(g)(v)`, `s(01h_0(g)v) = 10 ψ(g)(v)`; and
  `\widehat{σ(g)}(10v) = 1σ(g)(0v) = 10 ψ(g)(v)`.
- `0^{k+1}1v` (k ≥ 0): `s^{-1}` gives `0^{k+2}1v`, `ĝ` gives `0^{k+2}1 h_{k+1}(g)(v)`, `s`
  gives `0^{k+1}1 h_{k+1}(g)(v)`; and `\widehat{σ(g)}(0^{k+1}1v) = 0^{k+1}1 h_k(σ(g))(v)
  = 0^{k+1}1 h_{k+1}(g)(v)`.
- `0^∞` is fixed by both sides.

**The HNN map is well defined.** With `θ(g) = ĝ` and `θ(t) = s^{-1}`,
`θ(t)^{-1}θ(g)θ(t) = s ĝ s^{-1} = \widehat{σ(g)} = θ(σ(g))`.

**Injectivity.** From `t^{-1}gt = σ(g)` we get `G = tσ(G)t^{-1} ≤ tGt^{-1}`, so
`B = ⋃_{k≥0} t^{k} G t^{-k}` is an increasing union, and every element of `G*_σ` has the
form `t^m b` with `m ∈ Z` and `b ∈ B`. Each `t^k G t^{-k}` maps injectively (it is a
conjugate of `G`, and `θ|_G` is injective), so `θ|_B` is injective.

Put `Z_j = 1C ∪ 01C ∪ … ∪ 0^j1C` (j ≥ 0), a strictly increasing chain of clopen sets. Since
`s^{-1}(11C) = 1C`, `s^{-1}(10C) = 01C` and `s^{-1}(0x) = 00x`, we have
`s^{-j}(1C) = Z_j`. Hence `θ(t^j g t^{-j}) = s^{-j} ĝ s^{j}` preserves `Z_j`, because `ĝ`
preserves `1C`. It also preserves every `Z_{j'}` with `j' ≥ j`, since
`s^{-j} ĝ s^{j} = s^{-j'} \widehat{σ^{j'-j}(g)} s^{j'}` by the conjugation identity. So each
`θ(b)`, `b ∈ B`, preserves `Z_j` for all large `j`.

Now suppose `θ(t^m b) = 1` with `m ≠ 0`. Then `θ(t)^m = s^{-m}` equals `θ(b)^{-1}`, which
preserves `Z_j` for large `j`. But `s^{-m}(Z_j) = s^{-m}s^{-j}(1C) = Z_{j+m}` (for
`j ≥ |m|`), and `Z_{j+m} ≠ Z_j`. Contradiction. So `ker θ ⊆ B`, and `ker θ = 1`.

**Self-similarity.** `ĝ(0w) = 0E_g(w)` and `ĝ(1u) = 1g(u)`, where `E_g` acts on
`0^k1v` by `h_k(g)`; and `E_g(0w') = 0E_{σ(g)}(w')`, `E_g(1v) = 1ψ(g)(v)`, because
`h_{k+1}(g) = h_k(σ(g))`. So the sections of `ĝ` are `E_g` and `g`, and those of `E_g`
are `E_{σ(g)}` and `ψ(g)`. `E` is a homomorphism in `g`, as each `h_k` is. Hence `S` is
closed under sections, and `s ∈ V`, `ĝ ∈ S` give `θ(G*_σ) ≤ V_2(S)` (the group of cone
maps of `C` with local actions in `S`; BBMZ arXiv:2309.06224, Example `ex:rn`, read at
source). ∎

## Use

Boone–Higman follows whenever `S` is contracting: BBMZ Corollary `cor:RN_BH` (read at
source: "Every contracting Röver–Nekrashevych group embeds into a finitely presented
simple group"). A convenient sufficient condition: `S` is generated by a finite bounded
automaton (Bondarenko–Nekrashevych; Nekrashevych, *Self-similar groups*, Thm 3.9.12,
not re-read). That holds when `G` and the images `h_k(G)` are bounded, finitely many
`E_g` occur, and `h_k(G)` consists of finitary elements for all large `k`. First instance:
`grigorchuk-fp-amenable-group-satisfies-boone-higman`.

Calibration: the binary odometer `τ` (with `τ(0w) = 1w`, `τ(1w) = 0τ(w)`) satisfies
`τ^2 = (τ, τ)`. So on `G = ⟨τ⟩` the endomorphism `σ(τ^m) = τ^{2m}` has last section
`τ^m` and `ψ = id`, hence `h_k = id` for all `k`. The lemma then embeds
`Z*_σ = BS(1,2)` in `⟨F, τ̂⟩`, where `τ̂` applies `τ` on `1C` and on every cone
`0^{k+1}1C`. Here `E_τ` has linear activity, so part 3 gives no contraction, and nothing
new about BS(1,2) follows; the example only checks the sign conventions.
