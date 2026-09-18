---
rg: 2
id: neumann-doubling-host-candidate
kind: claim
title: Adding the doubling map to Neumann's group gives a residually finite ascending HNN extension, (locally finite)-by-BS(1,2), whose finite presentability is exactly a window question
distinct_from:
  neumann-alternating-product-group-embeds-in-fp-rf-group: that is Minasyan's open question; this builds one explicit residually finite overgroup of Neumann's group and reduces its finite presentability to a single question, which stays open.
  neumann-group-is-locally-finite-by-z-and-not-fp: that proves structure of Neumann's group itself and constraints on hosts; this builds a specific candidate host and proves its structure.
---

**ESTABLISHED** for the stated properties. Whether the host is finitely presented is
**OPEN**. Elementary; written inline by lane bh-free-59, not independently reviewed, no
priority claimed.

## The candidate

Keep the notation of `neumann-group-is-locally-finite-by-z-and-not-fp`: `M` is the set of
odd `m ≥ 5`, `G = ⟨α, β⟩ ≤ ∏_{m∈M} A_m` is Neumann's group, `a_i = β^iαβ^{-i}`, and
`W_k = ⟨a_0,…,a_k⟩`. Let `s = (s_m)` with `s_m(x) = 2x` on `Z/m`; this is a permutation
because `m` is odd. Put

    Γ = ⟨α, β, s⟩ ≤ ∏_{m∈M} Sym(Z/m).

Composing right to left, `s β s^{-1} = β^2` and `s α s^{-1} = (0 2 4)`. Since
`a_0, a_1, a_2` generate `Alt({0,…,4})`, there is a word `u(a_0,a_1,a_2)` equal to
`(0 2 4)` on `{0,…,4}`. It then equals `(0 2 4)` in every coordinate, because every
`m ≥ 5` keeps `{0,…,4}` distinct. So `θ(g) = s g s^{-1}` is an injective endomorphism
of `G`, with `θ(α) = u` and `θ(β) = β^2`.

## Proven properties

**(1)** `Γ` is 3-generated and residually finite (it lies in a product of finite groups),
and `G ≤ Γ`.

**(2) Comparison lemma.** For each `ℓ` there is `C(ℓ)` such that, for any word `w` of
length `≤ ℓ` in `α, β, s` and any `m ∈ M` with `m > C(ℓ)`: `w_m = 1` iff `w = 1` in

    Λ = Alt_fin(Z[1/2]) ⋊ BS(1,2),

where `BS(1,2) = ⟨x↦x+1, x↦2x⟩` acts on `Z[1/2]` and `α ↦ (0 1 2)`.

*Proof.* In `Λ`, write `w = π∘h` with `h(x) = 2^k x + c` and `π` a product of at most
`ℓ` 3-cycles. Here `|k| ≤ ℓ`, and all points involved have numerators and denominators
at most `2^{O(ℓ)}`. For `m > C(ℓ)`, reduction `Z[1/2] → Z/m` is injective on those
points and is `BS(1,2)`-equivariant, so `w_m = π_m∘h_m`. Suppose `h ≠ id`.
- If `k ≠ 0`: then `m ∤ 2^k − 1` because `m > 2^{|k|}`. So `h_m` fixes at most
  `gcd(2^k−1, m) ≤ m/3` points.
- If `k = 0`: then `c ≢ 0 (mod m)`, so `h_m` fixes nothing.

Either way `h_m` moves `≥ 2m/3 > 3ℓ` points, while `π_m` moves at most `3ℓ` points. So
`w_m = 1` forces `h = id` and then `π = 1`. The converse is immediate. ∎

**(3) Extension.** Words trivial in `Γ` are trivial in large coordinates, so by (2) they
are trivial in `Λ`. This gives an epimorphism `Γ → Λ` whose kernel is the set of
elements trivial in all large coordinates. That kernel is `⊕_{m∈M} A_m`: by (2) its
elements have `h = id`, so they are products of even permutations, and they contain every
coordinate `A_m` by the window proposition. So

    1 → ⊕_{m∈M} A_m → Γ → Λ → 1.

**(4) Λ is not finitely presented**, and neither is `L = Alt_fin(Z) ⋊ Z`. By (2), the
finite images `Γ_m ≤ Sym(Z/m)` converge to `Λ` as marked groups. If `Λ` were finitely
presented, `Γ_m` would be a quotient of `Λ` for large `m`. But every finite quotient of
`Λ` kills the infinite simple group `Alt_fin(Z[1/2])`, so it is metabelian, while
`Γ_m ⊇ A_m`. So the kernel in (3) is not normally finitely generated, and this is
compatible with `Γ` being finitely presented.

**(5) Structure.** `⟨β, s⟩ ≅ BS(1,2)`: it acts faithfully and affinely on `⊔ Z/m`. The
normal closure of `α` is

    G_∞ = ⋃_{k≥0} s^{-k} G_0 s^{k},

where `G_0 = ⟨a_i⟩`. This union is normal because `s G_0 s^{-1} = θ(G_0) ⊆ G_0` and
`s^kβs^{-k} = β^{2^k}`. It is **locally finite**, because `G_0` is. Also
`G_∞ ∩ ⟨β,s⟩ = 1`: the image in `Λ` of an element of the intersection lies in
`Alt_fin ∩ BS(1,2) = 1`, and `⊕A_m` is torsion while `BS(1,2)` is torsion-free. Hence
`Γ = G_∞ ⋊ BS(1,2)`.

Moreover `Γ ≅ G*_θ`, the ascending HNN extension with `t ↦ s^{-1}`. An element
`t^k g t^{-k}·t^n` with image `1` has `h = id` in large coordinates by (2), so `n = 0`,
and then `g = 1`.

**(6) Exactly what finite presentability needs.** Put

    Γ_K = ⟨α, β, s | sβs^{-1} = β^2, sαs^{-1} = u, all relations of W_K in a_i := β^iαβ^{-i}⟩.

Each `Γ_K` is finitely presented and maps onto `Γ`. Since `Γ = G*_θ`, and every relator
of `G` lies in a `β`-translate of some window, every relator of `Γ` holds in some `Γ_K`.
So **`Γ` is finitely presented iff `Γ_K → Γ` is an isomorphism for some `K`.** A yes
would answer MO 491978 affirmatively. By Proposition 5(a) of the companion node, it would
also answer Minasyan's title question.

## Obstruction for thinner coordinate sets, and why it vanishes for Neumann's set

For `S ⊆ M`, let `Γ^S = ⟨α, β, s⟩ ≤ ∏_{m∈S} Sym(Z/m)`.

**Proposition.** If `M \ S` is infinite, then `Γ^S` is not finitely presented.

*Proof.* Suppose `Γ^S = ⟨α,β,s | R⟩`, where `R` is finite with relators of length
`≤ ℓ`. Each `r ∈ R` is trivial in infinitely many coordinates, so it is trivial in `Λ`
by (2). Hence `r` is trivial in every coordinate `m > C(ℓ)`. Pick `m ∈ M \ S` with
`m > C(ℓ)`. Then `α,β,s ↦ α_m,β_m,s_m` defines a homomorphism `Γ^S → Sym(Z/m)`. By the
window proposition, some word in `α, β` is trivial in every coordinate of `M` except `m`,
where it is nontrivial. It is trivial in `Γ^S` but not in `Sym(Z/m)`, a contradiction. ∎

**Remark (proved).** A transitive `BS(1,2)`-set in which `s` fixes a point is `Z/m`
(`m` odd) or `Z[1/2]`. The point stabilizer is `N ⋊ ⟨s⟩`, with `N` an `s`-invariant
subgroup of `Z[1/2]` in both directions, hence an ideal `0` or `mZ[1/2]`. Near its
support, `α` must sit at an `s`-fixed point. So for `S = M` every "coordinate-like"
action is already a genuine `Γ`-action: the three cases are `m ∈ M`, `Z[1/2]` via `Λ`,
and actions with no `α`-support via `Γ → BS(1,2)`. The proposition above therefore gives
nothing for Neumann's own set `M`. Deciding `Γ_K = Γ` needs a different idea.
