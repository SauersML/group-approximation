---
rg: 2
id: twisted-shell-envelopes-of-bs12-meet-the-host-condition
kind: claim
title: Placing the vertices of the Bass--Serre tree of BS(1,2) on the shells of a finite germ extension of V, with the vertex stabilizer <b> acting on its shell by a degree-one zoom, meets every part of the host condition (H) except finite presentation; so the chain group lies in B_A as soon as one such twisted shell envelope is finitely presented with finitely generated point stabilizers
distinct_from:
  higman-group-satisfies-boone-higman: that is the open question for H4; the last section here implants H4 on its four cyclic coset spaces, faithfully as germs, and reduces the question to finite presentation of one full germ extension of V.
  shell-cantor-embeddings-are-finite-germ-extensions: that implants a group through its regular action on the shells; this implants BS(1,2) through its action on the vertices of its Bass--Serre tree, twisted on each shell by the stabilizer, so that the base generator acquires a regular fixed point of degree one.
  bs12-twist-hosts-need-dynamical-degrees: that proves the odometer counting law any germ host must obey; here the law holds automatically, because the degree-one fixed points of b are the fibre points over a Prufer orbit of tree vertices.
  odometer-2v-is-fp-simple-and-contains-bs12: that host contains BS(1,2) = <tau x id, baker>, but its base generator has no fixed point and its dilator has entropy log 2, so it meets neither (H) nor the middle of a chain.
---

**ESTABLISHED** for items 1–3 (lane proof, elementary; not reviewed; no priority claimed). Item 4 is the
open gate.

## Construction

- `A = ⟨a, b | a^-1 b a = b^2⟩`. Its Bass–Serre tree `T` has vertex set `𝒱 = A/⟨b⟩`. Fix a transversal
  `R ∋ 1` and write `x t = t' κ(x, t)` with `t' ∈ R` and `κ(x, t) ∈ ⟨b⟩ ≅ Z`.
- `g ∈ F ≤ V` is an element with fixed point `1^∞` and zoom germ of degree one there (the mirror of
  `0w ↦ 00w`, `10w ↦ 01w`, `11w ↦ 1w`).
- Choose a bijection `ν : 𝒱 -> N`. Put the fibre of `v` on the shell `C_(ν(v)) = 0^(ν(v)) 1 C` of
  `C = {0,1}^N`, with `p = 0^∞`.
- For `x ∈ A` put `x̂(p) = p` and `x̂(0^(ν(tC)) 1 w) = 0^(ν(t'C)) 1 g^(κ(x,t))(w)`.
- `E = ⟨V, Â⟩`.

## Statement

1. **Faithful twisted implant.** `x ↦ x̂` is an injective homomorphism `A -> Homeo(C)`, and `E` is a
   finite germ extension of `V` with `sing(E) ⊆ V·p`.
2. **The host datum.** Let `s_0 = 0^(ν(v_0)) 1 1^∞`, where `v_0 = ⟨b⟩`. Then:
   - `s_0 ∉ V·p`, so `s_0` is a regular point of every element of `E`, and the germ degree
     `χ : Stab_E(s_0) -> (V)_(s_0) ≅ Z` is a homomorphism;
   - `A ∩ Stab_E(s_0) = ⟨b⟩`, and `χ(b̂) = 1`;
   - the degree-one fixed points of `b̂` over the Prüfer orbit `N·v_0 ≅ Z[1/2]/Z` carry the odometer of
     `bs12-twist-hosts-need-dynamical-degrees` automatically.
3. **Reduction.** Suppose `E` is finitely presented and `Stab_E(s_0)` is finitely generated. Then
   `E ↷ V·s_0` is of type (A), (H) of `type-a-actors-closed-under-inner-twisted-lamp-wreaths` holds with
   `h = (1 ↦ e) ∘ χ`, the twisted lamplighter `M_1` lies in `B_A`, and so does the chain group `G_1`
   (through the unreviewed chain `higman-chain-group-pbh-iff-chain-configuration`).
4. **The gate (OPEN).** If `E` is to be certified by Theorem 2.1 of Belk–Hyde–Matucci, then
   `SingFix_E({p},{p})` must be finitely presented, and so must the germ group `Q_ν = ⟨germs of Â, τ⟩`
   at `p` (`bhm-singfix-condition-forces-fp-germ-groups`). Here `τ` is the shell shift.
   `shell-envelope-fp-forces-fp-germ-group` derives the same conclusion from finite presentation of `E`
   alone, for regular implants. Its argument was not re-checked for this twisted, non-regular implant.
   Whether some enumeration `ν` makes `E` finitely presented is open.

## Proof

- **Item 1.**
  - `κ` is a cocycle, so `x ↦ x̂` is a homomorphism. This is the induced action on `A ×_(⟨b⟩) C`, with
    `b` acting on `C` by `g`, carried to the shells.
  - It is faithful: every `1 ≠ x ∈ A` moves some vertex, or fixes all of them and then lies in every
    vertex stabilizer, which is trivial.
  - Each `x̂` permutes the shells and acts on each by a power of `g`, so it is a prefix replacement off
    `p`, and continuous at `p`. So `sing(x̂) ⊆ {p}`. The finite germ extension axioms follow as in
    `shell-cantor-embeddings-are-finite-germ-extensions`, whose proof does not use regularity of the
    action on shells.
- **Item 2.**
  - `s_0` has tail `1^∞`, so `s_0 ∉ V·p`. Hence no element of `E` is singular at `s_0`.
  - `x̂(s_0) = s_0` forces `x` to fix `v_0`, so `x ∈ ⟨b⟩`. And `b` acts on the fibre of `v_0` by
    `g^(κ(b,1)) = g`, which fixes `1^∞` with degree one.
  - The vertices `n·v_0`, `n ∈ N`, are fixed by `b` because `N` is abelian. Over them `b` acts by
    conjugates of `g`.
- **Item 3.**
  - `E·s_0 = V·s_0`, since every element maps `s_0` to a point with the same tail.
  - `V` has finitely many orbits on pairs of a `V`-orbit of rational points.
  - The action is faithful because `V·s_0` is dense.

  With finite presentation and finitely generated stabilizers, this is type (A). The rest is the
  corollary of `type-a-actors-closed-under-inner-twisted-lamp-wreaths`. ∎

## Remarks on the gate

- **No equivariant shift exists.** An `A`-equivariant self-map of `𝒱 = A/⟨b⟩` has the form
  `x⟨b⟩ ↦ xy⟨b⟩`, with `⟨b⟩ ⊆ y⟨b⟩y^-1`. For `y = a^n`, `n >= 1`, it is `2^n`-to-1: a vertex goes to
  its `n`-th ancestor. It is injective only when `y⟨b⟩y^-1 = ⟨b⟩`, that is `y ∈ N ≅ Z[1/2]`, and then
  it is bijective. So no injective, non-surjective map, such as the shell shift, is `A`-equivariant, for
  any `ν`. `Q_ν` is generated by a non-regular copy of `A` and a shift that does not normalize it, as for
  the untwisted shells of `research/artifacts/gq-gq-typea-design-u2-germ-implant.md`.
- **Entropy.** By `homogeneous-conjugation-invariants-vanish-on-bs-bases`, a Baumslag–Solitar base has
  entropy `0` or `∞`. The baker dilator of `2V_τ` has entropy `log 2`, so it cannot be the middle `b` of a
  chain in that host. The standard copy `⟨τ × id, u⟩` of `BS(1,2)` there fails (H), since its base has no
  fixed point. Other copies were not examined.

## The same construction for Higman's group

Let `H4 = ⟨g_0, …, g_3 | g_(i+1) g_i g_(i+1)^-1 = g_i^2, i ∈ Z/4⟩`. Each `⟨g_i, g_(i+1)⟩` is a faithful
`BS(1,2)` in `H4`. Put `𝒱_4 = ⊔_(i ∈ Z/4) H4/⟨g_i⟩`. Implant `H4` on the shells over `𝒱_4` exactly as
above: `⟨g_i⟩` acts on the fibre of its base coset by powers of the degree-one zoom `g`. Let `Ē` be the
full closure of `⟨V, Ĥ4⟩`, a finite germ extension of `V` with singular set `V·p`. Then:

1. **H4 embeds in the germ group.** The germ map `H4 -> (Ē)_p` is injective. So `H4 ≤ Ē`.
   - *Proof.* If `x̂` has trivial germ at `p`, then `x` fixes all but finitely many points of
     `H4/⟨g_0⟩`.
   - The cosets `g_1^k ⟨g_0⟩`, `k >= 0`, are pairwise distinct, since in `⟨g_0, g_1⟩ ≅ BS(1,2)` no
     nonzero power of `g_1` lies in the base.
   - Their stabilizers are `g_1^k ⟨g_0⟩ g_1^-k = ⟨g_0^(2^k)⟩`. So `x ∈ ⋂_(k >= k_0) ⟨g_0^(2^k)⟩ = 1`.
2. **Every generator is non-tame, with degree-one regular fixed points.**
   - `g_i` fixes the regular point `s_i`, the point `1^∞` in the fibre of `⟨g_i⟩`, with germ degree `1`.
   - It also fixes the cosets `g_(i+1)^-n ⟨g_i⟩`, `n >= 0`, with degree `2^n`.
   - So `g_i` has infinitely many hyperbolic fixed points, as
     `tame-power-conjugators-have-more-hyperbolic-points` (item 3) requires of any action of `H4` with
     infinite-order generators.
   - Each consecutive pair meets the local part of (H), with the character `χ_i` at `s_i`.
   - `Ē` is not a group of almost automorphisms (its elements are singular at `p`), so
     `higman-group-embeds-in-no-almost-automorphism-group` does not apply.
3. **Reduction.** If `Ē` is finitely presented for some `ν`, then `Ē` is full and clopen transitive, so
   `H4 ∈ B_A` (`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`). Then `H4` embeds in a
   finitely presented simple group.
4. **The gate (OPEN).** On the Theorem 2.1 route, the germ group `Q_4 = ⟨germs of Ĥ4, τ⟩` must be
   finitely presented, and it contains `H4`. So `Q_4` is not soluble and not
   residually finite. By `finite-hirsch-length-soluble-groups-hold-no-bs-chain` (item 3), the ascending
   zoom-tower engine of `zoom-tower-germ-groups-give-f-infinity-germ-extensions` can never certify it.

## Lesson for general BH

**The Bass–Serre tree is the right coordinate system for a twist.** The orbit that (H) needs is exactly
the vertex set `A/⟨b⟩`, and the Prüfer layers `N·v` are its horospheres. Once the tree's vertices are put
on shells and each stabilizer acts on its own shell, every local requirement holds by construction:
- the regular fixed point;
- the degree-one character;
- the odometer on fixed points;
- the trivial intersection `A ∩ Stab = ⟨b⟩`.

What remains is purely global: finite presentation of one germ group at the accumulation point. This is
the same single-point finiteness problem that shell envelopes pose for `GL_n(Q)`. So the chain group and
`GL_n(Q)` now share one gate: **finitely presented germ groups generated by a non-regular implant and a
shift.**

For Higman's group the same implant runs on the four cyclic coset spaces `H4/⟨g_i⟩`. The germ map is
injective for a reason special to Baumslag–Solitar cycles: conjugation by `g_(i+1)` shrinks `⟨g_i⟩` to
`⟨g_i^(2^k)⟩`, so no nontrivial element can fix cofinitely many cosets. So `H4`, the base of `BG`, and
`GL_n(Q)` all meet one gate. It is a finitely presented germ group generated by a non-soluble implant and
a shift that normalizes nothing. Soluble engines cannot certify it, so a positive answer needs a new
finiteness mechanism for such germ groups.
