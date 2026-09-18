---
rg: 2
id: basilica-hnn-has-no-finitely-presented-ascending-base
kind: claim
title: The finitely presented Basilica HNN extension is not an ascending HNN extension of any finitely presented group, because a section-inverting endomorphism turns every such base into a finitely presented cover of the Basilica group
requires:
  - fp-covers-of-grigorchuk-groups-are-large
  - basilica-hnn-extension-is-fp-amenable-non-ea
  - basilica-group-is-torsion-free-and-contains-every-z-n
distinct_from:
  grigorchuk-hnn-tree-stabilizers-not-fp2: that uses torsion to force every tree action of Grigorchuk's extension to have non-fp stabilizers; this uses only a section-inverting endomorphism and Erschler's theorem, so it reaches the torsion-free Basilica extension, but only for ascending decompositions.
  basilica-hnn-extension-is-fp-infinity: that is the open finiteness question; this closes one family of certificates for it, the base-change route in its homotopical form.
---

**ESTABLISHED** (lane proof below, elementary modulo the cited theorems). No priority is claimed. The inputs are
Erschler's theorem, as stated in Benli–Grigorchuk–de la Harpe (arXiv:1206.2072, Theorem 1.8), and Bartholdi–Virág.

## General statement

Let `G ≤ Aut(T_d)` be finitely generated and self-similar, so the sections of its elements lie in `G`. Let
`σ : G → G` be an injective endomorphism, and let `v` be a vertex with `σ(G) ≤ St_G(v)` and `φ_v ∘ σ = id_G`,
where `φ_v : St_G(v) → G` is the section homomorphism. Call such a `σ` **section-inverting**. Let
`H = G*_σ = ⟨G, t | t^(−1) g t = σ(g)⟩`, with `χ(t) = 1`, `χ(G) = 0` and `N = ker χ`. Assume:

**(E)** every finitely presented cover of `G` contains a non-abelian free subgroup, and `G` contains none.

**Theorem.** (Item 3 was added 09-18 through `basilica-fp2-covers-contain-free-subgroups`.)
1. A finitely generated subgroup `K ≤ N` that contains an `H`-conjugate of `G` is **not finitely presented**.
2. So in every ascending HNN decomposition `H = B'*_s` whose base lies in `N`, the base `B'` is not finitely
   presented.
3. **Homological form, for `G = B`.** In items 1 and 2, "not finitely presented" can be replaced by "not of type
   `FP_2`".

**Basilica instance.**
- Take `G = B`, `v = 1` and Bartholdi–Virág's `σ : a ↦ b^2, b ↦ a`. Then `σ(g) = (a^(ε_a(g)), g)`
  (`basilica-group-is-torsion-free-and-contains-every-z-n`, item 4). So `σ(B) ≤ St(1)` and the section of `σ(g)` at
  `1` is `g`.
- (E) holds: finitely presented covers of `B` contain `F_2` (`fp-covers-of-grigorchuk-groups-are-large`, item 2,
  Erschler), and `B` is amenable because it lies in the amenable group `B~`
  (`basilica-hnn-extension-is-fp-amenable-non-ea`, item 3).
- `H_1(B~; Q) = Q` (computed in `basilica-hnn-extension-is-fp-infinity`), so every nonzero character of `B~` is a
  multiple of `χ`, and every ascending decomposition has its base in `N`.
- **Hence `B~` is not an ascending HNN extension of any finitely presented group.**

## Proof

- **Iterated sections.** If `x` fixes `u` and `x|_u` fixes `u'`, then `x` fixes `uu'` with `x|_(uu') = (x|_u)|_(u')`.
  By induction `σ^q(G) ≤ St(v_q)` with `φ_(v_q) ∘ σ^q = id`, where `v_q = v v ⋯ v` (`q` copies).
- **Normal form.** From `t^(−1) g = σ(g) t^(−1)` and `g t = t σ(g)`, every `h ∈ H` is `t^p g t^(−q)` with
  `p, q ≥ 0` and `g ∈ G`. Also `t^(−q) G t^q = σ^q(G) ≤ G`, so `N = ⋃_n t^n G t^(−n)` is an increasing union.
- **Reduction.** `K` is finitely generated, so `K ≤ t^n G t^(−n)` for some `n`. Suppose `K ⊇ hGh^(−1)`, and write
  `t^(−n)h = t^p g t^(−q)`.
  - Let `K' = t^(−p) t^(−n) K t^n t^p`, which is isomorphic to `K`.
  - Then `K' ≤ t^(−p) G t^p = σ^p(G) ≤ G`.
  - Also `K' ⊇ g t^(−q) G t^q g^(−1) = g σ^q(G) g^(−1) =: D`.
- **Section at the conjugated vertex.** Put `c = g^(−1)` and `w = v_q · c`, in the right-action convention of main,
  where `x^(−1) y x` fixes `u·x` when `y` fixes `u`.
  - Then `D = c^(−1) σ^q(G) c` fixes `w`.
  - `φ_w(c^(−1) σ^q(y) c) = (c|_(v_q))^(−1) · y · (c|_(v_q))`, and `c|_(v_q) ∈ G`.
  - So `φ_w(D) = G`.
- **Contradiction.** `St_(K')(w)` has finite index in `K'`, at most `d^|w|`. By self-similarity `φ_w` maps it into
  `G`, and by the previous step onto `G`.
  - If `K` were finitely presented, so would be `K'` and its finite-index subgroup `St_(K')(w)`.
  - Then `St_(K')(w)` would be a finitely presented cover of `G`, so it contains `F_2` by (E).
  - But `St_(K')(w) ≤ G`, and `G` has no `F_2`. ∎
- **Item 2.** Let `H = B'*_s` with `s^(−1) B' s ≤ B'` and `B' ≤ N`. Then `N = ⋃_m s^m B' s^(−m)`, and `G` is finitely
  generated, so `s^(−m) G s^m ≤ B'` for some `m`. Apply item 1, since a finitely presented `B'` is finitely
  generated.

## What this does to the crux (`basilica-hnn-extension-is-fp-infinity`)

- **The base-change route is dead in homotopical form.** No base is finitely presented, so none is of type `F_n`
  for any `n ≥ 2`. Brown's criterion on the Bass–Serre tree of any ascending decomposition cannot certify `F_3`.
  Other tree actions are not treated here.
- **Homological form: also dead (added 09-18).** `basilica-fp2-covers-contain-free-subgroups` transfers de
  Cornulier's perfect-kernel argument (BGdlH, Proposition 5.11) to `B`: every cover of type `FP_2` of `B`
  contains `F_2`. The proof above then runs verbatim with "type `FP_2`" in place of "finitely presented", since
  finite-index subgroups of `FP_2` groups are `FP_2`. **So no ascending base of `B~` is of type `FP_2`.**
- **Σ-invariants (corrected 09-18 after reading Bieri–Renz, Comment. Math. Helv. 63 (1988) 464–497, at source).**
  - An earlier version of this node attributed to Bieri–Renz a characterization of `Σ^m` (`m ≥ 2`) through
    ascending HNN bases of type `F_m`. That paper does not contain it.
  - Its Theorem B says: `Z` is of type `FP_m` over `N ⊇ G'` iff the great subsphere `S(G, N)` lies in
    `Σ^m(G; Z)`. Its §6.5 defers the homotopical invariants to Renz.
  - The `m = 1` characterization (`Σ^1` and ascending HNN extensions over finitely generated bases) is
    Bieri–Neumann–Strebel, Proposition 4.4, as cited in Bieri–Renz §7.2.
  - So nothing is claimed here about `Σ^2(B~)` beyond this: exactly one of `±χ` lies in `Σ^1`. The ascending direction does
    (Bieri–Neumann–Strebel, Proposition 4.4), and not both do, since `N` is not finitely generated (Theorem B
    with `m = 1`). Bieri–Renz §1.3 warn that the sign depends on the left or right action convention.
  - Whether `[χ] ∈ Σ^2(B~)` holds is left open. `F_3` of `B~` does not hinge on it: free groups have empty
    `Σ^1` and are of type `F`.
- **Grigorchuk calibration.** Lysenok's `σ` is also section-inverting at vertex `1`: `d = (1, b)`, `b = (a, c)`,
  `c = (a, d)`, `aca = (d, a)`. The first Grigorchuk group satisfies (E). So the theorem covers Grigorchuk's extension
  too, where `grigorchuk-hnn-tree-stabilizers-not-fp2` already proves more.

## Lesson for general BH

Branch groups become finitely presented only "up to an endomorphism". The endomorphism is section-inverting, so
it plants a full copy of the branch group at a vertex of every overgroup base. That makes any finitely
presented intermediate group a finitely presented cover of the branch group, which Erschler-type theorems forbid.
So finiteness certificates for these extensions, and hosts built from them, cannot pass through a finitely
presented group in which the branch group is an ascending base. This is the same fence that gates germ groups in
V-type BH hosts, where the germ group must be finitely presented. Higher finiteness has to come from a genuinely
higher-dimensional complex, not from the tree.
