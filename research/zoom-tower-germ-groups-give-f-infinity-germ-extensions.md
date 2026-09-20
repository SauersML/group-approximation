---
rg: 2
id: zoom-tower-germ-groups-give-f-infinity-germ-extensions
kind: claim
title: A full finite germ extension of V whose singular germ groups are ascending towers over the zoom, realized by locally supported stable letters, has type F_∞ by Belk-Hyde-Matucci Theorem 2.1; the doubling extension of V on the Cantorized line is a first instance, of type F_∞ with germ group BS(1,2) and a non-normal zoom
distinct_from:
  normal-germ-extensions-of-thompson-v-contain-no-sl3z: that treats the Corollary 2.10 regime, where the zoom is normal in the germ group and no Baumslag-Solitar dilation can live in a germ group; this certifies germ extensions outside that regime, where the zoom is dilated, through the SingFix clause of Theorem 2.1.
  bhm-singfix-condition-forces-fp-germ-groups: that shows Theorem 2.1 forces finitely presented germ groups; this gives a class of germ groups for which the SingFix groups are finitely presented, and in fact F_∞, by an explicit HNN structure.
  scale-periodic-bs-chain-germ-representations-are-not-faithful: that is about towers of height two with a non-ascending top letter (the chain); this is the ascending case, where the tower closes up.
artifacts:
  - research/artifacts/beyond-polynomial-germs/mapping-tori-and-compact-core.md
---

**ESTABLISHED** (lane proof, elementary given Belk–Hyde–Matucci; not reviewed; no priority claimed).
Belk–Hyde–Matucci is arXiv:2407.03149. Its Theorem 2.1 (`thm:SingFixFiniteness`) and Appendix A
(`thm:Stabilizers`) are quoted in `research/artifacts/gq-gq-typea-design-u2-germ-implant.md`.

The later OPEN `compact-core-singfix-finiteness` proposal treats
general faithful annular profiles containing all depth-zero base
isotropy, and requires actual compact-core products and finite-forest
restriction groups. The bilateral application also separates the
eventually-zero and eventually-one species. These new input checks are
not supplied automatically by this earlier zoom-tower result; its
existing status and scope remain unchanged. See the linked artifact.

## Definitions

`V` acts on `C = {0,1}^N`. `G` is a finite germ extension of `V`, as in
`germ-complex-and-bux-gonzalez-morse-inputs`. At a rational point `p`, `(V)_p = ⟨z_p⟩ ≅ Z` is generated
by the zoom.

`(G)_p` is an **ascending zoom tower** of height `r` if there are germs `t_1, …, t_r` with the following
properties. Put `H_0 = ⟨z_p⟩` and `H_i = ⟨H_(i-1), t_i⟩`.
- `t_i H_(i-1) t_i^-1 ⊆ H_(i-1)`, and `H_i` is the ascending HNN extension of `H_(i-1)` by this
  endomorphism.
- `H_r = (G)_p`.

The tower is **locally realized** if every clopen neighbourhood `U` of `p` contains the supports of
elements `β_1, …, β_r ∈ G` with `sing(β_i) = {p}`, `β_i(p) = p` and `(β_i)_p = t_i`. Letters at
different points then have disjoint supports and commute.

## Theorem

Let `G` be a full finite germ extension of `V`. Suppose that:
- `sing(G)` is a finite union of `V`-orbits of rational points;
- every germ group `(G)_p`, `p ∈ sing(G)`, is a locally realized ascending zoom tower.

Then every `SingFix_G(M, M')` with `M ⊆ M'` finite is an iterated ascending HNN extension of `Fix_V(M')`,
with `Σ_(p ∈ M) r_p` stable letters. So `G` has type `F_∞`. If `G` is also clopen transitive (for
example, if it contains `V`), then `G ∈ B_A` by `fp-clopen-transitive-full-cantor-groups-have-type-a-actions`.

## Proof

- **Condition (1) of Theorem 2.1.** `V` has finitely many orbits on `sing(G)^n`. Two `n`-tuples with the
  same coincidence pattern and the same orbit of each entry are related by `V`: map small disjoint cones
  around the entries by prefix replacements that keep tails, then complete on the complements.
- **One point.** Take `M = {p} ⊆ M'`. Choose the `β_i` supported away from `M' \ {p}`. Put
  `S_0 = Fix_V(M')` and `S_i = ⟨S_(i-1), β_i⟩`.
  - *Ascending.* For `g ∈ S_(i-1)`, `sing(β_i g β_i^-1) ⊆ {p}`, by `sing(kh) ⊆ h^-1 sing(k) ∪ sing(h)`.
    Its germ at `p` is `t_i (g)_p t_i^-1 ∈ H_(i-1)`, and it fixes `M'`. For `i = 1` the germ is a power
    of `z_p`, so the element has no singular point and lies in `V` (condition (2) of the definition).
    In general it lies in `S_(i-1)`: it differs from a word in `S_(i-1)` with the same germ by an element
    of `RStab_V(p) ∩ Fix_V(M') ⊆ S_0`.
  - *Onto.* The germ map `S_i -> H_i` is onto. Every element of an ascending HNN extension has the form
    `t^-a h t^b`. Lift it to `β_i^-a g β_i^b`, and absorb the difference, which has trivial germ at `p`,
    into `RStab_V(p) ∩ Fix_V(M') ⊆ S_0`.
  - *Injective.* Let `Ĥ` be the abstract ascending HNN extension of `S_(i-1)` by conjugation with `β_i`.
    `Ĥ -> S_i` is onto. Its kernel lies in the kernel of `Ĥ -> H_i`. That kernel is the directed union
    of the conjugates `β_i^-a R β_i^a`, where `R` is the kernel of `S_(i-1) -> H_(i-1)`. On this union
    the map is injective, since each conjugate maps isomorphically and compatibly.
  - So `S_r = SingFix_G({p}, M')`, and it is an iterated ascending HNN extension of `Fix_V(M')`.
- **Several points.** The letters at different points of `M` have disjoint supports, so they commute and
  normalize each other's stages. Repeat the step at each point.
- **Finiteness.** `Fix_V(M')` has type `F_∞` (Appendix A, `M'` rational). An ascending HNN extension of an
  `F_n` group is `F_n`. So every `SingFix_G(M, M')` is `F_∞`, and Theorem 2.1 applies for every `n`. ∎

## Instance: the doubling extension

Use the Cantorized line `[-∞, +∞]` of `bs-chain-configurations-exist-in-finite-germ-extensions-of-v`, with
`c(x) = x + 1 ∈ V` and `b(x) = 2x`. Let `Γ_1` be the full closure of `⟨V, b⟩`.
- `sing(Γ_1) = O_0 ∪ O_1`, the two `V`-orbits of `-∞` and `+∞`. Near `0^±`, `b` is a zoom, which is a
  `V`-germ.
- `(Γ_1)_(+∞) = ⟨σ, δ⟩ = {x ↦ 2^k x + r : k ∈ Z, r ∈ Z[1/2]} ≅ BS(1,2)`. It is the ascending HNN
  extension of `⟨σ⟩` by `t_1 = δ`, since `δ σ δ^-1 = σ^2`. (The other direction is not ascending:
  `δ^-1 σ δ` is `x ↦ x + 1/2`.) The germ group at `-∞` is the mirror image.
- **Local realization.** For an integer `Y`, let `β` be the identity off `[Y, ∞]`. On `[Y, 2Y]` let it be
  a dyadic PL map onto `[Y, 4Y]`, and on `[2Y, ∞]` let it be `x ↦ 2x`. The clopen sets `[Y, ∞]` form a
  neighbourhood base of `+∞`. Move `β` by `V` to other points of `O_1`.
- **Conclusion.** `Γ_1` has type `F_∞`, is full and clopen transitive, and lies in `B_A`. It contains
  `BS(1,2) = ⟨b, c⟩`. Both generators are tame: `F_c = {±∞} ⊊ F_b = {0^±, ±∞}`.
- **Outside Corollary 2.10.** `(V)_(+∞) = ⟨σ⟩` is neither normal nor of finite index in
  `(Γ_1)_(+∞)`. By Lemma 5 of `normal-germ-extensions-of-thompson-v-contain-no-sl3z`, no Corollary 2.10
  host can carry this dilation in a germ group.

## Scope

`BS(1,2)` itself was already in `B_A` by linearity (`quasi-linear-groups-satisfy-permutational-boone-higman`).
The point is the engine: an explicit regime beyond Corollary 2.10 where the SingFix clause is checkable.
Ascending towers over `Z` are solvable. Heights `<= 2` are metabelian, and by
`chain-configurations-need-unboundedly-many-dilation-eigenvalues` no tower of height `<= 3` contains a
chain configuration. So the engine does not reach `G_1` below height 4.

## Lesson for general BH

Theorem 2.1 is usable beyond the normal regime exactly when the germ group **grows by ascending steps**.
Each new germ conjugates the previous germ group into itself. Its cut-off lift then conjugates the
previous SingFix group into itself, and finiteness passes up the HNN tower for free. Dilation of the zoom
is allowed. What is not allowed is a letter that pushes the zoom **out** of the lower stage, as the square
map of a Baumslag–Solitar chain does (`s σ s^-1` is not affine). So the chain problem for `G_1`, `H4` and
`BG` at a point is exactly this: find a germ tower that is not ascending but still has finitely presented
SingFix groups.
