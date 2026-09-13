# Paradoxical free minimal subshifts: simple Kazhdan groups with no MF quotient over every group containing F_2

Lane `un-horofunction-families`, 2026-09-13. Status: my own derivation, **unreviewed**.
Inputs: `gjs-countable-groups-have-free-minimal-subflows` (established by citation) and
`paradoxical-cantor-actions-give-simple-kazhdan-not-mf` (reviewed PASS, `un-review3-2026-09-13-part4.md`).

## 0. Target and pivot

The open claim `hyperbolic-group-cantor-model-simple-kazhdan-not-mf` asks for a zero-dimensional boundary model
(horofunction boundary) with a north–south element. In the program, its only use is to feed four hypotheses into
`paradoxical-cantor-actions-give-simple-kazhdan-not-mf`: minimality, topological freeness, (H-gen) and (H-par).
Those four hypotheses need no boundary. Encoding one paradoxical decomposition of the group in a subshift, multiplying
by a Gao–Jackson–Seward free minimal subflow and passing to a minimal subset gives all four, for every finitely
generated group containing a nonabelian free subgroup. The natural-boundary claim stays open as stated; its
downstream consequence does not wait for it.

## 1. A two-piece paradox on Γ

**Lemma 1.** Let `Γ` contain a free subgroup `F = ⟨a, b⟩` of rank 2. Then there are partitions
`Γ = A_1 ⊔ A_2 = B_1 ⊔ B_2` and elements `g_1, g_2, h_1, h_2 ∈ Γ` such that the four sets
`g_1 A_1, g_2 A_2, h_1 B_1, h_2 B_2` are pairwise disjoint.

*Proof.* For `x ∈ {a^{±1}, b^{±1}}` let `W(x) ⊆ F` be the set of reduced words beginning with `x`.
- `a W(a^{-1}) = F \ W(a)`. If `w = a^{-1} v` is reduced, then `v` does not begin with `a`, and `a w = v`.
  Conversely, if `v` does not begin with `a` (including `v = e`), then `a^{-1} v` is reduced and begins with `a^{-1}`.
- So `F = W(a) ⊔ a W(a^{-1})`, and likewise `F = W(b) ⊔ b W(b^{-1})`.
- Put `A_1^F = W(a)`, `A_2^F = a W(a^{-1})`, `g_1 = e`, `g_2 = a^{-1}`, and `B_1^F = W(b)`, `B_2^F = b W(b^{-1})`,
  `h_1 = e`, `h_2 = b^{-1}`. The four translates are `W(a), W(a^{-1}), W(b), W(b^{-1})`: pairwise disjoint.
- Choose a transversal `T` of the right cosets, `Γ = ⊔_{t ∈ T} F t`, and set `A_i = ⊔_t A_i^F t`,
  `B_j = ⊔_t B_j^F t`. Left multiplication by `f ∈ F` maps `F t` to itself and acts there as on `F`
  (`f · (w t) = (f w) t`). So the partitions and the disjointness pass from `F` to `Γ`. ∎

## 2. The encoding

Alphabet `Σ = {0,1}^4`. Let `Γ` act on `Σ^Γ` by `(γ · x)(g) = x(g γ)`. This is a continuous left action:
`(γ · (δ · x))(g) = (δ · x)(g γ) = x(g γ δ) = ((γ δ) · x)(g)`.

Put `x_0(g) = (χ_{A_1}(g), χ_{A_2}(g), χ_{B_1}(g), χ_{B_2}(g))` and `X = cl(Γ · x_0)`, a subshift.
Define the clopen sets `Â_i = {x ∈ X : x(e)_i = 1}` for `i = 1, 2` and `B̂_j = {x ∈ X : x(e)_{2+j} = 1}` for `j = 1, 2`.

**Lemma 2.** `X = Â_1 ⊔ Â_2 = B̂_1 ⊔ B̂_2`, and `g_1 Â_1, g_2 Â_2, h_1 B̂_1, h_2 B̂_2` are pairwise disjoint.

*Proof.*
- **Translates.** `γ · {x : x(e)_k = 1} = {y : (γ^{-1} · y)(e)_k = 1} = {y : y(γ^{-1})_k = 1}`.
- **Closed conditions.** Each assertion says that, at every `y ∈ X`, a fixed finite Boolean identity holds among
  finitely many coordinates of `y`: `y(e)_1 + y(e)_2 = 1`, `y(e)_3 + y(e)_4 = 1`, and
  `y(g_1^{-1})_1 + y(g_2^{-1})_2 + y(h_1^{-1})_3 + y(h_2^{-1})_4 ≤ 1`. Such a set of `y` is closed, so it suffices to check
  the orbit.
- **On the orbit.** For `y = δ · x_0` we have `y(g) = x_0(g δ)`. Then `y(e)_1 + y(e)_2 = χ_{A_1}(δ) + χ_{A_2}(δ) = 1`,
  and similarly for the `B`'s. Also `y(g_i^{-1})_i = χ_{A_i}(g_i^{-1} δ) = χ_{g_i A_i}(δ)` and
  `y(h_j^{-1})_{2+j} = χ_{h_j B_j}(δ)`. By Lemma 1 at most one of the four is `1`. ∎

## 3. Freeness, minimality, Cantor

Let `W ⊆ 2^Γ` be a free minimal subflow (`gjs-countable-groups-have-free-minimal-subflows`; `Γ` is countably
infinite). Let `Γ` act diagonally on `X × W`, and let `Z ⊆ X × W` be a minimal nonempty closed `Γ`-invariant subset
(it exists by Zorn's lemma, using compactness). Write `p : Z → X` for the projection.

**Proposition 3.** `Z` is a Cantor space, the action of `Γ` on `Z` is free and minimal, and:
- **(H-gen)** some finite family of clopen subsets of `Z` has translates separating the points of `Z`;
- **(H-par)** `Z = p^{-1}(Â_1) ⊔ p^{-1}(Â_2) = p^{-1}(B̂_1) ⊔ p^{-1}(B̂_2)`, and the four translates
  `g_i p^{-1}(Â_i)` and `h_j p^{-1}(B̂_j)` are pairwise disjoint.

*Proof.*
- **Free.** `Stab(x, w) ⊆ Stab(w) = {e}`.
- **Minimal.** By the choice of `Z`.
- **Cantor.** `Z` is a closed subset of `Σ^Γ × 2^Γ`, hence compact, metrizable and zero-dimensional (`Γ` is countable).
  `Γ` is infinite and acts freely, so orbits are infinite and `Z` is infinite. A minimal flow with an isolated point is
  finite: the orbit of an isolated point is open, its complement is closed and invariant, so minimality makes `Z` a
  single orbit of isolated points, which compactness makes finite. So `Z` is perfect, and a nonempty compact metrizable
  perfect totally disconnected space is a Cantor space (Brouwer, recalled).
- **(H-gen).** Take the finite family of clopens `{(x, w) ∈ Z : x(e) = σ}` for `σ ∈ Σ`, together with
  `{(x, w) ∈ Z : w(e) = 1}`. By the translate computation of Lemma 2, the translates of the first sets are all the
  coordinate cylinders `{x(γ) = σ}`. For the shift action on `2^Γ` the translates of `{w(e) = 1}` are likewise all the
  coordinate cylinders of `W`. Distinct points of `X × W` differ at some coordinate, so these translates separate the
  points of `X × W`, hence of `Z`.
- **(H-par).** `p` is equivariant, so `g · p^{-1}(E) = p^{-1}(g E)` for every `E ⊆ X`. Preimages of partitions are
  partitions, and preimages of pairwise disjoint sets are pairwise disjoint. Apply this to Lemma 2. ∎

## 4. The groups

**Theorem 4.** Let `Γ` be finitely generated and contain a nonabelian free subgroup. Let `Z` be as in §3, let `q` be a
prime power, `N ≥ 3`, and put `R = LC(Z, F_q) ⋊ Γ`. Then:
1. `S_N = EL_N(R)/Z(EL_N(R))` is an infinite, finitely generated, simple group with property (T), and
   `Z(EL_N(R)) ⊆ F_q^× I_N`;
2. for every `n ≥ 2`, every homomorphism from `EL_n(R)` to an MF group is trivial; in particular `S_N` is not MF and
   has no nontrivial MF quotient.

*Proof.* A free action is topologically free. So Proposition 3 supplies exactly the hypotheses of
`paradoxical-cantor-actions-give-simple-kazhdan-not-mf` (minimal, topologically free, (H-gen), (H-par), `Γ` finitely
generated), whose conclusion is items 1–2. ∎

The explicit full defect from that theorem is `s = Σ_i u_{g_i} χ_{p^{-1}(Â_i)}`, `t = Σ_i χ_{p^{-1}(Â_i)} u_{g_i}^{-1}`:
`ts = 1`, and `1 − st` is the indicator of `Z \ ⊔_i g_i p^{-1}(Â_i)`, which is full through the `B`-pieces.

## 5. Instances (classical inputs recalled, not imported; recorded only in Attempts)

- **Hyperbolic groups.** Non-elementary hyperbolic groups contain `F_2` (Gromov; ping-pong on `∂Γ`). So Theorem 4
  covers every non-elementary hyperbolic group: surface groups of genus `≥ 2`, uniform lattices in `SO(n,1)`,
  `SU(n,1)`, `Sp(n,1)` and `F_4^{-20}`, and hyperbolic Kazhdan groups. No trivial-finite-radical hypothesis is needed,
  because freeness comes from `W`, not from a boundary.
- **Linear groups.** By the Tits alternative, every finitely generated linear group that is not virtually solvable,
  e.g. `SL_n(ℤ)` for `n ≥ 2`.
- **All non-amenable groups.** By Tarski's theorem every non-amenable group has a paradoxical decomposition with finitely
  many pieces, and §§2–4 go through with more pieces. So Theorem 4 should hold for every finitely generated non-amenable
  group. Not claimed here, since Tarski's theorem is not imported.

## 6. One acting group, both sides of the dichotomy

Let `Γ` be finitely generated, residually finite and contain `F_2`: for example `F_2`, `SL_3(ℤ)` or a surface group.
- `residually-finite-group-toeplitz-elementary-groups-lef-kazhdan` (reviewed PASS) gives a Cantor `Γ`-space `Y` with
  `EL_N(LC(Y, F_q) ⋊ Γ)/Z` an infinite simple LEF Kazhdan group.
- Theorem 4 gives a Cantor `Γ`-space `Z` with `EL_N(LC(Z, F_q) ⋊ Γ)/Z` an infinite simple Kazhdan group with no
  nontrivial MF quotient.

So at a fixed acting group, even a Kazhdan one, the approximation type of the elementary group is decided by the
action: towers and an invariant measure versus a paradox. It is not decided by the acting group.

## 7. Model tests

- **Amenable `Γ`** (e.g. `ℤ^d`): every action on a compact space has an invariant probability measure `μ`, and (H-par)
  would force `μ(Z) ≥ 2 μ(Z) > 0`. So no such `Z` exists. The `F_2` hypothesis of Lemma 1 is used exactly to produce the
  paradox.
- **The Pestov ring:** a minimal `ℤ`-subshift carries an invariant measure, so it satisfies no (H-par). That is
  consistent with the group being LEF.
- **`Γ = F_2`:** the boundary action already satisfies (H-par) through north–south elements
  (`north-south-minimal-cantor-action-is-paradoxical`). Theorem 4 gives a different, symbolic model whose action is free,
  not just topologically free.

## 8. The horofunction route (superseded, not pursued)

- **Elementary remark.** For any finitely generated `Γ` with a word metric, the horofunction compactification sits
  inside `∏_g {−|g|, …, |g|}`, so it is compact and totally disconnected. With `(γ · h)(g) = h(γ^{-1} g) − h(γ^{-1})`,
  the increments `h(g s) − h(g) = (g^{-1} · h)(s)` show that translates of the finitely many clopens `{h : h(s) = v}`
  (`s ∈ S`, `v ∈ {−1, 0, 1}`) separate points. So (H-gen) comes for free there.
- **Not checked:** minimality of any closed invariant subset, topological freeness, and north–south dynamics on the
  fibres of `∂_h Γ → ∂Γ`. Coornaert–Papadopoulos and Webster–Winchester were not read, and nothing here rests on them.

## 9. Credit and limits

- **Mechanism.** Rørdam–Sierakowski built free minimal Cantor actions of non-amenable exact groups with purely infinite
  crossed products, from a paradoxical decomposition encoded in a `Γ`-invariant subalgebra of `ℓ^∞(Γ)` (recalled, not
  read). Their exactness hypothesis serves amenability of the action, which is not needed here. Taking the product with a
  free minimal subflow is standard.
- **Unreviewed:** Lemmas 1–2, Proposition 3 and the assembly of Theorem 4.
- **Recalled, not imported:** `F_2` inside non-elementary hyperbolic groups; the Tits alternative; Tarski's theorem;
  Brouwer's characterization of the Cantor set; Zorn's lemma for minimal subsets.
- **Novelty:** no literature search beyond the repo graph.
