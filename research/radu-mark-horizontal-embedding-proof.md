---
rg: 2
id: radu-mark-horizontal-embedding-proof
kind: route
title: Move a vertex-fixing kernel element to a boundary vertex of its fixed tree, read xz off the local action, collapse Radu's commutator, and get faithfulness from the second tree
target: radu-mark-survives-only-if-horizontal-group-embeds
requires:
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - radu-mark-is-controlled-by-one-commutator
  - radu-horizontal-quotient-is-arithmetic-lattice
  - radu-horizontal-quotient-is-quaternionic-s-arithmetic
artifacts:
  - research/artifacts/radu-mark-elliptic-check.py
  - research/artifacts/radu-mark-elliptic-check-output-2026-09-13.txt
---

# Proof

Notation of the target. Put `u = yδ^2y` and `A = Γ_R/N`; bars denote images in `A`.

**0. Square table and exact identities.** Each square relator gives `h s = s' h'` for
`h ∈ {a,b,c}` and `s ∈ {x,y,z}`:

```text
(h,s) -> (s',h'):  (a,x)->(x,a)  (a,y)->(y,a)  (a,z)->(z,b)
                   (b,x)->(x,b)  (b,y)->(y,c)  (b,z)->(z,a)
                   (c,x)->(z,c)  (c,y)->(y,b)  (c,z)->(x,c)
```

For example `azbz = 1` gives `az = zb`, and `cxcz = 1` gives `cx = zc` and `cz = xc`. From the
table:

* **(E1)** `δa = xza = xbz = bδ` and `δb = xzb = xaz = aδ`.
* **(E2)** `aδ^2 = δ^2a` and `bδ^2 = δ^2b` by (E1). Also `cδ = cxz = zcz = zxc = δ^(−1)c`, so
  `cδ^2c = δ^(−2)`.
* **(E3)** `yay = a`, and `yby = c` (from `by = yc`); so `cy = yb`.
* **(E4)** `aua = u`. `cuc = (cy)δ^2(yc) = y(bδ^2b)y = u`. `bub = (by)δ^2(yb) = y(cδ^2c)y = u^(−1)`.

Let `χ_u : C → {±1}` be the homomorphism with `a, c ↦ 1` and `b ↦ −1`; it exists because `C` is a
free product of three copies of `C_2`. By (E4) and induction on word length,
`k u k^(−1) = u^(χ_u(k))` for every `k ∈ C`.

The artifact script builds the normal form `v·h` (`v ∈ V`, `h ∈ C`) from the table and checks
every relator, (E1)–(E4), `u^2 = yδ^4y`, `δ^4 ≠ 1`, and the local action below, exactly; its
output file ends `ALL_OK`. Its last check, that short words of `C` move short vertical words, is
a sanity check and is not used.

**The vertical tree.** `Γ_R` acts simply transitively on the vertices of `T_h × T_v`, with
`T_h = Γ_R/V` and `T_v = Γ_R/C` (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`). So
`Γ_R = VC` with `V ∩ C = 1`, `V` is simply transitive on the vertices `vC` of `T_v`, and
`Stab(v·o) = vCv^(−1)`. Adjacency `gC ~ gsC` is well defined because `hsC = s'C` by the table.

At `o`, the table shows that `a` and `b` fix `xC, yC, zC`, and `c` swaps `xC` and `zC` and fixes
`yC`. So the local action of `C` at `o` is the homomorphism `χ : C → {±1}` with `a, b ↦ 1` and
`c ↦ −1`. If `χ(h) = −1`, then `h` swaps `xC` and `zC`. For `w = v·o` with `v ∈ V` and
`γ ∈ Stab(w)`, we have `γ(v s o) = v (v^(−1)γv)(s o)`. So `γ` permutes the neighbours `vso` of `w`
as `v^(−1)γv ∈ C` permutes the `so`.

**1. Item 1.** Let `γ ∈ N` fix a vertex and act nontrivially on `T_v`.
* Its fixed set is a nonempty proper subtree. So some fixed vertex `w = v·o` has a neighbour that
  `γ` moves.
* Then `h' := v^(−1)γv` fixes `o`, so `h' ∈ C`; it lies in `N` by normality; and it moves a
  neighbour of `o`, so `χ(h') = −1`.
* Hence `h'zC = xC`, so `k := xh'z` fixes `o` and `k ∈ C`. Since `h' ∈ N`, `k ≡ xz (mod N)`, that
  is `δ̄ = k̄`.

Now there are two cases.
* **`χ_u(k) = 1`.** Then `ū` commutes with `k̄ = δ̄`. Conjugating `ub = bu^(−1)` (E4) by `δ` and
  using (E1) gives `ūā = āū^(−1)`. With `āū = ūā` (E4) this gives `ū^2 = 1`.
* **`χ_u(k) = −1`.** Then `χ_u(kb) = 1`, so `ū` commutes with `(kb)‾ = δ̄b̄`. Since
  `(δb) b (δb)^(−1) = δbδ^(−1) = a` by (E1), conjugating `ub = bu^(−1)` by `δb` again gives
  `ūā = āū^(−1)`, and so `ū^2 = 1`.

In both cases `δ̄^4 = ȳ ū^2 ȳ = 1`, so `(xz)^4 ∈ N`. These are the exact cases (all defects 0,
with the discrete metric, which is bi-invariant) of `(RL1)` and `(RL3)` in
`radu-mark-is-controlled-by-one-commutator`, where `κ1 = 0` or `κ2 = 0`.

**2. Item 2.** Let `Λ_h = ker(Γ_R → Aut T_v)`. It is normal in `Γ_R` and fixes `o`, so
`Λ_h ⊆ C`.

* Let `ρ : Γ_R → Q` be the horizontal quotient, with kernel `Λ_v`. Since `C` acts simply
  transitively on the vertices of `T_h`, `C ∩ Λ_v = 1`.
* By item 4 of `radu-horizontal-quotient-is-arithmetic-lattice`, `ρ(C) = ρ(<a,b,c>)` fixes a point
  `p_A` of the second tree `T'`, either a vertex or an edge midpoint.
* `ρ(Λ_h)` is normal in `Q` and contained in `ρ(C)`. So for every `q ∈ Q` it lies in
  `q Stab(p_A) q^(−1) = Stab(q p_A)`, and it fixes the `Q`-orbit of `p_A` pointwise.
* By items 1 and 3 there, `Q` is transitive on the vertices of `T'`, and a vertex stabilizer
  permutes the three edges at its vertex as `S_3`. So the orbit of `p_A` is either all vertices,
  or contains every edge at every vertex.
* An automorphism preserving every edge setwise fixes every vertex, since a vertex is the common
  endpoint of two of its edges. In both cases `ρ(Λ_h)` fixes all vertices of `T'`.

`Q` acts on `T'` through `Q ⊆ PB^×(F) → PB^×(F_(𝔮')) ≅ PGL_2(Q_2)`
(`radu-horizontal-quotient-is-quaternionic-s-arithmetic`). This map is injective: an element of
`B^×` that is scalar in `B ⊗ F_(𝔮')` is central in `B`, hence lies in `F^×`. `PGL_2(Q_2)` acts
faithfully on its tree, as used in Part 4 of `radu-horizontal-quotient-is-arithmetic-lattice-proof`.
So `ρ(Λ_h) = 1`, hence `Λ_h ⊆ C ∩ Λ_v = 1`.

**3. Item 3.** Suppose `(xz)^4 ∉ N` and `1 ≠ γ ∈ N ∩ gCg^(−1)`. Then `γ` fixes `g·o`, and it acts
nontrivially on `T_v` by item 2. Item 1 gives `(xz)^4 ∈ N`, a contradiction. So `N` meets no
vertex stabilizer, and `C ∩ N = 1`. The map `C → Γ_R/N` is injective, and `C` contains the free
group of rank 2 on `ab` and `ac`: the even-length subgroup of `C_2 * C_2 * C_2` has index 2, is
torsion free, and has Euler characteristic `2(3/2 − 2) = −1`.

**4. Item 4.**
* If `Γ_R/N` has no nonabelian free subgroup, in particular if it is amenable, then `C ∩ N ≠ 1`
  by item 3, so `(xz)^4 ∈ N`.
* `(xz)^4 ≠ 1` in `Γ_R`: `xzxzxzxz` is a nontrivial reduced word in `V = C_2 * C_2 * C_2`.
  So `Γ_R` is not residually amenable.
* Local embeddability into amenable groups implies residual amenability for a finitely presented
  `G = <S | R>`. Take a partial map into an amenable `H` that is injective and multiplicative on a
  ball containing every relator and a given `g ≠ 1`. Its values on `S` satisfy `R`, so it extends
  to a homomorphism `G → H` that agrees with it on the ball, keeps `g`, and has amenable image.
* A refuted claim's routes are invalidated automatically, and the target records that it refutes
  `radu-lattice-residually-amenable-at-the-mark`. ∎
