# Radu's metabelian quotient: the edge-lamp host and the square firewall (2026-09-13)

Lane `ex2-radu-superstrong-negative`. Unreviewed. Notation as in
`radu-horizontal-tree-group-is-linear` and `radu-horizontal-quotient-is-arithmetic-lattice`.

## 0. Setup

* `Γ_R = <a,b,c,x,y,z | involutions, axax, ayay, azbz, bxbx, bycy, cxcz>` acts simply transitively on
  the vertices of `T_h × T_v`. `V = <x,y,z>` fixes the root of `T_h`; `A = <a,b,c>` fixes the root `o`
  of `T_v`. Every element is uniquely `v h` with `v ∈ V`, `h ∈ A`.
* Vertices of `T_v` are the cosets `vA` (`v ∈ V`), and the edges are `{vA, vsA}` for `s ∈ {x,y,z}`.
  `g ∈ A` acts by `g·vA = v'A`, where `gv = v'h'`. From the six relators, `A` acts through the automaton
  with states `a, b, c`:

  ```text
  a: x→x (a), y→y (a), z→z (b)      b: x→x (b), y→y (c), z→z (a)      c: x→z (c), y→y (b), z→x (c)
  ```

  (`ax = xa`, `ay = ya`, `az = zb`, `bx = xb`, `by = yc`, `bz = za`, `cx = zc`, `cy = yb`, `cz = xc`.)
* `Λ_v = ker(Γ_R → Aut T_h)` is free, contained in `V`, and normally generated there by `(xz)^2` and
  `(xyz)^3`. `W = V/Λ_v ≅ PGL_2(Z)`, and `Q = Γ_R/Λ_v`. Write `C` for the image of `A` in `Q`.
  `C ∩ W = 1`, because `v h ∈ Λ_v ⊂ V` forces `h = 1`.
* `Y = Λ_v\T_v` is the Cayley graph of `W` on `x, y, z`. `Λ_v` is normal, so `Γ_R` acts on `Y`
  through `Q`, and `Stab_Q(o) = C`.
* `G_2 = Γ_R/[Λ_v, Λ_v]`, `δ = xz`, and `ℓ = (xz)^2 ∈ Λ_v`.

## 1. The edge-lamp host

**Theorem 1.** Let `π : T_v → Y` be the quotient. For `g ∈ Γ_R` put `d(g) = π_*[o, g o] ∈ C_1(Y; Z)`,
the image of the geodesic from `o` to `g o`. Then `Φ(g) = (d(g), ḡ)` is a homomorphism
`Γ_R → C_1(Y) ⋊ Q` with kernel `[Λ_v, Λ_v]`. So `G_2` embeds in `C_1(Y) ⋊ Q`.

*Proof.* `T_v` is a tree, so `C_2(T_v) = 0` and `H_1(T_v) = 0`, hence `Z_1(T_v) = 0`. Two 1-chains
with the same boundary are therefore equal, and `[o, gho] = [o, go] + g_*[o, ho]`. Since `π` is
equivariant along `Γ_R → Q`, `d(gh) = d(g) + ḡ·d(h)`, which is the cocycle identity. If `ḡ = 1`,
then `g ∈ Λ_v`, and `d(g)` is the 1-cycle of the loop `π([o, go])`. This is the Hurewicz image of `g` in
`H_1(Y) = Z_1(Y)`: `Y` is a graph, so `B_1 = 0`. Hurewicz `π_1(Y) = Λ_v → H_1(Y)` has kernel
`[Λ_v, Λ_v]`. ∎

**Orbits of oriented edges.** Every element of `Q` maps `y`-edges to `y`-edges and `{x,z}`-edges to
`{x,z}`-edges. `W` preserves labels, and the automaton relabels only `x ↔ z`.
`W` is simply transitive on vertices. On the link of `o`, `a` and `b` fix `xo, yo, zo`, while `c`
swaps `xo ↔ zo` and fixes `yo`. Let `χ : C → {±1}` be the sign of `C` acting on `{xo, zo}`. Then
`χ(a) = χ(b) = 1`, `χ(c) = −1`, and `C_χ = ker χ = <a, b, cac, cbc>`. The oriented edges are:

```text
E_y^or ≅ Q/C,   base (o → yo);         E_xz^or ≅ Q/C_χ,   base e_0 = (o → xo).          (H1)
```

`e ↦ e − ē` embeds `C_1(Y)` equivariantly in `Z[E^or]`. Pulling back along `Q/C_χ → Q/C` embeds
`Z[Q/C]` in `Z[Q/C_χ]`. So

```text
G_2 ↪ Z[Q/C ⊔ Q/C_χ] ⋊ Q ↪ Z^2 wr_(Q/C_χ) Q.                                          (H2)
```

**Corollary 1.** If the set action `Q ↷ Q/C_χ` is sofic (Gao–Kunnawalkam Elayavalli–Patchell
Definition 2.1(5)), then `G_2` is sofic. This is their Theorem 3.6 (`gkp-wreath-permanence-theorem`)
with lamp group `Z^2` and actor `Q`, which is residually finite, plus passage to subgroups.

The "split host" attempt in `radu-nilpotent-by-arithmetic-quotients-are-sofic` used `T_h × Y`. That
creates the boundary submodule `B_1` of the squares and forces a quotient. The graph `Y` alone has
no 2-cells, so there is no quotient.

## 2. The square lamp

`x` and `z` commute in `Q`, and `cxc = z`. So `D_4 = <x, c> = {1, x, z, xz, c, xc, zc, xzc} ⊂ Q`
has order 8. `D_2 = <x,z>` lies in `W`, `c ∉ W`, and `D_4 ∩ C_χ = 1`, since `W ∩ C = 1` and `c ∉ C_χ`.

`D_4` normalizes `C_χ`. `c ∈ C` normalizes its index-2 subgroup. For `x`: `xax = a` and `xbx = b`,
while `xc = cz` and `zaz = b` give `x(cac)x = c(zaz)c = cbc` and `x(cbc)x = cac`.

Let `ε : D_4 → {±1}` be the character with `ε(x) = ε(z) = ε(c) = −1`, the orientation character of
the square. The geodesic of `ℓ = xzxz` from `o` projects to the 4-cycle `1 → x → xz → z → 1` in `Y`,
whose oriented edges are `e_0, xc·e_0, xz·e_0, zc·e_0`. The reversed edges are
`x·e_0, xzc·e_0, z·e_0, c·e_0`. Hence

```text
Φ(ℓ) = Σ_(g ∈ D_4) ε(g) g·e_0  ∈  Z[Q/C_χ],     and the mark is Φ((xz)^4) = 2Φ(ℓ).   (H3)
```

The eight cosets `g C_χ` are distinct, so `(H3)` is visibly nonzero.

## 3. The square firewall for finite `Q`-sets

**Theorem 2.** Let `Q` act on a finite set `Ω`, and let `p ∈ Ω` be fixed by `a, b, cac, cbc`. Then
some orientation-reversing element of `D_4`, one of `x, z, c, xzc`, fixes `p`.

*Proof.* Put `K = Stab_Q(p) ⊇ C_χ` and `N = ker(Q → Sym Ω)`. `N` is normal, so `N ⊂ K`. Let `Ψ` be
the composite

```text
Γ_R → G_2 →Φ C_1(Y) ⋊ Q → C_1^xz(Y) ⋊ Q ↪ Z[Q/C_χ] ⋊ Q → (Z/32)[Q/K] ⋊ Q/N.
```

The third arrow projects onto the `Q`-invariant `{x,z}`-summand, and the fifth pushes forward along
`gC_χ ↦ gK`. Each arrow is a homomorphism, and the target is finite. Put `H = D_4 ∩ K`. The points
`gK` and `g'K` of `Q/K` coincide iff `g^(−1)g' ∈ H`. If `ε|_H = 1`, then by `(H3)`

```text
Ψ((xz)^4) = 2|H| Σ_(gH ∈ D_4/H) ε(g) [gK],
```

whose coefficients `±2|H|` lie in `{±2, ±4, ±8, ±16}` and are nonzero mod 32. But `(xz)^4` lies in
the finite residual of `Γ_R` (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`, item 2), so
`Ψ((xz)^4) = 0`. Hence `ε|_H ≠ 1`, and `H` contains an orientation-reversing element. ∎

**Relation to the sign character.** `ε` is the restriction to `D_4` of the character `ψ'` of
`H_Q = <a,b,c,x,z>` in `radu-delta-squared-orbit-is-signed-permutation-module`, landed by a
neighbouring lane at the same time. Its item 4 goes one way: a sign-reversing element of `H_Q ∩ N`
kills the mark. Theorem 2 with `K = C_χN` goes the other way. Some reflection `g` lies in `C_χN`; write
`g = kn` with `k ∈ C_χ`, and then `n ∈ H_Q ∩ N` has `ψ'(n) = −1`. So `ker ψ'` is not closed in the
induced profinite topology, which is exactly the hypothesis that item leaves open.

**Corollary 2 (exact models of the coset action die at radius 3).** Let `ρ` be an action of `Q` on a
finite set `A`, and let `f : A → B` satisfy `f∘ρ(h) = f` for `h ∈ {a, b, cac, cbc}`. Then
`f∘ρ(g) = f` for some orientation-reversing `g ∈ D_4`.

*Proof.* Apply Theorem 2 to the point `f` of the finite `Q`-set `Q·f ⊂ B^A`, with
`(q·f)(s) = f(ρ(q)^(−1)s)`. It gives `g` with `g·f = f`, and `g^(−1)` is also orientation-reversing. ∎

In an `(F, E, ε')`-orbit approximation of `Q ↷ Q/C_χ` with `E ⊇ D_4·C_χ`, the colouring
`f(s) = π_s(C_χ)` is `C_χ`-invariant on the good set, and `f(ρ(g)s) ≠ f(s)` for every `g ∈ D_4 \ {1}`
on the good set. With zero invariance defect, Corollary 2 forbids this on all of `A`. With a positive
defect, the argument needs a uniform spectral gap of `C_χ` on all finite `Q`-sets. That follows from
the congruence subgroup property for `Q` together with property τ for `C_χ` (both recalled, not
verified here) and bounds the defect below by a constant. Transferring to almost actions needs
flexible permutation stability of `Q`.

## 4. The local meaning of `χ` at the second prime

In the proof of `radu-horizontal-quotient-is-arithmetic-lattice` (Parts 2 and 4), the vertex `p` of
`T'` has `Stab_W(p) = S_3 = <xz, xyx> = {1, xz, xyx, xyz, zyx, zyz}`, and the edges at `p`
correspond to the `<xz>`-cosets `{1, xz}`, `{xyx, xyz}`, `{zyx, zyz}`. The automaton maps `S_3·o`
to itself under `a, b, c`. On these three pairs, `a` and `b` fix all three, while `c` fixes
`{1, xz}` and swaps the other two (`c·xyx = zyx`, `c·xyz = zyz`).

**Hypothesis (not checked).** `C` fixes `p`. This holds iff the `W`-equivariant map
`w·o ↦ ρ(w)p` is also `C`-equivariant. It is plausible, because `C` preserves the fibre `S_3·o`,
but that alone does not prove it. A direct check needs `ρ(a), ρ(b), ρ(c)` at `𝔮'`.

Under this hypothesis, `χ` is the local action of `C` on the star of `p` in `T'`:

```text
C_χ = C ∩ Fix_Q(star of p in T').                                                     (H4)
```

So the parity carrying Radu's mark in `G_2` would be a `𝔮'`-adic congruence condition on the
horizontal lattice `C`. `𝔮'` lies in the set of places inverted in `Q`, so the profinite completion
of `Q` cannot see it, and Theorem 2 is the finite-set shadow of that blindness. `(H4)` is not used in
any proof above.
