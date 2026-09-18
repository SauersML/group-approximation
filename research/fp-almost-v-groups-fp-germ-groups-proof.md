---
rg: 2
id: fp-almost-v-groups-fp-germ-groups-proof
kind: route
title: Map the Schreier complex of the point stabilizer into the germ groupoid of V with finitely many free arrows; relators give finitely many loops, and the germ kernel dies by pushing words off the singular points
target: fp-almost-v-groups-have-fp-germ-groups
requires:
  - almost-v-fw-subgroups-act-through-finitely-many-germs
  - shell-envelope-fp-forces-fp-germ-group
---

Notation as in the claim. Fix `p in C` and the finite presentation `E = <Y ∪ Z | R>`. Put
`Ω = E·p`, `St = Stab_E(p)`, and `F = ⋃_{z in Z} (sing(z) ∪ z(sing z))`, a finite set.

**Step 1. Ω is a finite union of V-orbits.** A letter `y in Y` maps `V`-orbits to themselves,
and a letter `z^±` applied at a point `x ∉ F` agrees near `x` with an element of `V`, so it
also stays in `V·x`. Following a word from `p`, the `V`-orbit changes only when a letter
`z^±` is applied at a point of `F`. So `Ω ⊆ V·({p} ∪ F)`.

**Step 2. The groupoid Π.** Let `G_V` be the groupoid with objects `Ω` and arrows the germs
`(v)_x : x -> v(x)` of elements `v in V` at points `x in Ω`. Its components are the
`V`-orbits in `Ω`, finitely many by Step 1. The isotropy `(V)_x` is trivial or infinite
cyclic (Lemma 2 of `normal-germ-extensions-of-thompson-v-contain-no-sl3z-proof`). Let `Π` be
`G_V` with one free arrow `σ_(z,x) : x -> z(x)` adjoined for each `z in Z` and each
`x in sing(z) ∩ Ω`, finitely many in all. `Π` is connected, because `Ω` is one `E`-orbit and
every letter gives an arrow (Step 3). Its isotropy `Π_p` is the fundamental group of a finite
graph of groups: vertex groups `(V)_x`, one per component, and trivial edge groups. So
`Π_p` is a free product of finitely many groups `Z` and a finitely generated free group, and
it is finitely presented.

**Step 3. From words to arrows.** Send a letter `y in Y`, applied at `x in Ω`, to `(y)_x`.
Send `z in Z` applied at `x` to `σ_(z,x)` if `x in sing(z)`, and otherwise to `(v)_x` for any
`v in V` agreeing with `z` near `x`; this germ does not depend on `v`. Inverse letters go to
inverse arrows. This is a morphism from the Schreier graph of `St` in `E` (vertices `Ω`) to
`Π`. So it gives a homomorphism `Φ_0` from the free group on the loops at `p` to `Π_p`.
The Schreier 2-complex, with a 2-cell for each relator at each vertex, has fundamental group
`St`.
- A relator `r` read from `x` that applies no letter `z^±` at one of its singular points maps
  to a composite of `G_V`-arrows. That composite is the actual germ of `r` at `x`, which is
  trivial because `r = 1` in `E`.
- For each relator and each position of a letter `z^±` in it, the starting points `x` from
  which that letter lands on one of its finitely many singular points form a finite set, since
  `x ↦` (current point) is a bijection. So only finitely many relator loops are exceptional.

Transport each exceptional loop to `p` along the image of a path in the Schreier graph. Let
`W_R ⊆ Π_p` be the resulting finite set. Different paths give conjugates by elements of
`Π_p`. So `Φ_0` induces a homomorphism

    Φ : St -> Q_R := Π_p / <<W_R>>.

`Φ` is onto. Every arrow of `Π` is realized: a `G_V`-arrow by the element of `V` it is a germ
of, and `σ_(z,x)` by `z` at `x`. So every loop at `p` in `Π` is the image of a word
representing an element of `St`.

**Step 4. Back to germs.** Sending each arrow to the actual germ, with `σ_(z,x) ↦ (z)_x`,
gives a morphism from `Π` to the germ groupoid of `E`. It kills every relator loop, so it
induces `Ψ : Q_R -> (E)_p`, and `Ψ ∘ Φ` is the germ map `St -> (E)_p`, which is onto.

**Step 5. The germ kernel dies.** Let `l in St` have trivial germ at `p`: `l` is the identity
on an open `U ∋ p`. Let `w` be a word for `l`, and let `B_w` be the finite set of starting
points from which `w` applies a letter `z^±` at one of its singular points.
- `V·p` is dense, so choose `p' in V·p ∩ U` with `p' ≠ p` and `p' ∉ B_w`.
- Write `p = b ζ` and `p' = b' ζ` with the same tail `ζ` and prefixes `b, b'` so long that
  `cone(b)` and `cone(b')` are disjoint and lie in `U`. The prefix exchange `c` swapping them
  lies in `V`, is supported in `U`, and has `c(p) = p'`.
- `c` and `l` commute, since `l` is the identity on `U` and preserves `C \ U`. So `l = c^-1 l c`.
- Read the word `c^-1 w c` from `p`. The letters of `c` are in `Y`. Then `w` is read from `p'`,
  where it applies no `z^±` at a singular point. So every arrow is in `G_V`, and the composite
  is the germ of `c^-1 l c = l` at `p`, which is trivial. So `Φ(l) = 1`.

**Step 6. Conclusion.** By Step 5, `Φ` factors through the germ map as `Φ̄ : (E)_p -> Q_R`,
and `Ψ ∘ Φ̄` is the identity. Also `Φ̄ ∘ Ψ ∘ Φ = Φ̄ ∘ germ = Φ`, and `Φ` is onto, so
`Φ̄ ∘ Ψ = id`. Hence `(E)_p ≅ Π_p / <<W_R>>`, finitely presented. `∎`
