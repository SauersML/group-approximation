---
rg: 2
id: fpbs-mal-depth-promotion-equals-overfold-merge-number-proof
kind: route
title: The folded L_{j+1}-graph maps onto the folded L_j-graph, so promoting chords fold into it only by vertex merges, the domination lemma counts them, and the depth-0 clopen approximation runs unchanged with t_j in place of b
target: fpbs-mal-depth-promotion-equals-overfold-merge-number
requires:
  - fpbs-word-chords-are-dominated-by-merges
  - fpbs-profinite-relcost-equals-fold-seed-density
artifacts:
  - experiments/fpbs-depth-overfolding-2026-09-17/foldlib.py
  - experiments/fpbs-depth-overfolding-2026-09-17/exact_search.py
  - experiments/fpbs-depth-overfolding-2026-09-17/check_surjective.py
  - experiments/fpbs-depth-overfolding-2026-09-17/check_surjective_n12.txt
---

Notation is as in the target. `Q` is a finite `L`-set and `n = |Q|`. Write
`Γ_j = Γ_j(Q)`. Standard facts (F1) and (F2) are those of §1 of
`fpbs-profinite-relcost-equals-fold-seed-density-proof`:
- (F1) a path in a fold lifts to a path in the unfolded graph between the
  same classes, with a freely equal label;
- (F2) in a folded graph, a path whose label reduces to `w` is homotopic rel
  endpoints to the path reading `w`.

One more fact:
- (F3) a morphism from a connected labelled graph into a folded graph is
  determined by the image of one vertex. At each step the next edge is
  forced by its label.

Every vertex of `Γ_j` is joined to a real vertex, because every vertex of
the unfolded graph lies on an `a`-edge or on a `t_j`-path at a real vertex.

## 1. Surjectivity (item 1)

**Existence.** `t_{j+1} = t_j a t_j^{-1} t_j^{-1}` is a word in `a, t_j`.
- In `Γ_j`, read this word from the real `p` along `t_j`-paths and
  `a`-edges. The reading ends at the real `p·t_{j+1}`.
- Send the `t_{j+1}`-path at `p` onto this reading. Send reals and
  `a`-edges to themselves.
- This is a morphism from the unfolded `L_{j+1}`-graph into the folded
  `Γ_j`. So it factors through the fold `Γ_{j+1}`.
- Uniqueness is (F3), since each component contains a real.

**Onto.** The `a`-edges are hit. Take a real `p`.
- **Claim:** the reduced word `t_j` is a prefix of the reduced word
  `t_{j+1}`.
  - For `j = 0`, `t_1 = b a b^{-1} b^{-1}` is reduced and begins with `b`.
  - For `j ≥ 1`, `t_j` begins with `b` and ends with `b^{-1}`, by induction.
  - So `t_j a` is reduced. `red(t_j^{-2})` begins with `b`, because `t_j^{-1}`
    begins with `b` and `w·w` cannot cancel all of `w`.
  - So `t_{j+1} = (t_j a)·red(t_j^{-2})` without cancellation. It begins
    with `b` and ends with `b^{-1}`, which completes the induction.
- In `Γ_{j+1}`, the `t_{j+1}`-path at `p` reads the reduced word `t_{j+1}`.
  Its image under `m` is a path in the folded `Γ_j` reading the same
  reduced word from `p`.
- In a folded graph, the path from `p` reading a given reduced word is
  unique. Its initial segment reading `t_j` is the image in `Γ_j` of the
  `t_j`-path at `p`.
- So every vertex and edge of the `t_j`-path at `p` is hit. These paths and
  the `a`-edges make up all of `Γ_j`.

**Quotient.** `m` is onto, and `Γ_j` is folded, so an edge of `Γ_j` is
determined by its origin and label. So `Γ_{j+1} / ker(m) ≅ Γ_j`, and
`ker(m)` is fold-closed.

## 2. Folding criterion at depth j (item 3, first half)

Let `G(Φ)` be `Γ_{j+1}` with the chord paths attached, and `F(Φ)` its fold.
`ψ` descends to `F(Φ)`, as in depth 0. Real vertices stay distinct.

**Real-to-real paths act.** Let `x` lie over `p`, and let `γ` be a path in
`G(Φ)` from `p` to a real vertex, with label `u`. Chord paths meet
`Γ_{j+1}` only at reals, and their interior vertices have degree 2. Cut `γ`
at the ends of its maximal chord-path segments. Each piece is one of:
- a whole chord path, in either direction;
- an excursion into a chord path and back, with freely trivial label;
- a path inside `Γ_{j+1}` between two reals. By (F1) for the fold
  `Γ_{j+1}`, its label is freely a product of `a^{±1}` and `t_{j+1}^{±1}`,
  so it lies in `L_{j+1}`.

Apply the pieces to `x` in turn, as in the depth-0 route. Each chord step
is taken over its base point, or over its target when read backwards. So
`x·u ∈ [x]_{E_{L_{j+1}} ∨ Φ}`.

**Sufficiency.** Let `f : Γ_j → F(Φ)` fix the reals.
- The `t_j`-path at `p` maps to a path from `p` to the real `p·t_j`, with
  label `t_j`.
- By (F1), `G(Φ)` has a path from `p` to `p·t_j` whose label is freely equal
  to `t_j`.
- So `(x, x·t_j) ∈ E_{L_{j+1}} ∨ Φ` for every `x`. Together with `a`, this
  gives `E_{L_j} ⊆ E_{L_{j+1}} ∨ Φ`.

Freeness is not used here.

**Necessity.** Suppose `E_{L_{j+1}} ∨ Φ ⊇ E_{L_j}` on one essentially free
`X` with factor `Q`.
- For each `p`, some free `x` over `p` has a finite path from `x` to
  `x·t_j`. Its steps are `a^{±1}`, `t_{j+1}^{±1}` and chord steps.
- They trace a path in `G(Φ)` from `p` to a real vertex, and its label
  equals `t_j` by freeness.
- By (F2), `F(Φ)` has a path from `p` reading the reduced `t_j` that ends at
  a real vertex. That vertex lies over `p·t_j`, so it is `p·t_j`.
- Send the unfolded `L_j`-graph into `F(Φ)`: reals and `a`-edges to
  themselves, and each `t_j`-path onto this reading. This is a morphism into
  a folded graph. So it factors through `Γ_j`, which gives `f`.

Let `d_j(Q)` be the least `|Φ|` meeting the criterion, and `d_j^law(Q)` the
least with every chord label in `L_j`.

## 3. Chords are merges: d_j = deep_j (item 3, second half)

**Lower bound.** Let `Φ` be `k` chords, and let `f : Γ_j → F(Φ)` fix the
reals.
- `Γ_{j+1}` is finite and folded. The chord paths run between its
  vertices. By the domination lemma (item 1 of
  [[fpbs-word-chords-are-dominated-by-merges]]), the relation `R` "same
  vertex of `F(Φ)`" on `V(Γ_{j+1})` is `cl(P)` for some set `P` of at most
  `k` pairs. `P ⊆ cl(P) = R`.
- `ψ` descends to `F(Φ)`, so `R` relates only vertices over the same point.
  So `P` is a set of same-fibre pairs.
- Let `g : Γ_{j+1} → F(Φ)` be the canonical map, so `R = ker(g)`. The maps
  `f∘m` and `g` agree on the reals, and every component of `Γ_{j+1}`
  contains a real. By (F3), `g = f∘m`.
- So `ker(m) ⊆ ker(g) = cl(P)`, and `deep_j(Q) ≤ |P| ≤ k`.

This is the step that answers the w15 obstruction. The reading of `t_j` in
`F(Φ)` is `f` of a `t_j`-path, and by item 1 it is `g` of a path of
`Γ_{j+1}`. It never enters the Δ-part.

**Upper bound.** Let `P` be same-fibre pairs with `cl(P) ⊇ ker(m)`.
- For `(u, v) ∈ P` over `y`, choose a path `α` in `Γ_{j+1}` from a real `p`
  to `u`, and a path `β` from `v` to a real `q`. Put
  `w = lab(α) lab(β)`. Then `p·lab(α) = y` and `y·lab(β) = q`, so
  `q = p·w`, and `(p, w)` is a chord.
- The arc labelled `lab(α) lab(β)` folds onto `α` from `p` and onto `β^{-1}`
  from `q`. So it identifies `u` with `v`, and nothing more. A path reading
  the reduced word `w` folds to the same result.
- So `F(Φ) = Γ_{j+1} / cl(P)` for these `|P|` chords.
- `cl(P) ⊇ ker(m)` and `Γ_j = Γ_{j+1} / ker(m)`, by item 1. So `Γ_j` maps
  onto `F(Φ)` fixing the reals.

So `d_j(Q) = deep_j(Q)`.

## 4. Lawful chords (item 2 and item 3, lawful half)

**`d_j^law = law_j`.**
- **Chords with labels in `L_j` stay in the kernel.** For `w ∈ L_j`, write
  `w` as a word in `a, t_j`. In `Γ_j`, it reads from `p` to `p·w` along
  `a`-edges and `t_j`-paths. By (F2), the reduced `w` reads there too.
  - So `m` extends to a morphism `G(Φ) → Γ_j`, which factors through
    `F(Φ)`. Hence `R ⊆ ker(m)`.
  - With §3, `R = ker(m)`. The `P` given by domination lies in
    `R = ker(m)`, so it is lawful, and `d_j^law ≥ law_j`.
- **Lawful pairs give chords with labels in `L_j`.** Take `(u, v)` with
  `m(u) = m(v)`. In §3, the path `m(α) m(β)` of `Γ_j` runs from `p` to `q`.
  By (F1), the label of a real-to-real path of `Γ_j` is freely a product of
  `a^{±1}` and `t_j^{±1}`. So `w ∈ L_j`, and `d_j^law ≤ law_j`.

**`law_j = r(Q^{(j)})`.**
- `φ` is injective. `L_1` is a 2-generated non-abelian subgroup of a free
  group, so it is free of rank 2, and `F_2` is Hopfian.
- Let `X = Q × ρ` with the diagonal action and `ρ` the Bernoulli shift. It
  is free, and each fibre over `Q` has mass `1/n`.
- Let `X^{(j)}` be `X` with `g` acting as `φ^j(g)`. It is free, and it has
  factor `Q^{(j)}`. Moreover:
  - `E_{X^{(j)}|L} = E_{X|L_j}`;
  - `E_{X^{(j)}|L_1} = E_{X|L_{j+1}}`;
  - the chord `(p, w)` with `w ∈ L_j` on `X` is the chord `(p, φ^{-j} w)`
    on `X^{(j)}`, as a partial map.
- The criterion of §2 on `X`, and its depth-0 case on `X^{(j)}` (§1 of the
  depth-0 route; that proof uses only that each fibre has positive mass),
  therefore give `d_j^law(Q) = d_0(Q^{(j)})`.
- By item 4 of [[fpbs-word-chords-are-dominated-by-merges]],
  `d_0(Q^{(j)}) = r(Q^{(j)})`.

Finally, `deep_j ≤ law_j`, since lawful pairs are same-fibre pairs.

## 5. Profinite exactness (item 4)

Let `X = lim Q_m` be essentially free with transitive levels. A level-`m`
chord costs `1/|Q_m|`. `E_{X|L_j}` is generated by `a` and `t_j`, and `a`
lies in `L_{j+1}`. So `E_{L_{j+1}} ∨ Ψ ⊇ E_{L_j}` iff
`(x, x·t_j) ∈ E_{L_{j+1}} ∨ Ψ` for almost every `x`.

**Upper bound.** By §2 sufficiency, which does not use freeness, `deep_j(Q_m)`
level-`m` chords pulled back through `π_m` promote on `X`. So
`Q_j(X) ≤ deep_j(Q_m)/|Q_m|` for every `m`. With lawful chords,
`Q_j^law(X) ≤ law_j(Q_m)/|Q_m|`.

**Lower bound.** Run §3 of the depth-0 route with these substitutions:
- `b` becomes `t_j`;
- the steps `c^{±1}` become `t_{j+1}^{±1}`;
- a pattern is a finite step sequence whose label product is `t_j`;
- the fallback piece `(b, B)` becomes `(t_j, B)`.

The truncation and clopen approximation are unchanged. They use only
countable additivity, invariance of the cylinder partitions, and
`μ(A·h Δ A'·h) = μ(A Δ A')`. They give a finite set `Φ'` of
`N = |Q_m|·C(Φ')` level-`m` chords with `E_{L_{j+1}} ∨ Φ' ⊇ E_{L_j}` and

```text
C(Φ')  ≤  C(Ψ) + 3ε .
```

- Freeness enters twice. A path from `x` to `x·t_j` reads `t_j`. And §2
  necessity applies to `X`.
- By §2 necessity and §3, `N ≥ deep_j(Q_m)`. So
  `inf_m deep_j(Q_m)/|Q_m| ≤ Q_j(X)`.
- If every label of `Ψ` lies in `L_j`, then every label of `Φ'` does too:
  the labels `g_i` are kept, and `t_j ∈ L_j`. Then §4 gives
  `N ≥ law_j(Q_m)`.

With §4, `law_j(Q_m) = r(Q_m^{(j)})`. This proves item 4. ∎

**Checks (artifacts).**
- `foldlib.depth_graphs` builds `Γ_j`, `Γ_{j+1}` and `m`, and asserts that
  `m` is well defined.
- `check_surjective.py` checks item 1 on 15 random levels with `n = 12`,
  for `j = 0..3`. It checks that `m` is onto on vertices and edges, and that
  `cl(ker m) = ker m`. The output `check_surjective_n12.txt` shows 60 of 60
  cases pass, with vertex counts up to `588 → 240`.
- `exact_search.py` computes `deep_j` and `law_j` exactly by breadth-first
  search over partitions.
- `exact_n6_j1.txt` and `exact_n4_j2.txt` list the values.
