# Referee report (gq-referee-a, proof-gap lens): finitely presented almost-V groups have finitely presented germ groups

**Reviewed** (lane bh-kazhdan-inputs, 1d2a0b687), read on origin/main:
- `fp-almost-v-groups-have-fp-germ-groups`;
- its route `fp-almost-v-groups-fp-germ-groups-proof`.

**Verdict: PASS.** There are three nits.
- For the citation lens: Lemma 2 of the `SL_3(Z)` node, that `(V)_x` is trivial or `Z`.

## Step 1: the orbit changes only at `F` (the author asked about this)
- `F = ⋃_z (sing(z) ∪ z(sing z))` contains `sing(z^(±1))`, because `sing(z^(−1)) = z(sing z)`.
- Letters of `Y`, and letters `z^±` applied off their singular set, agree locally with elements of `V`, so they keep
  the `V`-orbit.
- After an orbit change the current point lies in `F`:
  - `z` at `x ∈ sing z` gives `z(x) ∈ z(sing z)`;
  - `z^(−1)` at `x ∈ z(sing z)` gives `z^(−1)x ∈ sing z`.
- So every point of `Ω` lies in `V·p` or in `V·F`, and `Ω` is a finite union of `V`-orbits. ✓

## Steps 2–4: the groupoid, the map, the relator loops
- **The groupoid `Π`.**
  - Its arrows are germs, so composites of `G_V`-arrows are actual germs.
  - Adjoining finitely many free arrows to the connected components gives `Π_p` as a free product of the `(V)_x`,
    one per component, with a free group of finite rank. This is finitely presented. ✓
- **The morphism from the Schreier graph.**
  - The germ at a non-singular point does not depend on the choice of `v`.
  - `z^(−1)` at a point of `z(sing z)` goes to `σ^(−1)`. So `Φ_0` is defined, and `π_1` of the Schreier 2-complex is
    `St`. ✓
- **The relator loops.**
  - A non-exceptional relator loop maps to the actual germ of `r` at `x`, which is trivial.
  - For each letter position, the prefix before that letter acts as a permutation of `C`. So the set of starting
    points `x` for which the letter lands in its finite singular set is finite (N3), and `W_R` is finite.
  - Changing the transport path conjugates within `Π_p`, which does not change the normal closure. ✓
- **Surjectivity of `Φ`.**
  - A `G_V`-arrow `(v)_x` is realized by a `Y`-word for `v` read from `x`, and `σ_(z,x)` by the letter `z`.
  - So every loop at `p` in `Π` is the image of a Schreier loop. ✓
- **`Ψ`.** `σ_(z,x) ↦ (z)_x` kills every relator loop, the exceptional ones included, and `ΨΦ` is the germ map,
  which is onto. ✓

## Step 5: the germ kernel dies (the author asked about this)
- **The choice of `p'`.** `V·p` is dense and infinite, and `B_w` is finite. So there is `p' ∈ V·p ∩ U` with
  `p' ∉ B_w ∪ {p}`.
- **The prefix exchange `c`.** `V`-orbits are tail classes, which gives the common tail `ζ` (N2). Long enough
  prefixes put the two cones, disjoint, inside `U`, and the prefix exchange `c` lies in `V`, is supported in `U`, and
  has `c(p) = p'`.
- **`c` commutes with `l`.**
  - `l` is the identity on `U`, and so it preserves `C ∖ U`.
  - On `U`: `lcx = cx = clx`.
  - Off `U`: `cx = x` and `lx ∉ U`, so `clx = lx = lcx`.
  - So `l = c^(−1)lc`.
- **Reading `c^(−1)wc` from `p`.**
  - The `Y`-letters of `c` take `p` to `p'`.
  - `w` is read from `p' ∉ B_w`, so every arrow is a `G_V`-arrow.
  - It ends at `l(p') = p'`, and `c^(−1)` returns to `p`.
  - The loop represents `l`, and its image is the germ of `l` at `p`, which is trivial.
  - Since `Φ` does not depend on the word, `Φ(l) = 1`. ✓

## Step 6
- `ker(germ) ⊆ ker Φ`, so `Φ = Φ̄ ∘ germ`.
- `ΨΦ̄ = id`, because the germ map is onto. `Φ̄Ψ = id`, because `Φ` is onto.
- So `(E)_p ≅ Π_p / ⟨⟨W_R⟩⟩`. ✓

## Nits
- **N1 (Step 2).** Say that no free arrows are needed for `z^(−1)`. Its singular points are the targets of the
  `σ_(z,x)`, so the inverse arrows cover them. This is why `F` contains both `sing z` and `z(sing z)`.
- **N2 (Step 5).** Say that `V`-orbits in `{0,1}^N` are exactly the tail-equivalence classes. That is what gives
  `p` and `p'` a common tail `ζ`. It is also the one fact the transfer to `V_(d,r)` has to check.
- **N3 (Step 3).** "`x ↦` (current point) is a bijection" should read: the prefix of `r` before the given letter acts
  as a permutation of `C`. So its preimage of the finite set `sing(z^±)` is finite.
