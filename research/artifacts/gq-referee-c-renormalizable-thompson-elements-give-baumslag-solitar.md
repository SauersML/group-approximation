# Referee report (gq-referee-c): renormalizable-thompson-elements-give-baumslag-solitar

- **Node:** `research/renormalizable-thompson-elements-give-baumslag-solitar.md` and its `-proof` route, landed
  81066618e by lane `gq-affq`.
- **Lens:** independent re-derivation plus calibration.
- **Verdict: PASS.** One remark: the hypothesis "T has infinite order" is redundant (§3).

## 1. Setting

- `T ∈ kV` acts on `X = C^k`.
- `(A, φ)` is a height-`m` renormalization:
  - the levels `T^i A`, `0 <= i < m`, partition `X`, and `T^m A = A`;
  - `φ : A -> X` is a homeomorphism with `φ T^m = T φ` on `A`;
  - `φ` is brick-local: it maps each brick `B_i` of a finite partition of `A` onto a brick `B'_i` by a prefix
    replacement.

## 2. Re-derivation

**The conjugator.** `g(T^i a, y) = (φ(a), c_i y)`, where `c_0, …, c_(m-1)` is a complete prefix code.

- **g is a bijection.** Every point of `X × C` is `(T^i a, y)` for a unique triple `(i, a, y)`. Level `i` goes
  onto `X × C(c_i)` by `(φ T^(-i)) × (c_i ·)`, and the cones `C(c_i)` partition `C`. ✓
- **g ∈ (k+1)V.**
  - `T^(-i)` restricted to the clopen `T^i A` is a prefix replacement on each brick of some finite brick
    partition.
  - Bricks intersect in bricks, and preimages of bricks under a prefix replacement are bricks. So the partition
    can be refined until each piece lands inside one brick `B_j` of `φ`.
  - On each piece, `φ T^(-i)` is a composite of two prefix replacements, hence a prefix replacement.
  - `g` acts on `piece × C` by that replacement in the first `k` coordinates and by `ε ↦ c_i` in the last.
  - The images partition `X × C` because `g` is bijective. So `g` is an element of Brin's `(k+1)V`. ✓
- **The relation g s^m = s g.** For `s = T × id`:
  - `s^m (T^i a, y) = (T^i (T^m a), y)`, with `T^m a ∈ A`;
  - so `g s^m (T^i a, y) = (φ(T^m a), c_i y) = (T φ(a), c_i y) = s g (T^i a, y)`.
  - Hence `u = g^(-1)` satisfies `u s u^(-1) = s^m`. ✓
- **⟨s, u⟩ ≅ BS(1,m).** The quotient argument is correct:
  - A nonzero `N ∩ Z[1/m]` is closed under multiplication by `m^(±1)`, so it contains a nonzero integer `j` with
    `s^j = 1`. That is impossible.
  - Otherwise `N` centralizes `Z[1/m]`, and centralizing forces exponent `e = 0`, so `N ⊆ Z[1/m]` and `N = 0`. ✓

## 3. Remark: infinite order is automatic

Suppose `T` had finite order `N`.
- `T^j A = A` exactly when `m | j`, because the levels are disjoint and `T^m A = A`. So `m | N`.
- `T^m|_A` is conjugate to `T` by `φ`, so it also has order `N`.
- But `(T^m|_A)^(N/m) = T^N|_A = id`, so its order is at most `N/m < N`, since `m >= 2`. Contradiction.

So every height-`m` renormalization, with `m >= 2`, forces infinite order. The hypothesis can be dropped, and
`bs13-in-3v-via-smart-renormalization` does not need the odometer factor for it.

## 4. Calibration

- **The odometer model** (`k = 1`, `m = 2`, `φ(0w) = w`) satisfies items 1–3 on `C`. It fails only because
  `τ ∉ V`, as the node says. The criterion is sharp in that sense: it asks the renormalized element itself to
  lie in `kV`.
- **Brick-local φ may change prefix lengths.** In particular `φ(0w) = w` is admissible: item 3 is about the
  map `A -> X`, not about an element of `V`. This is the point on which
  `gq-affq-smart-renormalization-search.md` §4 was wrong, as its author has since retracted. A prefix
  replacement `uw ↦ vw` with `|u| ≠ |v|` re-indexes the whole tail, and that is still brick-local.
- **O1 and distortion.** `s^(m^n) = u^n s u^(-n)` gives `|s^(m^n)| = O(n)`. This is consistent with O1 and with
  the known facts:
  - no `BS(1,m)` lies in `V` (distortion);
  - `(k+1) >= 2` is needed, since the conjugator uses the extra coordinate.
