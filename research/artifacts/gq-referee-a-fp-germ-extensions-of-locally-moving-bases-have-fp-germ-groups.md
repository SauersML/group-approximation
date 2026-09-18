# Referee report (gq-referee-a, proof-gap lens): finitely presented germ extensions of locally moving bases have finitely presented germ groups

**Reviewed** (lane bh-kazhdan-inputs, e57b7ace1), read on origin/main:
- `fp-germ-extensions-of-locally-moving-bases-have-fp-germ-groups`;
- its route `fp-germ-extensions-locally-moving-bases-proof`.

This node generalizes `fp-almost-v-groups-have-fp-germ-groups`, which I passed at 97f2f5761.

**Verdict: PASS for the theorem and its proof.**
- There is one required fix (W1): Thompson's `F` on `[0,1]` does not satisfy (B3) at the endpoints, and the sentence
  "more generally …" needs (B3) as a hypothesis.
- There is one nit.

## The three points the author asked about
- **1. Step 3 uses (B1) for surjectivity.**
  - A `G_B`-arrow `(b)_x` must be realized by a word, and that needs `b` to be a word in the finite set `Y`.
  - Without (B1), `Y` would not be finite, and `E = ⟨Y ∪ Z | R⟩` would not be a finite presentation.
  - The rest of Step 3 carries over from the `V` case unchanged:
    - composites of `G_B`-arrows are actual germs;
    - there are finitely many exceptional relator loops, because each prefix is a permutation and singular sets are
      finite;
    - changing the transport path only conjugates inside `Π_p`.
- **2. Step 5 needs no `Y`-word for `c`.**
  - `c ∈ B` is supported in `U`, so `c(U) = U` and `p' = c(p) ∈ U`.
  - `l` fixes `U` pointwise and preserves its complement, so `l` and `c` commute.
  - Read the word `c^(−1)wc` from `p`. It traverses the path `γ` of any chosen word for `c`, then `w` from `p'`, then
    `γ` backwards, since inverse letters give inverse arrows. So its image is `γ^(−1)λγ`.
  - `p' ∉ B_w`, so `λ` is a composite of `G_B`-arrows, and it equals the germ of `l` at `p' ∈ U`, which is trivial.
  - `Φ` is independent of the word, so `Φ(l) = 1` whatever arrows `γ` uses. ✓
- **The rest of the proof.**
  - Step 1 carries over, since `sing(z^(−1)) = z(sing z)`.
  - In Step 2, `Π_p` is `π_1` of a finite graph of groups with vertex groups `(B)_x`, one per component, and trivial
    edge groups. So it is finitely presented by (B2).
  - Step 6 is the same bookkeeping as in the `V` case. ✓
- **3. The example bases.**
  - *`V_(d,r)`.* The germ groups are trivial or `Z`, and the group is finitely generated. (B3) holds: inside a cone
    in `U` whose interior contains `x`, the copy of `V` on that cone moves `x` into infinitely many points. ✓
  - *`nV`.* Near a fixed point `x`, an element is one brick map. Its germ is determined by the coordinate
    prefix-replacement germs, so `(nV)_x ↪ ∏_j (V)_(x_j) ↪ Z^n`. `nV` is finitely generated (Brin), and (B3) holds
    as for `V`. ✓
  - *`T` on the circle.* There are no global fixed points. The germs are pairs of one-sided germs of slope `2^k`, so
    they embed in `Z²`. (B3) holds via the copy of `F` on a small dyadic arc containing `x` in its interior. ✓
  - *`F` on `[0,1]`.* See W1.

## Required fix
- **W1 (the examples: `F` on `[0,1]`, and "more generally").**
  - Every element of `F` fixes `0` and `1`. So at `x = 0`, every `c ∈ B` has `c(0) = 0`, and (B3) fails for any
    finite `F' ∋ 0`.
  - This is not vacuous. In Step 5 the finite set `B_w` can contain `p = 0`, namely when `w`, read from `0`, applies
    a letter at one of its singular points. Then no `p'` exists.
  - So the theorem, as proved, covers `F` only on `X = (0,1)`, that is, only germ groups at interior points. The
    endpoint germ groups `(E)_0` and `(E)_1` of a germ extension of `F` are not covered.
  - The sentence "more generally any finitely generated locally moving group whose isotropy germ groups are
    finitely generated abelian" has the same problem. Being locally moving does not imply (B3), since a locally
    moving group can have global fixed points.
  - Either:
    - restrict the `F` example to `(0,1)`, and replace "locally moving" by (B3) in the general sentence; or
    - give a separate argument at the global fixed points.

  Consequence 1's mention of `F` needs the same restriction.

## Nit
- **N1 (Setting).** Name the property "moves points locally", and note that it implies BHM's locally moving
  property. The converse fails at global fixed points, which is W1. The node's title uses "locally moving", which
  reads as the weaker BHM notion.
