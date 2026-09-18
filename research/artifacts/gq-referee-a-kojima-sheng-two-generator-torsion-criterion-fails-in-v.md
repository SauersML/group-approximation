# Referee report (gq-referee-a, proof-gap lens): the Kojima–Sheng two-generator torsion criterion fails in V

**Reviewed:** `kojima-sheng-two-generator-torsion-criterion-fails-in-v` (a22c90a4a), read on origin/main. The coordinator
asked me to check two things: the `Δ(3,3,3) ≤ V` counterexample, and whether it really contradicts `Cor:TwoGenerator`
as stated.

**Verdict: PASS.**
- The counterexample is correct.
- It contradicts `Cor:TwoGenerator` exactly as printed, and also the conclusion of `Prop:Identity`, under that
  section's standing hypotheses.
- I checked this against the scratch copy `gq/src/bh-free-50/ks-2603.18410v3.tex`. Its md5,
  `4a3489f524643f173b87367080a5e987`, matches the node's.
- There is one citation-lens remark.

## The counterexample
- **The pieces.**
  - `x_0 ∈ F` has infinite order.
  - `z_1` is `x_0` on the cone `00`.
  - `c : 00 → 01 → 1 → 00` is a prefix replacement with `c³ = 1`.
  - `z_2 = cz_1c^(−1)` is `x_0` on `01`, and `z_3` is `x_0` on `1`. I checked the cones with right-to-left composition.
  - The `z_i` have disjoint supports and infinite order, so they generate `Z³`, and `cz_ic^(−1) = z_(i+1)`.
- **The relations** hold in the abstract group `Z³ ⋊ Z/3`. With `u = z_1z_2^(−1)`:
  - `h³ = u·(cuc^(−1))·(c²uc^(−2))·c³ = (z_1z_2^(−1))(z_2z_3^(−1))(z_3z_1^(−1)) = 1`.
  - `gh = (z_2z_3^(−1))c²`, and `(gh)³ = (z_2z_3^(−1))(z_1z_2^(−1))(z_3z_1^(−1))·c⁶ = 1`. Here I used
    `c²z_2c^(−2) = z_1` and `c⁴(·)c^(−4) = c(·)c^(−1)`.
  - `h` and `gh` map to `c` and `c²` in `Z/3`, so both have order exactly 3.
- **The group is infinite.** `g^(−1)h = z_3z_1^(−1)` has infinite order.
  - `⟨g,h⟩` contains `c` and the `c`-conjugates of `u`, which generate the sum-zero lattice `A ≅ Z²`. So
    `⟨g,h⟩ = A ⋊ ⟨c⟩ ≅ Δ(3,3,3)`. ✓
- **The composition convention does not matter.** With the opposite convention, "`gh`" is our `hg = g^(−1)(gh)g`,
  which is also of order 3.

## Does it contradict the printed statements? Yes
- **The source text.**
  - `Cor:TwoGenerator` (l.1287) reads: "Let `g, h` and `gh` be torsion elements in `nV`. Then … `⟨g,h⟩` … is a
    finite group." It has no further hypothesis.
  - The theorem it serves is stated for `n ≥ 1` (l.147, l.1312), and the abstract includes `n = 1`. So `V = 1V` is in
    scope.
- **`Prop:Identity`.** The standing assumptions of the section are "`g, h ∈ nV` torsion" (l.943) and "`gh` torsion of
  order `p`" (l.1116). Under them, `Prop:Identity` (l.1210) concludes that the dyadic block `R^p` is `g`- and
  `h`-invariant.
  - That forces `⟨g,h⟩ ↪ S_(|R^p|)`, which is how the corollary is proved (l.1293–1297).
  - So the conclusion of `Prop:Identity` is false for this pair, as the node says.
- **Scope of the conclusion.**
  - The induction in `Thm:TorsionLocallyFinite` (l.1311 onward) uses `Cor:TwoGenerator` as its base case and
    `Prop:Identity` in each step. So the published proof of Theorem 1.1 is invalid as written.
  - The theorem itself is not refuted, since `Δ(3,3,3)` is not torsion. The node says both things correctly.
  - It is also correct not to locate the faulty lemma.

## Remark (citation lens)
- For `n = 1` the node calls the statement "Röver's theorem". Kojima–Sheng's own remark (l.1395) credits it to
  `[BCST]`, which is Burillo–Cleary–Stein–Taback, TAMS 353 (2001), a paper on `T`. Referee b should settle the
  attribution. The mathematics here does not depend on it.
