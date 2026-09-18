# Referee report (gq-referee-a, proof-gap lens): PGL_2(Q) embeds in the rational group

**Reviewed:** `pgl-2-q-embeds-in-the-rational-group` and its route `-proof` (lane gq-deep-free-3, d43f85bec), read on
origin/main.

**Verdict: PASS.** No gaps found. Two sentences should be added (§5). Three facts are imported and belong to the
citation lens: the BBMZ rationality criterion, the simplicity of `R` (Belk–Hyde–Matucci) and Raney. As the node says,
this is essentially Raney's classical transducer theorem in Farey coordinates.

## 1. The coding
- **The charts.** `S_1 = [[0,−1],[1,0]]` maps `[0,∞]` onto the other half. `L` maps `[0,∞]` to `[0,1]` and `R` maps it
  to `[1,∞]`. So the cones are the Stern–Brocot arcs.
- **Standard `V`.** The map `S_v S_w^{-1}` sends `C_{wα}` to `C_{vα}`, so `V` acts as prefix replacement, in standard
  form.

## 2. Step 1
- **Deep cones stay in one half.** A rational point lies in the interior of only finitely many cones: once it has
  appeared as a mediant, every cone containing it has it as an endpoint. So only finitely many `w` have `M(C_w)`
  straddling `0` or `∞`, which are the images of `M^{-1}(0)` and `M^{-1}(∞)`.
- **The local action.** For the other `w`, `u` is the smallest cone containing `M(C_w)`, and `M(w·ω) = u·N(ω)` with
  `N = S_u^{-1} M S_w`. This matches BBMZ's definition of the local action.
- **The matrix `N`.** It is integral and primitive, because unimodular factors preserve the content, and
  `det N = D`.

## 3. Step 2: the sign normalization (the author's weak spot)
- **No zero or pole inside.** `N` maps the arc `[0,∞]` into itself. A pole at an interior point would put `∞` in the
  interior of the image. So `cx + d` has no root in `(0,∞)`, and `c, d` have the same weak sign. The same argument
  applies to `a, b`.
- **Needs a sentence.** To make all four entries `≥ 0` after one overall sign change, the two linear forms must also
  have the same sign as each other. This follows from `N(x) ≥ 0` on `(0,∞)`, since `N` maps into `[0,∞]`. The proof
  should say so. It is not implied by "each has constant weak sign" alone.
- **Maximality of `u`.** It means the image lies in neither child `[0^+, 1^-]` nor `[1^+, ∞^-]`.

## 4. Step 3: finiteness, including `c = 0` and `d = 0` (the author's weak spot)
- **`D > 0`.** The image is `[(b/d)^+, (a/c)^-]`.
  - It is not inside `[0^+, 1^-]` iff `a/c > 1`. The doubled endpoint `1^-` makes `a/c = 1` count as contained.
  - It is not inside `[1^+, ∞^-]` iff `b/d < 1`.
  - `c = 0` gives `a/c = ∞`, and `a ≥ 1` because `ad = D > 0`.
  - `d = 0` would give `N(0) = ∞`, which is impossible for an orientation-preserving map into `[0,∞]`. So `d ≥ b + 1`.
  - Hence `D ≥ b + c + 1`, and `a, d ≤ D + (D−1)^2`.
- **`D < 0`.** Orientation reversal swaps the doubled copies: `0^+ ↦ (b/d)^-` and `∞^- ↦ (a/c)^+`. So the image is
  `[(a/c)^+, (b/d)^-]`.
  - This gives `c ≥ a + 1`, which excludes `c = 0`, and `b ≥ d + 1`, which covers `d = 0` with `b ≥ 1`.
  - Hence `|D| ≥ a + d + 1`.
- **Conclusion.** There are finitely many deep local actions, plus finitely many shallow ones. So `M` is rational, and
  so is `M^{-1}`. The action is faithful on the irrationals.

## 5. Items 3–5
- **Item 3.** All but finitely many local actions of `diag(2^k, 1)` have determinant `2^k`. Infinitely many `w`
  therefore realize some such matrix at arbitrary depth, so a contracting nucleus would contain one for every `k`.
  Distinct determinants give distinct Möbius maps, hence distinct maps on codes. So no contracting RSG contains this
  copy. Correct.
- **Item 4.** Elements of `⟨V, PGL_2(Z[1/P])⟩` are piecewise `PGL_2(Z[1/P])` on finitely many arcs with rational
  endpoints. A finitely generated subgroup of `Γ_2` involves finitely many primes. By Möbius rigidity (three points),
  a global Möbius element of it lies in `PGL_2(Z[1/P])`. Correct.
- **Item 5.** `2·(x/2)/((x/2)+1) = 2x/(x+2)`, with matrix `[[2,0],[1,2]]`, which is primitive of determinant 4. An
  element of `V` is piecewise `PSL_2(Z)`, so agreement on an arc would force the map into `PSL_2(Z)` by rigidity.
  Correct.

## 6. Nits
1. **Step 2.** Add the sentence on why the two signs agree (§3).
2. **Step 1.** Say explicitly that each rational point is interior to only finitely many cones. The phrase "every
   rational point is an endpoint of all cones of depth at least some `k`" is ambiguous. It is true for the cones that
   contain the point.
