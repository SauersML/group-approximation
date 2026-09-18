---
rg: 2
id: kazhdan-central-elements-of-2v-have-slope-free-periodic-points
kind: claim
title: A central element of a Kazhdan (or FW) subgroup of 2V has slope zero at every periodic point; in nV the same holds for slopes of support at least n-1, and for all slopes if Kazhdan subgroups of lower-dimensional kV are finite
distinct_from:
  kazhdan-subgroups-of-brin-thompson-groups-have-finite-center: that asks for finite center outright; this proves the central elements have no periodic point with nonzero slope, which reduces finite center in 2V to central elements whose periodic points are all slope-free (e.g. minimal elements).
  kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures: that uses the slope cocycle against invariant measures of all of K; this uses only fixed points of a central element, where the slope is K-invariant.
requires:
  - thompson-v-has-haagerup-property
artifacts:
  - research/artifacts/gq-bh-bh-free-38-torelli-quotients.md
---

**ESTABLISHED** (lane proof, elementary given Farley's theorem; not reviewed; no
priority claimed).

**Setting.** `C = {0,1}^ω`. `nV` acts on `C^n` by brick maps: on each brick
`w_1C × … × w_nC` of a finite partition, `(w_1u_1,…,w_nu_n) ↦ (w'_1u_1,…,w'_nu_n)`.
The slope `s(g,x) ∈ Z^n` is `(|w'_i| − |w_i|)_i` on the brick containing `x`. It is
well defined, locally constant, and satisfies `s(gh,x) = s(g,hx) + s(h,x)`.

**Theorem.** Let `K ≤ nV` have property (T) or property FW, and let `z ∈ Z(K)`.
Suppose `z^m x = x` and `σ = s(z^m, x) ≠ 0`, and let `J = {i : σ_i = 0}`. Then `K`
has an infinite quotient that embeds in `|J|V` (so `|J|V` contains an infinite
Kazhdan, resp. FW, group), and hence `|J| ≥ 2`.

In particular:
- **For `n = 2`, unconditionally:** every periodic point of `z` has slope `0`.
- **For `n ≥ 3`:** the conclusion holds for slopes with at most one zero
  coordinate. It holds for all slopes if Kazhdan (resp. FW) subgroups of `kV` are
  finite for every `k < n`.

**Proof.**
1. **A `K`-invariant set.** Let `P = {y : z^m y = y, s(z^m,y) = σ}`. It is closed,
   because `Fix(z^m)` is closed and the slope is locally constant.
   - It is `K`-invariant. For `g ∈ K`, `z^m(gy) = g z^m y = gy`.
   - Also `s(z^m, gy) = s(g z^m, y) − s(g, y) = s(g, y) + σ − s(g, y) = σ`,
     using `z^m g = g z^m` and the cocycle identity twice.
2. **Local shape.** On a brick `B` where `z^m` is a single brick map with words
   `w_i ↦ w'_i`:
   - for `i ∉ J`, the equation `w'_i u = w_i u` has at most one solution in `C`;
   - for `i ∈ J`, it has every `u` as a solution when `w'_i = w_i`, and none
     otherwise.
   So `P ∩ B` is empty or `{pt} × w_JC^J` in the coordinates `(I = J^c, J)`. By
   compactness, `P = ⊔_{p ∈ F} {p} × W_p` with `F` finite and each `W_p ⊂ C^J`
   clopen.
3. **The action on `P`.** Each `g ∈ K` maps `P` to itself, locally by brick maps.
   So on `Y = ⊔_p W_p` it acts by homeomorphisms that are locally `J`-brick maps.
   Identify `Y` with a clopen subset of `C^J` via prefix codes and extend by the
   identity. This gives a homomorphism `ρ: K → |J|V`. When `J = ∅`, `ρ` has
   finite image because `P` is finite.
4. **`ρ(K)` is finite when `|J| ≤ 1`.** The group `ρ(K)` is a quotient of `K`, so
   it has (T) (resp. FW).
   - For `|J| = 0` it is finite.
   - For `|J| = 1` it is finite because V has the Haagerup property
     (`thompson-v-has-haagerup-property`), and for FW by
     `fw-subgroups-of-eventually-similar-groups-virtually-embed`.
   - More generally it is finite whenever Kazhdan (resp. FW) subgroups of `|J|V`
     are.
5. **The contradiction.** If `ρ(K)` is finite, `K_1 = ker ρ` has finite index in
   `K`, so it has (T) (resp. FW) and finite abelianization.
   - `K_1` fixes `x ∈ P`, so `χ(g) = s(g, x)` is a homomorphism `K_1 → Z^n`. It
     is additive at a common fixed point.
   - `χ` vanishes. For (T), `K_1^{ab}` is finite and `Z^n` is torsion-free. For
     FW, `K_1` has FW and so has no quotient isomorphic to `Z`.
   - But `z^m ∈ K` fixes `P` pointwise, so `z^m ∈ K_1`, and `χ(z^m) = σ ≠ 0`.

**Consequences.**
- **Excluded central elements.** No Kazhdan or FW subgroup of 2V has a central
  element with an attracting, repelling or saddle periodic point. For example,
  the baker map `(ax,y) ↦ (x,ay)`, whose fixed points have slope `(−1,+1)`, lies in
  the center of no Kazhdan or FW subgroup of 2V.
- **What remains for `kazhdan-subgroups-of-brin-thompson-groups-have-finite-center`
  in 2V:** infinite-order central elements all of whose periodic points have slope
  zero. Examples of such elements are minimal elements, like the SMART moving-tape
  map on `C²`, and elements with no periodic points on a clopen set.
- **The BH test cases.** An embedding of Deligne's lattice `Γ~`, or of the
  Kazhdan subgroup `E` of a Torelli quotient `Q_{g,c}`
  (`torelli-lower-central-quotients-not-rf-proof`), into 2V must send its infinite
  central element to such a slope-free element.

**Calibration.** For `n = 1` the theorem says central elements of Kazhdan
subgroups of V have no periodic point with nonzero slope. That is consistent with
Kazhdan subgroups of V being finite.
