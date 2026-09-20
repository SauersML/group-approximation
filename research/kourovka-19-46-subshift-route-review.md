---
rg: 2
id: kourovka-19-46-subshift-route-review
kind: claim
title: Referee review of 43a9564ac4 (Kourovka 19.46 — the CT(Z) subshift-factor route and the recurrent-tail obstruction) — PASS with minor repairs; the problem text matches, Matte Bon's input is confirmed at source, items 1–6 of the recurrent-tails node check (periodic points are rational or lie in pointwise-periodic classes; bounded-scale recurrence closes into an affine-isometric set), and the north-south element's f.g. periodic subgroups are finite
distinct_from:
  ct-p-z-recurrent-slope-tails-force-isometric-minimal-sets: that is a lane node under review; this checks it item by item.
  ct-z-has-an-infinite-finitely-generated-periodic-subgroup: that is the OPEN target node; this checks its problem text and its "What is known" bullets.
---

## Route comparison record

The following comparison was formerly misplaced in `distinct_from`,
which accepts claim ids, not route ids. Its text is preserved without
adding a proof dependency or accepting a route:

- [ct-z-periodic-groups-via-subshift-factors-of-elements](ct-z-periodic-groups-via-subshift-factors-of-elements.md): that is the lane route under review; this checks its lifting step and its input.

**ESTABLISHED (referee bh-ref-e, 2026-09-19; review of three lane nodes by bh-1946, landed in
43a9564ac4).**
- **Priority:** none claimed.
- **Read at source:** the three nodes on origin/main; the arXiv abstract of Matte Bon, arXiv:1408.0762.
- **Kourovka text:** checked against bh-ref-d's earlier extraction from the 21st issue's LaTeX, in
  `ct-p-z-mixed-ray-nodes-review`. I did not reopen the notebook's PDF.
- No code was run.

## 1. The problem text

- The OPEN node quotes 19.46 (Kohl) as "Does the group CT(Z) have finitely generated infinite periodic subgroups?
  (See the definition of CT(Z) in 17.57)."
- This agrees word for word with bh-ref-d's check of the 21st issue's LaTeX source (arXiv:1401.0300v46).
- The reduction to some `CT_P(Z)`, with `P` finite, is correct: finitely many class transpositions involve finitely
  many primes.

## 2. The route (`ct-z-periodic-groups-via-subshift-factors-of-elements`): correct

**Matte Bon, at source.** The abstract of arXiv:1408.0762 reads: "every Grigorchuk group `G_ω` embeds in (the
commutator subgroup of) the topological full group of a minimal subshift", with finitely generated infinite
torsion subgroups and subgroups of intermediate growth as corollaries. So the route's input is correct.
- The Toeplitz and Vorobets description of that subshift is recalled, and the node says so.

**Lifting.**
- For a factor `π : U → X` with `T` aperiodic, `f ↦ f~`, with `f~(u) = ĝ^(n_f(πu))(u)`, is a homomorphism. This
  holds because `n_(fh) = n_f ∘ h + n_h` and `π(h~ u) = h(πu)`.
- It is injective because `S = ĝ|_U` is aperiodic: `S^n u = u` gives `T^n πu = πu`.
- Extending by the identity off `U` gives an element of `[[ĝ]]`. Its cocycle is locally constant, so it is a
  piecewise power of `g` on finitely many classes with `P′`-smooth moduli. It maps `Z` onto `Z`, since its inverse
  lies in the same full group.
- Item 3 of `ct-p-z-is-a-one-vertex-k-graph-full-group` then places it in `CT_P(Z)`.

The route is correct as a conditional. The condition (F) is correctly marked OPEN.

## 3. `ct-p-z-recurrent-slope-tails-force-isometric-minimal-sets`

**1 (the reading lemma): correct.**
- A class of degree `≥ D` has a modulus divisible by every defining modulus, so it lies in one defining class.
- Canonical maps compose, and the degree bookkeeping is `d(m) + d(N) − d(M)`.

**2 (returns): correct.**
- **(a)** Equal degree gives `m = n`, and equal-radius balls that meet are equal.
- **(b)**
  - For `δ_p > 0`, `φ_p` maps `B_p` into itself as a contraction, with fixed point `q = (sm − rn)/(m − n)`.
  - For `δ_p < 0`, `φ_p^(−1)` does the same.
  - For `δ_p = 0`, `φ_p` is an isometry of `B_p`.
  - So `F` is nonempty and invariant.

**3 (periodic points): correct, with one repair.**
- In case (b), every coordinate is fixed by an affine map of slope `n/m ≠ 1`, so it equals the same rational `q`.
  Then `q ∈ Ẑ` forces its denominator to be prime to `P′`.
- **Repair.** For the "iff" relative to `U`, choose `E` also large enough that the degree-`E` class `C ∋ x` lies in
  `U`. `U` is clopen, so this is possible. Then the integers of `C` are in `U` and in finite cycles.

**4 (recurrent tails): correct.**
- Pigeonhole in the finitely many degree-`E_0` classes gives `n_1 < n_2` with `n_1 ∈ N_B(x)`. That makes
  `E_0 + t_y(j) ≥ D` for every `j ≥ 0`, so item 1 applies for `L = n_2 − n_1`, and the image class meets `C_0`.
- **Case (a)** gives a finite family of maps.
- **Case (b)** gives `ĝ^L|_F`, an isometry for the max metric. On `F̃ = ⋃_(i<L) ĝ^i F`, every `ĝ^n` is a
  composite of finitely many uniformly continuous maps with isometries, so the family is equicontinuous.
- `C_0 ⊆ U`, because `C_0 ∋ y ∈ U` and `D` resolves `U`.

**5 (subshift factors): correct.**
- `π(M) = X` by minimality.
- Factors of equicontinuous compact systems are equicontinuous (Auslander, *Minimal Flows*, Ch. 2).
- Infinite expansive systems are not equicontinuous.
- The mixed-ray and positive-ray translations of "`N_B(x)` finite for all `B`" are checked:
  - on a mixed ray, `n ∈ N_B` bounds `τ` on both sides, so the condition is unboundedness;
  - on a positive ray, the condition is `liminf τ = −∞`. The three cases `liminf = −∞`, finite, and `τ → +∞` are
    handled correctly.

**6 (the north-south element): correct, with one small gap filled.**
- **The formulas.** They define a bijection of `Z`:
  - domains `{0, 2, 3 (4)} ∪ {1, 5, 9, 13 (16)}`;
  - images `{2, 10, 14 (16)} ∪ {6 (16)} ∪ {0, 1, 3 (4)}`.
- **Fixed points.** `a = −2/3 ∈ 2 + 4Z_2` is attracting, with `ψ(x) − a = 4(x − a)`. `r = −1/3 ∈ 5 + 16Z_2` is
  repelling. Both fixed points have denominator 3, so there are no periodic points on `Z_2 × Z_3`.
- **Minimal fibers.** By lifting the exponent, `S(n) = Σ_(i<n) u^i` satisfies `|S(n) − S(m)|_3 = |n − m|_3`.
  - An isometry of `Z_3` into itself is onto: it is injective on each `Z/3^k`, hence dense, and its image is
    compact.
  - So `x ↦ 4x + 2` and `x ↦ (x − 1)/4` are minimal on `Z_3`, and these fibers are the only minimal sets.
- **Periodic subgroups.**
  - The restrictions to `F_a` and `F_r` land in locally virtually abelian groups, where the elements are
    `Z^(3^N)`-by-finite at level `N`. So a finitely generated periodic image is finite.
  - The kernel `P_0` fixes a clopen neighbourhood of the fibers, by uniqueness of cocycles.
  - `K = ⋃ supp(s_i)` is `P_0`-invariant. If `s_j x ∉ K`, then `s_j` fixes `s_j x`, so `x = s_j x ∉ K`.
  - Each `ψ̂`-orbit meets `K` in at most `2N_0 + 1` points, and the finite-index intersection argument is
    correct.
- **The gap filled.** The node uses *backward* convergence to `r` without proving it. It follows: if some
  backward orbit of `x ≠ a` accumulated at `y ≠ r`, then forward convergence of a neighbourhood of `y` into the
  shrinking basin of `a` would put `x` arbitrarily close to `a`. Compactness then gives the uniform `N_0`. Add a
  line.
- **Wording.** The claim is "every finitely generated periodic subgroup of `[[ψ̂]]` is finite". The full group is
  not itself torsion, since it contains `ψ̂`. The commit message's "torsion locally finite" should be read that way.

## 4. The OPEN node's "What is known"

- **Germ bullet (repair: label it heuristic).** "Grigorchuk's and Nekrashevych's groups … can only enter `CT(Z)`
  with that point blown up, i.e. through a factor map" is not proved. The germ argument only shows that such an
  embedding cannot keep the singular point as a point with its Klein-four germ.
- **The other bullets.** Each cites its source node correctly.

## Verdict

**PASS with minor repairs.** Items 1–6 and the route are correct, and the problem text and Matte Bon's input are
confirmed. Repairs:
- item 3: choose `E` so that the class lies in `U`;
- item 6: add the backward-convergence line;
- the OPEN node: mark the germ bullet heuristic.

19.46 and 17.58 stay OPEN, as the nodes say.
