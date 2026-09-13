# ZP topology review, 2026-09-13, part 2

Reviewer lane: z-verify-topology. Verdict conventions as in part 1
(`research/artifacts/zp-review-topology-2026-09-13-part1.md`).

## 9. Problem 1.21 reductions (z1-21-wall-obstruction, 7bbd497c52): four PASS

The root quotes Problem 1.21 verbatim, and both answer routes require the equivalence claim together
with open answer claims, so nothing fires.

**9a. `g-times-z-type-f-iff-g-f-infinity-with-finite-cd` (+ `-proof`): PASS.**
- *Finite presentation of the retract.* With `e = i∘r`, the proof shows `ker r = ⟨⟨x^{-1}e(x)⟩⟩`.
  I checked the identity `(gh)^{-1}e(gh) = h^{-1}(g^{-1}e(g))h · h^{-1}e(h)`. Closure under inverses
  is not written but is immediate: `g e(g)^{-1} = g (g^{-1}e(g))^{-1} g^{-1}`. So G is finitely
  presented.
- *FP_∞.* The Bieri–Eckmann comparison map for G at `(M_λ)` is a retract, in the arrow category, of
  the one for `G × Z` at `(r^*M_λ)`, since `r^*∏ = ∏r^*` and `(r∘i)_* = id`. Correct.
- *cd.* `cd G ≤ cd Γ`, and FP_∞ + finite cd = FP (Brown VIII.6).
- *(3) ⇒ (1).* `P_* ⊗_Z (Z[t^±] →(t−1) Z[t^±])` is a finite projective resolution over `ZΓ`, by
  Künneth over Z, since projective ZG-modules are free abelian. Its Euler class is
  `Σ_k (−1)^k([ind P_k] + [ind P_{k−1}]) = 0`, so by the Eilenberg trick Γ is FL, and it is finitely
  presented, so it is of type F (Brown VIII.7). Correct.

**9b. `fp-type-fp-group-is-type-f-iff-wall-class-vanishes` (+ `-proof`): PASS.**
- Independence of the resolution follows from generalized Schanuel.
- (1)⇒(2)⇒(3) are immediate; (3)⇒(2) is the Eilenberg trick; (2)⇒(1) is fp + FL ⇒ F.
- The (S4) cell-attaching sketch at `n = max(3, cd G)` is the standard proof.
- The identification with Wall's obstruction up to sign is correct (Wall 1965), and the node flags it
  as a relation rather than using it.

**9c. `f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f` (+ `-proof` requiring 9a, 9b): PASS.**
- The logic is two lines and correct.
- The informational list of Farrell–Jones classes is outside the claim's logic. The node itself flags
  CAT(0) (arXiv:0901.0442) as "to be checked". My recollection, not re-read here: Bartels–Lück (Ann. of
  Math. 2012) prove the K-theoretic FJC in degrees ≤ 1 for CAT(0) groups, which suffices for
  `K̃_0 = 0`, and Wegner later extends it to all degrees. Whoever relies on the CAT(0) bullet should
  read the source.

**9d. `g-times-h-of-type-f-iff-euler-char-of-h-kills-wall-class` (+ `-proof`): PASS.**
- For a type-F factor H with finite free resolution `Q_j = (ZH)^{m_j}`, the product resolution has
  `E(G×H) = χ(H)·i_*E(G)`.
- `r_* i_* = id` on `K_0` with `r_*[ZΓ] = [ZG]`, so `i_*` descends to reduced K_0.
- (⇐) follows from 9b. (⇒) uses the retract step (fp, FP_∞, finite cd for G) and then applies `r_*`.
- The corollary is correct and worth recording: `G × F_2` of type F ⇒ G of type F, unconditionally.
  The difficulty of 1.21 is exactly `χ(Z) = 0`.
- Gersten's product formula is credited without being re-read, and the proof does not depend on it.

The open claims `f-infinity-groups-of-finite-cd-are-of-type-f` and
`some-f-infinity-group-of-finite-cd-is-not-of-type-f` record correct necessary conditions. In
particular a counterexample has no free cocompact action on an acyclic complex, so it has no
contractible Rips complex.

## 10. Problem 1.21 dictionary (z1-21-type-f-proof, ee8fcf7c0d, narrowed at feddf74880): PASS, duplicate GAP

**`g-times-z-type-f-iff-finitely-dominated-classifying-space` (+ `-proof`): PASS on content.**
- (1)⇒(2): `Y → Y×S¹ ≃ X → Y×S¹ → Y` composes to `≃ id`.
- (2)⇒(3): by Wall's Theorem 3.1(iii) (Ferry–Ranicki arXiv:math/0008070), the finite projective
  complex chain equivalent to `C_*(Ỹ)` has homology Z in degree 0, and the augmentation transports.
- (3)⇔(4): skeleton induction for fp + FP_n ⇒ F_n; dimension shifting makes `ker(F_{n−1}→F_{n−2})`
  projective at `n = cd G`.
- (3)⇒(2): Wall (iii). (2)⇒(1): Mather (Ferry–Ranicki Prop. 1.5).
- Type F ⇔ vanishing Wall class: Wall (i).

**GAP (graph hygiene, not mathematics).** This claim restates 9a (items 1, 3, 4) and 9b (the Wall-class
criterion) from the other 1.21 lane, adding only "finitely dominated `K(G,1)`". Two established
claims with the same content under different ids make both `cairn why` outputs misleading. Pick one of:
1. retarget the dictionary claim to state only the new equivalence "(1) ⇔ (2) finite domination" and
   require `g-times-z-type-f-iff-g-f-infinity-with-finite-cd` and
   `fp-type-fp-group-is-type-f-iff-wall-class-vanishes` for the rest;
2. add block-form `distinct_from` entries on the node naming both ids with one-line reasons.

Option 1 is better. The deletion of the duplicate open claim at feddf74880 is right. The READFAIL in my
watcher at that SHA was that deletion. The conditional routes into
`f-infinity-groups-of-finite-cd-are-of-type-f` (universal tester, Hsiang) require open claims and do
not fire. Their mathematics is queued for part 3.

## 11. Problem 4.05 imports and corollary (z4-05-raag-rips, 2867a9996d): PASS

**Sources re-read at arXiv HTML.**
- Li–Sánchez Saldaña arXiv:2608.24279v1:
  - the type ℛ definition matches verbatim;
  - Theorem 1.5: "Let Γ be a finite simplicial graph without triangles. Then (A_Γ, Γ^(0)) is of type
    ℛ. More precisely, for every r ≥ 2, R_r(A_Γ, Γ^(0)) is contractible.";
  - Theorems 1.3 and 1.4: amalgams and HNN extensions over finite C.
  My rendering summarized 1.3 and 1.4 without the generating-set clause on C. The node's version
  carries the extra hypothesis (the generating sets contain C∖{1}), which is the safer reading and
  vacuous for C = 1.
- Hulbert–Zaremsky arXiv:2608.25614v1: the closed convention `diam ≤ t`, and Theorem B verbatim ("If Γ
  is triangle-free then 𝒱ℛ₂(A_Γ) (using the standard word metric) is contractible."). The
  prediction `t ≥ n` for clique size n matches the node.

**Corollary `raags-with-clique-or-triangle-free-components-are-type-r` (+ `-proof`).**
- `A_Γ` is the free product of the component RAAGs with the disjoint union of generators.
- Complete components are `(Z^m, e_i)`, type ℛ by Virk; triangle-free components are type ℛ by
  Theorem 1.5.
- Induct with the free-product clause (C = 1).
- Correct. It inherits the unrefereed status of 2608.24279, and the node says so.

**Root reading.** The quote is verbatim. "Large enough parameter" = type ℛ with `r_0` depending on Γ.
The Helly remark checks out: in Z² the four unit balls at the corners of a unit square pairwise meet
and have no common point. The smallest open cases (triangle + pendant vertex = `Z³ *_Z Z²`;
`K_4` minus an edge = `F_2 × Z²`) are identified correctly.

## 12. Problem 1.03 geodesic reading (z1-03-qi-fn, ea7a1d52d4): two PASS

**12a. `fg-group-qi-to-simply-connected-geodesic-space-is-fp` (+ `-proof`): PASS.** Re-derived:
- Consecutive images of an edge loop are within `λ + c` and are joined by geodesics. A null-homotopy
  H: D² → X is uniformly continuous, so a triangulation with image-edges `< 1` exists.
- Nearest points of `f(G)` map triangles to simplices of `R_{ρ_1}(G)`, with
  `ρ_1 = λ(1 + 2C + c)` from the lower QI bound.
- Boundary vertices between `θ_i` and `θ_{i+1}` lie within `ρ_2 = λ(λ + 2c + C)` of `g_i`, so with
  `g_i`, `g_{i+1}` they span a simplex of `R_{2ρ_2}` (`ρ_2 ≥ 1` since `λ ≥ 1`).
- A simply connected Rips complex gives a finite presentation.
Properness is not used. So Problem 1.3 under the geodesic reading holds for n = 2. The root's by-yes
route still requires the all-n claim, correctly.

**12b. `short-detour-enumeration-gives-contractible-qi-2-complex` (+ `-proof`): PASS.** Re-derived:
- *Contractible.* At stage k+1 each new edge `e_i` (i ≥ 2) lies on exactly one cell `c_i` and occurs
  once in its boundary `e_1^{-1}p_i e_i`, because `p_i` avoids v. So `X_{k+1} ↘ X_k`. Later cells may
  use `e_i`, which does not matter, since each `X_k` is already contractible and compact spheres lie in
  some `X_k`.
- *Proper geodesic.* The complex is locally finite with finitely many shapes (Bridson–Haefliger
  I.7.19).
- *Quasi-isometric.* `d_X ≤ d_Γ` on vertices; crossings of a regular polygon with ≤ L+2 sides are
  replaced by boundary arcs at bounded ratio; cells are `(L+2)/2`-close to vertices.

The consequence is stated correctly. A non-F_3 group with a short-detour enumeration would answer the
geodesic reading of 1.3 negatively at n = 3, and the conditional route into
`some-non-fn-group-is-qi-to-n-connected-geodesic-space` requires the open existence claim.

The almost-convex example bullet is informational and plausible. Cannon's AC(2) ⇒ AC(k) is needed for
distance-4 pushdowns and should be cited if it becomes load-bearing.

## 13. No false establishments found in the dead routes checked in this window

- `thompson-v-quadratic-via-bounded-non-f-normal-form` is killed by the established
  `thompson-v-elements-need-unboundedly-many-non-f-letters`.
- `type-fn-hosts-via-higman-rope-trick` is killed by the established
  `higman-rope-trick-group-is-never-fp3`.
- `type-fn-hosts-via-vertex-groups-over-fp-edges` is killed by the established
  `fp-n-splittings-over-fp-n-edges-have-fp-n-vertex-groups`. I checked that proof as well:
  - Induced modules are FP_n iff the subgroup is, by the Bieri–Eckmann summand argument.
  - The Bass–Serre sequence `0 → ⊕Ind_{G_e} → ⊕Ind_{G_v} → Z → 0` makes the middle term FP_n.
  - Summands and retracts inherit FP_n.
  PASS.

The mathematics of the V obstruction (the order-break count) is queued for part 3.
