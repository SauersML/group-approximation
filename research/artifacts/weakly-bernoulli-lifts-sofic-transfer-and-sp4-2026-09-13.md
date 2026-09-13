# Weakly Bernoulli liftable actions (part 2): soficity transfer and the Sp_4(Z) instance

Lane ex2-rokhlin-almost-cocycle, 2026-09-13. Unreviewed. Part 1 is
`research/artifacts/weakly-bernoulli-lifts-extension-class-norm-2026-09-13.md` (Lemmas L and M, Theorems N and G).

## 8. Theorem S: a weakly Bernoulli lift makes the extension sofic

**Theorem S.** Let `Gamma = <S | R>` be finitely presented and sofic, `A` finite abelian, and `alpha` the class of
`1 -> A -> Gamma~ -> Gamma -> 1`. Suppose some liftable free p.m.p. `Gamma`-action `Y` is weakly contained in
`[0,1]^Gamma`. Then `Gamma~` is sofic. More precisely, for every sofic approximation `sigma_n : F_S -> Sym(V_n)` of
`Gamma` there are sofic approximations of `Gamma~` on `V_n x A`, with `A` translating the second factor and the first
factor following `sigma_n`.

*Proof.*
1. **Presentation.**
   - Fix lifts `s~` of `s in S`, and let `a_r in A` be the value of the relator `r` on the lifts. Then
     `Gamma~ = <S ∪ A | relations of A, [a, s], r = a_r (r in R)>`.
   - The group `G` so presented maps onto `Gamma~`. Killing `A` gives `Gamma`, and `A` is central in `G`, so
     `ker(G -> Gamma)` is the image of `A`. That image maps injectively into `Gamma~`, so `G ≅ Gamma~`.
2. **The lift on `Y`.**
   - By Lemma L, `Gamma~` acts on `Y x A` by `T_s(y,t) = (sy, t + b_s(sy))`, with `A` translating the second factor,
     for some `b_s in L^0(Y, A)`.
   - For each `r in R`, walking along the word `r` accumulates a sum `sum_i ±b_(s_i)(w_i y)`. The `w_i` range over a
     finite set `F_r` of suffixes. This sum equals `a_r` for a.e. `y`.
3. **Weak containment.**
   - Let `F = {1} ∪ U_r F_r` and let `P` be the partition of `Y` by `(b_s)_s in A^S`.
   - For `delta > 0`, weak containment gives `b'_s` on `Bern` whose joint law over the `F`-translates is within
     `delta` of that of `(b_s)`.
   - The failure of `r` at `x` is a union of atoms of the joined `F`-translates. So it has measure at most
     `eta = |A|^(|S||F|) delta`.
   - Approximating each `b'_s` by a block function of the coordinates in a ball `B_rho` costs at most another
     `eta` per relator.
4. **Transfer.**
   - For `L = rho + max|F|`, most `v in V_n` have a labeled `L`-ball isomorphic to the Cayley `L`-ball. Call these
     `v` good.
   - Put i.i.d. uniform labels `omega` on `V_n`. For good `v`, set `b^n_s(v)` to the block function applied to
     `omega` read through that ball isomorphism; for other `v` set it to 0.
   - At a good `v`, the failure event of each `r` has the Bernoulli law, so its probability is `<= 2 eta`. Fix
     labels `omega` with at most `3 eta |V_n| |R| + o(|V_n|)` failing pairs `(v, r)`.
5. **Permutations.**
   - Set `tau(s)(v,t) = (sigma_n(s)v, t + b^n_s(sigma_n(s)v))` and `tau(a)(v,t) = (v, t + a)`.
   - The relations of `A` and the commutators `[a, s]` hold exactly. The relation `r = a_r` holds at `(v,t)` whenever
     `v` is good and `r` does not fail at `v`.
6. **Freeness.** Let `w` be a word representing `g~ != 1`, with image `g` in `Gamma`.
   - If `g != 1`, then `sigma_n(g)` moves most `v`, so `tau(w)` moves most `(v, t)`.
   - If `g = 1`, then `g~ = a in A \ {0}`. A van Kampen diagram for `w a^-1` uses finitely many relator cells within
     a fixed radius `C_w` of the base point.
   - The accumulated `A`-value along `w` is the sum of the cell values `a_r`. It equals `a` whenever no relator fails
     within radius `C_w` of `v` and the ball is good, so `tau(w)(v,t) = (v, t + a)`.
   - The exceptional fraction is `<= |B_(C_w)| |R| 3 eta + o(1)`.
7. **Conclusion.** Letting `eta -> 0` diagonally in `n` gives a sofic approximation of `Gamma~`. QED

**Corollary S1 (Sp_4(Z)).** `E_3` is finitely presented and `Sp_4(Z)` is residually finite, hence sofic. So a liftable
free `Sp_4(Z)`-action weakly contained in Bernoulli would prove `deligne-triple-cover-is-sofic`, which is open.
Contrapositive: nonsoficity of `E_3` would prove the Sp_4(Z) instance of the target.

**Relation to Gohla--Thom.** Their Remark 3.5 is the converse mechanism for limit actions: a sofic `Gamma~` makes the
class vanish on the induced limit action. Theorem S is the Bernoulli-specific forward direction.

## 9. The Sp_4(Z) instance: one sufficient condition, and where the attempts die

- **Setup.** `Gamma(m)` is the principal congruence subgroup; for `m >= 3` it is torsionfree, with finite Borel--Serre
  models. Restricting to `Gamma(3)` loses nothing (Section 0 of part 1).
- **Congruence norm.** By Gohla--Thom Lemma 2.5 (Shapiro, isometric), the norm of `alpha` on the finite action
  `Gamma(3)/Gamma(m)` is the normalized Hamming cosystole of `alpha|Gamma(m)` on the covering model `BGamma(m)`. Call it
  `cosys(m)`.
- **Condition C.** `liminf_k cosys(3^k) > 0`, or the same along any descending chain of finite-index normal subgroups
  with trivial intersection.
- **C implies the instance.** Along such a chain, the profinite action is free and weakly contained in the chain's
  finite actions, and `Bern ≺` it (Abert--Weiss). Lemma M then gives `|||theta^Bern||| >= liminf cosys > 0`, and
  Theorem N(b) gives the instance.

**Attempts on C.**
- **(a) Property (T) controls dimension 1 only.**
  - On a finite action, a small cocycle representative of a class in `H^1(Λ, A)` makes the Schreier graph of the
    corresponding `A`-cover almost disconnected. Uniform expansion from (T) excludes this.
  - Dimension 2 needs a higher-dimensional expansion input. Gohla--Thom get it from Kaufman--Mass local-to-global
    theorems on Bruhat--Tits quotients. No simplicial model of `Gamma(m)\Sp_4(R)/U(2)` with uniformly
    coboundary-expanding links is known to the lane.
  - Recalled, not checked: higher-(T) vanishing results for real rank 2 reach unitary degree 1 only, and unitary or
    Frobenius linearizations do not bound Hamming support (compare `hamming-cosystolic-misses-hs-magnitude`).
- **(b) Cycle packing is too weak.**
  - If `sigma_1..sigma_k` are disjoint 2-cycles with `<alpha, sigma_i> != 0`, every representative meets each one, so
    `cosys >= k/#cells`.
  - A detecting cycle is a surface whose essential loops map to nontrivial elements of `Gamma(m)`, hence have length
    at least the injectivity radius `~ c log m`. A torus with `N` triangles already has a loop of length `O(sqrt N)`,
    so detecting cycles need `N >~ (log m)^2` cells.
  - Packing therefore bounds `cosys` below only by `O((log m)^-2)`, which tends to 0. It cannot prove C.
- **(c) Popa plus compactness reaches bounded complexity only.**
  - Discretize the base to `k` levels and use windows of radius `rho`. There are finitely many block functions
    `{0..k-1}^(B_rho) -> A^S`.
  - An exact trivialization among them would make `Bern(k)` liftable, hence its extension `Bern([0,1])` liftable. That
    contradicts `bernoulli-lifts-across-finite-kernels-force-virtual-splitting`.
  - So window-`(rho, k)` defects are `>= eps_(rho,k) > 0`. The instance is exactly `inf_(rho,k) eps_(rho,k) > 0`, and
    compactness does not give that.
- **(d) Local patching cannot make the defect small (heuristic, supports C).**
  - Trivialize `alpha` on pieces of diameter below the injectivity radius. The mismatches live near the walls between
    pieces.
  - `Sp_4(R)/U(2)` is non-amenable, so any tiling into bounded pieces has walls of volume comparable to the total.
    Non-local constructions are not excluded.

## 10. What a counterexample over Sp_4(Z) must look like

- **Complexity.** Block approximations whose windows or base resolution grow without bound, by (c).
- **Sofic models.** Torsor sofic approximations of `E_3` over every sofic approximation of `Sp_4(Z)`, by Theorem S.
- **Congruence covers.** `cosys -> 0` along every chain of congruence covers, by the C-route.
- **Every free action.** Norm 0 on every free p.m.p. `Sp_4(Z)`-action, by Theorem N(c).

## 11. Model tests for Theorem S

- **Hypothesis side.** For a split extension `Gamma x A`, the action `Bern x A` is a liftable weakly Bernoulli action,
  and `Gamma x A` is sofic, which is correct. No finitely presented nonsofic `Gamma~` over a sofic base is known, so
  the theorem cannot be tested against a known nonsofic group.
- **Conclusion side.** Over the Gohla--Thom lattices, Theorem G excludes weakly Bernoulli lifts. That is consistent
  with Gohla--Thom 3.13, which predicts nonsoficity under stability.
