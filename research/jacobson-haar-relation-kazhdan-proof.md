---
rg: 2
id: jacobson-haar-relation-kazhdan-proof
kind: route
title: EL_n(J) is Kazhdan, so its ergodic Haar relation is Kazhdan; the Bass-Serre tree distance of an amalgam is cnd, bounded on a piece, spread by the ergodic edge relation, and unbounded by nontriviality
target: jacobson-haar-relation-is-kazhdan-and-unsplittable
requires:
  - ershov-jaikin-kassabov-steinberg-groups-have-property-t
  - kazhdan-groupoid-cnd-criterion-and-t-h-exclusion
  - kazhdan-relations-coamenable-subrelations-locally-kazhdan
  - jacobson-haar-relation-is-laurent-affine-restriction
---

Notation is as in the target. All relations are countable Borel p.m.p. relations on standard probability spaces. "a.e."
means off an `R`-invariant null set. Such a set exists whenever a null set is given, because the `R`-saturation of a
null set is null.

## Step 1. `EL_n(J)` has property (T) for `n >= 3`

`J` is generated as a ring by `S` and `T`. `EL_n(J)` is the elementary Chevalley group `E_Φ(J)` of type
`Φ = A_(n-1)`, of rank `n - 1 >= 2`. Type `A` allows noncommutative rings. The import
`ershov-jaikin-kassabov-steinberg-groups-have-property-t` (EJK, Theorem thm:main_Steinberg, quoted there verbatim)
therefore applies: `E` has Kazhdan's property (T).

## Step 2. `R_E` is ergodic

`D_fin = x^(-1) F_2[x^(-1)]^n` is a countable subgroup of the compact abelian group `D = x^(-1) F_2[[x^(-1)]]^n`, and
it is dense in `D`: truncations converge.

For `d in D_fin`, the element `(d, 1) in A^n x| EL_n(A)` acts by `y -> y + d`. This preserves `D`. So `R_tail`, the
orbit relation of the `D_fin`-translations on `D`, is a subrelation of `R_Γ|_D`, and of both `R_+` and `R_-`, since
`(d, 1) in Γ_+ ∩ Γ_-`.

`R_tail` is ergodic. Let `f in L^2(D)` be `D_fin`-invariant, and let `χ` be a character of `D`. Then
`f^(χ) = χ(d) f^(χ)` for all `d in D_fin`, so `f^(χ) ≠ 0` forces `χ|_(D_fin) = 1`. By continuity and density this
forces `χ = 1`. So `f` is constant.

Hence `R_Γ|_D`, which contains `R_tail`, is ergodic. By `jacobson-haar-relation-is-laurent-affine-restriction`
(Theorem 1), a measure-preserving isomorphism `(D, m) -> (X_+, mu)` carries `R_Γ|_D` onto `R_E` off a countable
invariant set. That set is null, because Haar measure is diffuse. So `R_E` is ergodic: the action `E ↷ (X_+, mu)` is
ergodic and p.m.p. The space `X_+` is a diffuse standard probability space.

## Step 3. Theorem parts 1 and 2

By the import `kazhdan-groupoid-cnd-criterion-and-t-h-exclusion` (AD11 Corollary 9.4 with its verbatim one-line proof,
and AD05 Theorem 5.18):
* for an ergodic p.m.p. action of a countable Kazhdan group, `X x| Γ` has (T);
* since `X x| E` is r-discrete and ergodic, its associated relation `R_E` has (T).

AD11 Corollary 9.4, read verbatim, needs only an ergodic p.m.p. action of a countable Kazhdan group, not a free one.
It gives that `R_E` does not have (H) and is not treeable.

Property (T) (AD05 Def 4.3), ergodicity and treeability are invariant under isomorphism of measured relations up to
null sets. So all of this transfers to `R_Γ|_D`.

The co-amenability statement is `kazhdan-relations-coamenable-subrelations-locally-kazhdan`, part 3, applied to
`R = R_E`. Its hypotheses are ergodic, p.m.p., (T), and a diffuse standard space.

## Step 4. General lemma (Theorem part 3)

Let `R` be ergodic with (T), and suppose `R = R_1 *_(R_0) R_2` is a nontrivial amalgam over an ergodic `R_0`.
* Let `U` be an `R`-invariant conull Borel set on which generation and free position hold.
* Let `N_j = {x : exists y, (x,y) in R_j \ R_0}`. Nontrivial means `mu(N_1), mu(N_2) > 0`.
* Relations compose Borel-ly. For example, `{(y,w) : exists b, (y,b) in R_1, (b,w) in R_2}` is the projection of a
  Borel set with countable fibres, which is Borel by Lusin--Novikov. The same argument makes `N_j` and saturations
  Borel.

**4a. The Bass--Serre graph is a tree.** For a class `C = [x]_R` with `x in U`, define the graph `Tr_C`:
* its vertices are `C / R_1 ⊔ C / R_2`;
* `P in C/R_1` and `Q in C/R_2` are adjacent iff `P ∩ Q ≠ ∅`.
It is a simple bipartite graph.

*Connected.* Every point `q` lies in the adjacent pair `[q]_1, [q]_2`. If `(q, q') in R_j` then `[q]_j = [q']_j`.
Generation joins any two points of `C` by such steps.

*Acyclic.* Take a simple cycle `P_0, P_1, ..., P_(2m) = P_0` with `m >= 2`, distinct `P_i` for `i < 2m`, and
alternating types. Pick `a_i in P_(i-1) ∩ P_i` for `i = 1, ..., 2m`, and read indices mod `2m`. Then `a_i, a_(i+1)`
both lie in `P_i`, so `(a_i, a_(i+1)) in R_(type P_i)`.

This pair is not in `R_0`. If it were, then `a_i in [a_(i+1)]_(R_0) ⊆ P_(i+1)` and also `a_i in P_(i-1)`. Both
vertices have the same type and share a point, so `P_(i-1) = P_(i+1)`. This contradicts distinctness, since
`2m >= 4`.

So `a_1, a_2, ..., a_(2m), a_1` is a chain of length `2m` whose steps lie in `R_j \ R_0` with alternating `j`, and it
starts and ends at `a_1`, where `(a_1, a_1) in R_0`. This contradicts free position.

**4b. The tree distance is a cnd function.** Let `d` be the path metric of a tree with vertex set `V`, and `\vec E`
its oriented edges. Let `H(v) ⊆ \vec E` be the set of oriented edges pointing toward `v`.
* An edge off the geodesic `[u,v]` has `u` and `v` on the same side, so it points the same way toward both.
* An edge on `[u,v]` separates them. Each of its two orientations lies in exactly one of `H(u)`, `H(v)`.

So `|H(u) Δ H(v)| = 2 d(u,v)`. Fix `v_0` and set `h(v) = 1_(H(v)) - 1_(H(v_0))`, which lies in `l^2(\vec E)` with
finite support. Then `2 d(u,v) = ||h(u) - h(v)||^2`. If `Σ λ_i = 0`, then
`Σ_(i,j) λ_i λ_j ||h_i - h_j||^2 = -2 ||Σ λ_i h_i||^2 <= 0`.

Define `ψ(y,z) = d_(Tr_C)([y]_1, [z]_1)` for `(y,z) in R|_U` with `C = [y]_R`, and `ψ = 0` elsewhere. Check AD05 Def
5.19 on the inessential reduction `R|_U`:
* (i) `ψ(y,y) = 0`;
* (ii) `ψ` is symmetric;
* (iii) for `γ_i = (x, y_i) in G^x` we have `γ_i^(-1) γ_j = (y_i, y_j)`, and all `[y_i]_1` are vertices of the one
  tree `Tr_([x])`, so the sum is `<= 0` by the display above.

*ψ is Borel.* A path `[y]_1 = P_0, Q_1, P_1, ..., Q_k, P_k = [z]_1` gives a chain `y R_1 b_1 R_2 c_1 R_1 b_2 ... c_k R_1 z`,
with `b_i in P_(i-1) ∩ Q_i` and `c_i in Q_i ∩ P_i`. Conversely such a chain gives a walk of length `2k`. So
`{ψ <= 2k} = R_1 ∘ (R_2 ∘ R_1)^k` on `U`, which is Borel.

**4c. Bounded.** AD05 Thm 5.22 (i) => (ii) applies, since `R` is ergodic, r-discrete and (T). It gives `E` with
`mu(E) > 0` and `ψ <= c` on `R|_E`.

Let `Y` be the `R_0`-saturation of `E ∩ U`. It is `R_0`-invariant with `mu(Y) > 0`, so `mu(Y) = 1` by ergodicity of
`R_0`.

For `(z,w) in R` with `z, w in Y ∩ U`, pick `x, x' in E ∩ U` with `(x,z), (x',w) in R_0 ⊆ R_1`. Then `[z]_1 = [x]_1`
and `[w]_1 = [x']_1`, so `ψ(z,w) = ψ(x,x') <= c`.

Put `U' = U \ R.(X \ Y)`, which is invariant and conull. For a class `C` inside `U'`, every type-1 vertex is `[z]_1`
for some `z in C ⊆ Y`, so any two are within `c`. Every type-2 vertex `Q` is adjacent to `[q]_1` for `q in Q`. So
`diam Tr_C <= c + 2`.

**4d. Unbounded.** `N_j` is `R_0`-invariant: if `(x,x') in R_0` and `(x,y) in R_j \ R_0`, then `(x',y) in R_j \ R_0`.
Since `mu(N_j) > 0`, ergodicity of `R_0` gives `mu(N_j) = 1`. Put `U'' = U' \ R.(X \ (N_1 ∩ N_2))`.

Take a class `C` inside `U''` and a vertex `P in C/R_j`, and let `j'` be the other index. Pick `p in P`. Since
`p in N_j`, there is `p'` with `(p,p') in R_j \ R_0`, and then `p' in P`. The vertices `[p]_(j')` and `[p']_(j')` are
both adjacent to `P`.

They are distinct. If they were equal, `p, p', p` would be a chain of length 2 with steps in `R_j \ R_0` and
`R_(j') \ R_0` returning to `p`, which contradicts free position. So every vertex has degree `>= 2`.

In a tree with all degrees `>= 2`, non-backtracking walks of every length exist, and non-backtracking walks in a tree
are geodesics. So `diam Tr_C = ∞`, which contradicts 4c on the nonempty conull set `U''`. QED

## Step 5. The halves (Theorem part 4)

Any `R_0 ⊇ R_tail` is ergodic, because an `R_0`-invariant set is `R_tail`-invariant (Step 2). For `n >= 3`, Step 4
applies to `R = R_Γ|_D` with any such `R_0`. In particular `R_tail <= R_0 := R_+ ∩ R_-`.

Suppose `R_Γ|_D = R_+ *_(R_0) R_-`. By Step 4 the amalgam is trivial, so `R_+ = R_0` or `R_- = R_0` a.e.
* If `R_+ = R_0`, then `R_+ ⊆ R_-`, and generation gives `R_Γ|_D = R_-`.
* If `R_- = R_0`, then `R_Γ|_D = R_+`.

In either degenerate case one half is already the whole relation and nothing is glued: the soficity question is
entirely the question for that half.

Neither case is ruled out here. Note that `R_-` is a profinite-action relation (`EL_n(F_2[x^(-1)])` is integral on `D`,
so on `D` the only translations are by `D_fin`). It is not hyperfinite a priori, because the acting group is
non-amenable.

## What is and is not proved

* Proved: Theorem parts 1--4. Imports: EJK (property (T) of `EL_n` over f.g. rings, `n >= 3`) and AD05/AD11 (Def 4.3,
  Thm 5.18, Thm 5.22, Cor 9.4). Both are verbatim in the required nodes.
* The class-kill paragraph of the target is a reading of parts 2--4: it says which inputs the named permanence
  theorems need. Those theorems are not imported and nothing depends on their exact statements.
* Not proved: amalgams over non-ergodic subrelations, HNN extensions, and whether either degenerate case of Step 5
  (`R_Γ|_D = R_+` or `R_Γ|_D = R_-`) occurs.
