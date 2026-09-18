# Primitive shifts: a symbolic dictionary for Serre goodness (2026-09-18)

Worker `swarm-0917-w12-w12-titz-pull`, role transplanter, family symbolic dynamics,
target `every-hyperbolic-group-is-good`.

Summary. Fix a class `x ∈ H^q(G; A)` with `A` finite and `G` of type `FP_q`. We build one
shift of finite type `Σ(z)` on `G` with these properties.

- It is an affine group shift carrying an invariant Haar measure.
- It is the **terminal effacer**. The class `x` dies in `H^q(G; C(X, A))` for a compact
  Hausdorff `G`-space `X` exactly when there is a continuous `G`-map `X -> Σ(z)`.
- Its `H`-fixed points exist exactly when `res^G_H x = 0`.

So `G` is good exactly when every primitive shift has a finite orbit (§3). Every other
dynamical property of an effacer comes for free (§4). The natural density principle, that
linear SFTs have dense periodic points, is strictly stronger than goodness: on the coset
shifts of §5 it is equivalent to LERF.

Conventions.
- `G` acts on the left.
- For a `ZG`-module `F` and a `G`-module `A`, the group `Hom_Z(F, A)` is a `G`-module under
  `(g·ψ)(σ) = g·ψ(g^{-1}σ)`. Its `H`-fixed points are exactly `Hom_H(F, A)`.
- A space of configurations `B^G` (with `B` finite) has the product topology and the left
  shift `(h·v)(g) = v(h^{-1}g)`.

## 1. The primitive shift

**Setup.**
- Let `q >= 1` and let `G` be of type `FP_q`.
- Choose a free resolution `... -> F_q -> F_{q-1} -> ... -> F_0 -> Z -> 0` in which
  `F_i = ZG^{m_i}` has finite rank for every `i <= q`. It exists because `G` is `FP_q`.
- Write `e_1, ..., e_m` for the basis of `F_{q-1}` and `e'_1, ..., e'_{m'}` for the basis of
  `F_q`, and put
  `∂_q e'_i = Σ_j Σ_{s ∈ S} a_{ijs} s e_j`,
  with `S ⊂ G` finite and `a_{ijs} ∈ Z`.
- Let `A` be a finite `G`-module, and let `z ∈ Hom_G(F_q, A)` be a cocycle representing
  `x ∈ H^q(G; A)`.

**Definition.** `Σ(z) := {ψ ∈ Hom_Z(F_{q-1}, A) : ψ∘∂_q = z}`.

**Lemma 1.1 (coordinates; SFT).**
- Send `ψ` to `v_ψ ∈ (A^m)^G`, where `v_ψ(g)_j := g^{-1}·ψ(g e_j)`. This is a
  homeomorphism from `Hom_Z(F_{q-1}, A)` (topology of pointwise convergence) onto `(A^m)^G`.
- It carries the `G`-action to the left shift.
- It carries `Σ(z)` onto the set of `v` satisfying, for every `g ∈ G` and every `i`,
  `(R_i)`  `Σ_{j,s} a_{ijs} s·v(gs)_j = z(e'_i)`.
- So `Σ(z)` is a shift of finite type with window `S`. It is an affine subset of the group
  shift `(A^m)^G`.

*Proof.*
1. **Bijection.** A `Z`-linear `ψ` is determined by its values on the `Z`-basis
   `{g e_j}`, and those values are arbitrary. The map `v ↦ ψ` is the inverse. Both maps are
   continuous for the product topologies, so this is a homeomorphism.
2. **Equivariance.**
   `v_{h·ψ}(g)_j = g^{-1} h ψ(h^{-1} g e_j) = (h^{-1}g)^{-1} ψ((h^{-1}g) e_j) = v_ψ(h^{-1}g)_j`.
3. **The constraint.** `ψ∘∂_q = z` holds exactly when `ψ(g ∂_q e'_i) = g·z(e'_i)` for all
   `g` and `i`. Now `ψ(g ∂_q e'_i) = Σ a_{ijs} ψ(gs e_j) = Σ a_{ijs} gs·v(gs)_j`.
   Applying `g^{-1}` gives `(R_i)`.
4. **Invariance.** The right-hand side of `(R_i)` does not depend on `g`. So the constraint
   is invariant under the shift and is checked on the finite window `gS`. ∎

**Lemma 1.2 (nonempty torsor).**
- `Σ(z) ≠ ∅`.
- `Σ_0 := {ψ : ψ∘∂_q = 0}` is a compact abelian group shift.
- `Σ_0` acts simply transitively on `Σ(z)` by addition, and `G` acts on `Σ_0` by continuous
  automorphisms.

*Proof.*
1. The augmented resolution `F_* -> Z -> 0` is an exact complex of free abelian groups, so
   it is contractible over `Z`. Hence `Hom_Z(F_*, A)`, augmented by `Hom_Z(Z, A)`, is exact.
2. The cocycle condition `z∘∂_{q+1} = 0` says `z` is a cycle in degree `q >= 1` of this
   exact complex. So `z = ψ∘∂_q` for some `ψ`.
3. The other statements are clear, because the constraint is affine-linear and the action
   is linear. ∎

**Lemma 1.3 (invariant measure).** Transport Haar measure `m` of `Σ_0` by setting
`μ(E) := m(E - ψ_0)` for a fixed `ψ_0 ∈ Σ(z)`. Then `μ` is a `G`-invariant Borel probability
measure of full support on `Σ(z)`, and it does not depend on `ψ_0`.

*Proof.*
1. **Independence of `ψ_0`.** This follows from translation invariance of `m`.
2. **Invariance.** For `g ∈ G`,
   `μ(gE) = m(gE - gψ_0) = m(g(E - ψ_0)) = m(E - ψ_0)`. The first equality uses
   independence of the base point. The last uses that the pushforward of `m` under the
   continuous automorphism `g` of `Σ_0` is a Haar probability measure, hence equals `m`.
3. **Full support.** Haar measure has full support. ∎

## 2. The dictionary

**Theorem 2.1.** Keep the setup of §1.

- **(ii) Fixed points.** For every subgroup `H <= G`, we have `res^G_H x = 0` exactly when
  `Σ(z)^H ≠ ∅`.
- **(i) Terminal effacer.** Let `X` be a compact Hausdorff `G`-space, and let `C(X, A)` be
  the module of continuous maps `X -> A` under `(g·f)(y) = g·f(g^{-1}y)`. Let `x_X` be the
  image of `x` under the constants map `A -> C(X, A)`. Then `x_X = 0` in `H^q(G; C(X, A))`
  exactly when there is a continuous `G`-map `X -> Σ(z)`.
- In particular, `x` dies in `H^q(G; C(Σ(z), A))`.

*Proof of (ii).*
1. A point of `Σ(z)^H` is an element `ψ ∈ Hom_Z(F_{q-1}, A)^H = Hom_H(F_{q-1}, A)` with
   `ψ∘∂_q = z`.
2. `F_*` is also a free `ZH`-resolution of `Z`, so `Hom_H(F_*, A)` computes `H^*(H; A)`, and
   `z` restricted to `H` represents `res^G_H x`.
3. So such a `ψ` exists exactly when `res^G_H x` is a coboundary. ∎

*Proof of (i).*
1. **Reformulation.** Compute `H^q(G; C(X, A))` with `Hom_G(F_*, C(X, A))`. Then `x_X = 0`
   exactly when there is `c ∈ Hom_G(F_{q-1}, C(X, A))` with `c(∂_q τ)` equal to the constant
   function `z(τ)` for every `τ ∈ F_q`.
2. **From `c` to a map.** Given such `c`, put `Φ(y)(σ) := c(σ)(y)`.
   - `Φ(y)` is `Z`-linear, and `Φ(y)(∂_q τ) = z(τ)`, so `Φ(y) ∈ Σ(z)`.
   - `Φ` is continuous, because each coordinate `y ↦ c(g e_j)(y)` is continuous.
   - `Φ` is equivariant. Using `(g^{-1}·f)(y) = g^{-1}·f(g y)`,
     `(g·Φ(y))(σ) = g·c(g^{-1}σ)(y) = g·(g^{-1}·c(σ))(y) = g g^{-1}·c(σ)(gy) = Φ(gy)(σ)`.
     The second equality is `G`-linearity of `c`.
3. **From a map to `c`.** Given a continuous `G`-map `Φ`, put `c(σ)(y) := Φ(y)(σ)`.
   - `c(σ)` is continuous, since evaluation at a finite combination `σ` of basis elements
     is continuous on `Hom_Z(F_{q-1}, A)`.
   - The same computation, read backwards, shows that `c` is `G`-linear.
   - `c∘∂_q = z`, taking values in constants.
4. **The particular case.** For `X = Σ(z)`, take `Φ = id`. ∎

**Consistency check.** Take `X = G/H` with `H` of finite index. Then `C(G/H, A)` is the
coinduced module and Shapiro's lemma turns `x_X` into `res^G_H x`. Also, a `G`-map
`G/H -> Σ(z)` is the same thing as a point of `Σ(z)^H`. So (i) and (ii) agree.

**Corollary 2.2 (goodness in symbolic terms).**
1. **One class.** `x` is effaceable, meaning it dies on some finite-index subgroup, exactly
   when `Σ(z)` has a finite orbit. A finite orbit is a point with finite-index stabilizer.
2. **The group.** Let `G` be of type `FP_∞`, for example hyperbolic: hyperbolic groups are
   of type `F_∞` by the Rips complex (recalled). Then, by
   `effaceable-cohomology-makes-inflation-an-isomorphism` (Serre's criterion), `G` is good
   exactly when every primitive shift `Σ(z)` of positive degree has a finite orbit.
3. **The high-degree hole.** For `torsion-free-hyperbolic-mod-p-classes-die-virtually`
   (degree `q >= 3`, trivial `F_p`), the hole is equivalent to this: every primitive shift of
   degree `q >= 3` with trivial `F_p`-coefficients on a torsion-free hyperbolic group has a
   finite orbit. By construction, `Σ(z)` is then an `F_p`-affine SFT carrying the invariant
   Haar measure of Lemma 1.3.

*Proof.*
1. **One class.** If `x` dies on a finite-index `H`, then (ii) gives a point with stabilizer
   containing `H`. Conversely, a point with finite-index stabilizer `H` is `H`-fixed, so
   `res^G_H x = 0` by (ii).
2. **The group and the hole.** Both follow from the one-class statement. ∎

**Corollary 2.3 (odometers).** Let `X = lim← G/H_n` be a profinite odometer, the inverse
limit of finite-index subgroups `H_n`. If `x_X = 0`, then `x` is effaceable.

*Proof.*
1. Theorem (i) gives a `G`-map `Φ: X -> Σ(z)`. Its image `Y` is a closed invariant subset.
2. `Y` is a factor of an equicontinuous system, so it is equicontinuous.
3. `Y` is a subsystem of the expansive shift `(A^m)^G`, so it is expansive.
4. An equicontinuous, expansive compact metric `G`-system is finite. Here is why. Let `δ`
   be an expansivity constant. Equicontinuity gives `ε > 0` such that `d(y, y') < ε`
   implies `d(gy, gy') < δ` for every `g`. Then any two points at distance `< ε` are
   equal, so `Y` is discrete. Being compact, it is finite.
5. So `Y` is a finite invariant set, and Corollary 2.2 applies. ∎

## 3. A linear group shift whose periodic density implies effaceability

Assume that `G` is finitely generated by a finite set `T`, which holds since `G` is `FP_1`.
Let `e` be the exponent of `A`.

**Definition.**
- `Σ^+(z) ⊂ (A^m × Z/e)^G` is the set of pairs `(v, λ)` satisfying, for all `g ∈ G`,
  `t ∈ T` and `i`:
  - `λ(gt) = λ(g)`;
  - `Σ_{j,s} a_{ijs} s·v(gs)_j = λ(g)·z(e'_i)`.
- Since `G` is generated by `T`, the function `λ` is constant.
- So `Σ^+(z)` is the union, over `λ ∈ Z/e`, of the shifts `Σ(λz)` with `λ` recorded.
- It is a **group shift of finite type**: a closed shift-invariant subgroup cut out by
  finitely many local linear rules.

**Proposition 3.1.** If the periodic points (finite orbits) of `Σ^+(z)` are dense, then `x`
is effaceable.

*Proof.*
1. The set `U := {(v, λ) : λ(1) = 1}` is clopen. It is nonempty, because it contains
   `(v_{ψ_0}, 1)` from Lemma 1.2.
2. By density, `U` contains a point `(v, 1)` with finite-index stabilizer `H`.
3. Then `v ∈ Σ(z)^H`, so `res^G_H x = 0` by Theorem 2.1(ii). ∎

**Consequence.** Suppose every group shift of finite type on `G` has dense periodic points.
Then every finite-coefficient class of degree `q` on `G` is effaceable, provided `G` is
`FP_q`.

**Calibration (recalled from main, not required).**
- In `sl3z-level-three-fails-degree-two-goodness`, `Γ(3) <= SL_3(Z)` has, for all large
  primes `p`, a class `x ∈ H^2(Γ(3); F_p)` that is not effaceable. This is because
  degree-two inflation is not onto, together with Serre's criterion.
- For that class, `Σ^+(z)` is an `F_p`-linear SFT on a torsion-free, residually finite,
  linear, Kazhdan group of type F whose periodic points are **not** dense.
- `Σ(z)` is an affine SFT on the same group with an invariant Haar measure of full support
  and **no** finite orbit.
- So neither of the following is a theorem about residually finite linear Kazhdan groups:
  - periodic density for linear SFTs;
  - "measured SFTs have finite orbits".

  Any proof of goodness through either principle must use hyperbolicity in an essential way.

## 4. The obstruction: every non-periodic symbolic property is free

Call `X` an **effacer** of `x` when `x_X = 0`. By Theorem 2.1(i), `Σ(z)` is the terminal
effacer, and it already has all of the following properties.

- **SFT** (Lemma 1.1).
- **Invariant measure of full support** (Lemma 1.3).
- **Minimality.** Any minimal subsystem `M ⊂ Σ(z)` is an effacer, via the inclusion.
- **Freeness.** Let `F` be a free subshift on `G`, which exists for every countable group by
  Gao–Jackson–Seward (recalled). Then `M × F` is a free effacer, via the projection.
  Taking a minimal subsystem of `M × F` gives a free minimal effacer.
- **Expansiveness.** `Σ(z)` is a subshift.

So the existence of an effacer with any combination of these properties carries **no
information** about `x`. The single property that does carry information is a finite orbit:
by Corollary 2.2, a finite orbit is equivalent to effaceability. By Corollary 2.3, the only
kind of equicontinuous effacer that helps is one that factors onto a finite orbit.

**The step where every symbolic transplant dies.** Take a program that proves goodness of
`G` in either of these ways:
- (a) by building, for each class, a compact `G`-space `X` with a property `P` on which the
  class dies;
- (b) by proving that SFTs on `G` with property `P` have periodic points.

In case (a), the program must at some point pass from `X` to a finite-index subgroup. By
Theorem 2.1(i), that passage is exactly the existence of a periodic point in `Σ(z)`. In
case (b), the input `Σ(z)` is literally the statement of goodness.

Two further facts close the natural density principles.
- On the Γ(3) calibration above, `P ∈ {SFT, linear, measured}` fails.
- On non-LERF good groups, periodic density of linear SFTs fails (§5).

So a symbolic proof of `every-hyperbolic-group-is-good` must prove, for the specific
primitive shifts, "`Σ(z)` has a finite orbit". By (ii), that is `res^G_H x = 0` itself.
**The invariant that decides everything is the set of fixed-point subgroups
`{H : Σ(z)^H ≠ ∅}` = `{H : res^G_H x = 0}`.** No property that is invariant under passing
to effacers of `Σ(z)` sees it.

## 5. Coset shifts: linear periodic density is LERF

Let `G` be a group and `K <= G` a subgroup generated by a finite set `{k_1, ..., k_r}`. Let
`B` be a finite abelian group with `|B| >= 2`, for example `F_p`.

**Definition.** `X_K := {c ∈ B^G : c(gk) = c(g) for all g ∈ G, k ∈ K}`.

- These are exactly the functions constant on left cosets `gK`.
- The set is invariant under the left shift, because `(h·c)(gk) = c(h^{-1}gk) = c(h^{-1}g)`.
- It is cut out by the finitely many local rules `c(g k_i) = c(g)`, with window
  `{1, k_1, ..., k_r}`.
- It is a subgroup, so `X_K` is a **linear (group) shift of finite type**.

**Proposition 5.1.** The periodic points of `X_K` are dense in `X_K` exactly when `K` is
separable, meaning closed in the profinite topology of `G`.

*Proof of (⇐).*
1. **Setup.** Let `c ∈ X_K` and let `W ⊂ G` be finite. We need a periodic `c' ∈ X_K` with
   `c'|_W = c|_W`.
2. **Choosing `N`.** Let `P` be the finite set of pairs `(w, w') ∈ W^2` with `wK ≠ w'K`,
   that is, `w^{-1}w' ∉ K`. By separability, `K` is the intersection of the subgroups `KN`
   over finite-index normal `N`. So we can choose one finite-index normal `N` with
   `w^{-1}w' ∉ KN` for every `(w, w') ∈ P`.
3. **Double cosets.** For any `g`, the set `NgK = gNK` is a union of left `K`-cosets.
   Moreover, `NwK = Nw'K` holds exactly when `w^{-1}w' ∈ NK = KN`.
4. **Definition of `c'`.** Put `c' := c(w)` on `NwK` for each `w ∈ W`, and `c' := 0`
   elsewhere.
5. **Well defined.** If `NwK = Nw'K`, then `(w, w') ∉ P` by step 2, so `wK = w'K` and
   `c(w) = c(w')`.
6. **Properties.**
   - `c'` is constant on left `K`-cosets, so `c' ∈ X_K`.
   - `c'` is invariant under left translation by `N`, so its stabilizer has finite index
     and `c'` is periodic.
   - `c'` agrees with `c` on `W`. ∎

*Proof of (⇒).*
1. **Setup.** Let `g ∉ K`, and let `c := 1_K`, the function equal to `1 ∈ B` on `K` and
   `0` off `K`. Since `xk ∈ K` exactly when `x ∈ K`, we have `c ∈ X_K`.
2. **A periodic approximant.** By density there is a periodic `c' ∈ X_K` with
   `c'(1) = 1` and `c'(g) = 0`. Let `N` be the normal core of its stabilizer, a
   finite-index normal subgroup.
3. **`c'` is 1 on `NK`.** For `n ∈ N` and `k ∈ K`, we have `c'(nk) = c'(k) = c'(1) = 1`.
   The first step is left `N`-invariance and the second is `c' ∈ X_K`.
4. **Conclusion.** Since `c'(g) = 0`, we get `g ∉ NK`. Now `NK` is a finite-index subgroup
   containing `K`, so `K` is separable. ∎

**Corollary 5.2.** Let `G` be finitely generated. Suppose every linear SFT on `G` over
`F_p` has dense periodic points (call this LSP). Then every finitely generated subgroup of
`G` is separable, that is, `G` is LERF.

**Calibration (recalled, not required).**
- **Non-LERF hyperbolic groups.** By the Rips construction, there are torsion-free
  `C'(1/6)` small-cancellation groups `G` with a finitely generated normal subgroup `N` and
  quotient `G/N` a prescribed finitely presented group. Take `G/N` infinite and not
  residually finite.
  - Then `N` is not separable, since a normal subgroup is separable exactly when the
    quotient is residually finite.
  - These `G` are hyperbolic and cubulated (Wise), hence virtually compact special
    (Agol), hence residually finite.
- **Goodness of such groups.** They are good by the special cube complex route recorded in
  the Attempts of `every-hyperbolic-group-is-good`.
- **Consequence.** LSP is **strictly stronger** than goodness on hyperbolic groups. Density
  theorems of Kitchens–Schmidt type, or Fiorenzi's density for group shifts over finitely
  generated abelian groups (arXiv:1402.3448, Cor. 7.2), cannot be transplanted to
  hyperbolic groups at full strength. Only the periodic points of the specific torsors
  `Σ(z)` are relevant.
- **Existence of periodic points.** Arbitrary SFTs on one-ended hyperbolic groups need not
  have periodic points (Cohen–Goodman-Strauss–Rieck, recalled), and Kazhdan hyperbolic
  groups are one-ended. So "SFT" alone is the wrong class too.
- **Which structure could suffice (remark, not proved here).** The structure that the torsors `Σ(z)` carry and the
  counterexamples lack is the pairing of a finitely presented module `M` (the
  `(q-1)`-st syzygy) with an extension class. An affine linear SFT is a torsor for an
  extension class in `Ext^1_{F_pG}(M, F_p)` with `M` finitely presented, and it has a
  periodic point exactly when that class vanishes on a finite-index subgroup.

## 6. What survives

The only symbolic statement of the right strength is the following.

> (PS_q) For torsion-free hyperbolic `G`, every primitive shift of degree `q >= 3` with
> trivial `F_p`-coefficients has a finite orbit.

By Corollary 2.2 it is **equivalent** to `torsion-free-hyperbolic-mod-p-classes-die-virtually`,
not merely sufficient for it. Any future dynamical attack should state which feature of
`Σ(z)` beyond the ones listed in §4 it exploits. Two candidates are:
- hyperbolicity of the Cayley graph through the finiteness of the window `S`;
- the torsor structure over the syzygy shift `Σ_0`.
