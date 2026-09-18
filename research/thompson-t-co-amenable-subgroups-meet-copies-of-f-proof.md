---
rg: 2
id: thompson-t-co-amenable-subgroups-meet-copies-of-f-proof
kind: route
title: "Restrict the invariant mean on G/H to K and average over amenable stabilizers; test T with copies of F and with the double-cover lift of PSL(2,Z)"
target: thompson-t-co-amenable-subgroups-meet-copies-of-f
requires:
  - psl2z-in-thompson-t-has-amenable-centralizers-in-v
  - thompson-f-rigid-interval-subgroups-facts
  - thompson-f-has-no-free-subgroups
---

**Conventions.**
- A mean on `ℓ^∞(Y)` is a positive linear functional `m` with `m(1) = 1`.
- If a group `G` acts on `Y`, write `(g·f)(y) = f(g^{-1}y)`. Then `m` is `G`-invariant if
  `m(g·f) = m(f)` for all `g` and `f`.
- `H ≤ G` is co-amenable if `ℓ^∞(G/H)` has a `G`-invariant mean. This is the definition used in
  `thompson-t-co-amenable-subgroup-kills-real-euler-class`.
- A group `L` is amenable if `ℓ^∞(L)` has a mean invariant under left translation,
  `(λ_l φ)(k) = φ(l^{-1}k)`.

## Step 1: invariant means with amenable stabilizers (proof of (A))

**Lemma 1.** Let `K` act on a set `Y`. Suppose `ℓ^∞(Y)` has a `K`-invariant mean and every
stabilizer `K_y` is amenable. Then `K` is amenable.

*Proof.* Let `m` be the invariant mean on `ℓ^∞(Y)`.
- Choose one point `y_i` in each `K`-orbit, and put `K_i = K_{y_i}`.
- Choose a left-invariant mean `μ_i` on `ℓ^∞(K_i)`.
- For `f ∈ ℓ^∞(K)` and `y` in the orbit of `y_i`, choose `g` with `g y_i = y`, and put
  `(Φf)(y) = μ_i(k ↦ f(g k))`.

*Well defined.* Another choice is `g' = g k_0` with `k_0 ∈ K_i`. Then
`μ_i(k ↦ f(g k_0 k)) = μ_i(k ↦ f(g k))` by left invariance of `μ_i` (translate by `k_0^{-1}`).

*Mean.* `Φ` is linear and positive, `Φ1 = 1`, and `|Φf| ≤ ‖f‖_∞`.

*Equivariance.* Let `h ∈ K`, and write `(λ_h f)(k) = f(h^{-1}k)`. If `g y_i = y`, then
`(h^{-1}g) y_i = h^{-1}y`, so
`(Φ λ_h f)(y) = μ_i(k ↦ f(h^{-1} g k)) = (Φf)(h^{-1}y) = (h·Φf)(y)`.
Hence `Φ λ_h = h·Φ`.

*Conclusion.* `M = m ∘ Φ` is a mean on `ℓ^∞(K)`, and
`M(λ_h f) = m(h·Φf) = m(Φf) = M(f)`. So `K` is amenable. ∎

**Proof of (A).** Restrict the `G`-invariant mean on `ℓ^∞(G/H)` to `K`. It is `K`-invariant.
The `K`-stabilizer of `gH` is `{k : g^{-1}kg ∈ H} = K ∩ gHg^{-1}`, which is amenable by
hypothesis. Lemma 1 applies. ∎

## Step 2: copies of F in T (proofs of (B1) and (B2))

`T` is the group of homeomorphisms of `S^1 = R/Z` that are piecewise linear with finitely many
breakpoints, all in `Z[1/2]/Z`, have slopes in `2^Z`, and map `Z[1/2]/Z` onto itself.

**Facts from the definitions.**
- An element of `T` fixing `0` is a homeomorphism of `[0,1]` fixing both ends, with the same
  properties. So `Stab_T(0) = F`.
- For a dyadic `y`, the rotation `r_y(x) = x + y` lies in `T`. So `Stab_T(y) = r_y F r_y^{-1}`.
- For dyadics `0 < a < b < 1`, write `F[a,b]` for the elements of `T` fixing
  `S^1 ∖ (a,b)` pointwise. These fix `0`, so `F[a,b]` is exactly Chaudkhari's `F[a,b] ≤ F`.

**Imports.**
- (F2) of `thompson-f-rigid-interval-subgroups-facts`, verbatim: "If $a<b$ are dyadic rationals,
  then $F[a,b]$ is isomorphic to $F$."
- `thompson-f-has-no-free-subgroups` (Brin–Squier): `F` has no non-abelian free subgroups.

**Proof of (B1).** Suppose `F` is not amenable.
1. Put `K = F[1/4,3/4] ≅ F`, which is nonamenable.
2. By (A) there is `g ∈ T` with `K ∩ gHg^{-1}` nonamenable. Conjugating,
   `g^{-1}Kg ∩ H` is nonamenable.
3. `g^{-1}Kg` fixes `g^{-1}(S^1 ∖ (1/4,3/4))` pointwise. This set contains the nonempty open arc
   `g^{-1}((3/4,1) ∪ [0,1/4))`. ∎

**Proof of (B2).** Take `K = F` in (A).
1. For `g ∈ T`, `F ∩ gHg^{-1} = g (g^{-1}Fg ∩ H) g^{-1}`.
2. `g^{-1}Fg = Stab_T(g^{-1}(0))`, and `g^{-1}(0)` is dyadic.
3. So `F ∩ gHg^{-1}` is isomorphic to the subgroup of `H` fixing the dyadic point `g^{-1}(0)`,
   which is amenable by hypothesis.
4. By (A), `F` is amenable.

For the Brin–Squier clause:
- A subgroup `S ≤ H` fixing a dyadic `y` lies in `r_y F r_y^{-1}`, so by Brin–Squier it has no
  non-abelian free subgroup.
- If every such subgroup of `H` is amenable, the hypothesis of (B2) holds.
- The three examples follow from standard facts. Tits' alternative in characteristic zero makes a
  subgroup either virtually solvable or containing `F_2`. Subgroups of virtually free groups
  without `F_2` are virtually cyclic. In a hyperbolic group, a subgroup without `F_2` is virtually
  cyclic or finite, by Gromov's classification of subgroups.
- Only the principle, and not these examples, is used downstream. ∎

## Step 3: the double-cover lift of PSL(2,Z) (proof of (B3))

**Import** (`psl2z-in-thompson-t-has-amenable-centralizers-in-v`, from Haagerup–Olesen,
Theorem 2.2). There is a homeomorphism `φ : R ∪ {∞} → R/Z` with `Λ := φ PSL(2,Z) φ^{-1} ≤ T`.
So `Λ` acts on `S^1` topologically conjugate to the Möbius action of `PSL(2,Z)` on `P^1(R)`.

**3a. Möbius facts (elementary).** Let `A ∈ SL_2(Z)` with `±A ≠ ±I` and `t = tr A`.
- If `|t| < 2`, then `t ∈ {0, ±1}`. The eigenvalues are primitive 4th, 3rd or 6th roots of
  unity, so `A^12 = I`. There is no real eigenvector, hence no fixed point on `P^1(R)`.
- If `|t| = 2`, then `±A` is conjugate to a nontrivial unipotent. It has exactly one fixed point
  and infinite order. Call it *parabolic*.
- If `|t| > 2`, the real eigenvalues are `λ^{±1}` with `|λ| ≠ 1`. It has exactly two fixed points
  and infinite order. Call it *hyperbolic*.

These properties are invariant under topological conjugacy. So for every `g ∈ T`:

(M) Every element of `gΛg^{-1}` has finite order, or has exactly one or two fixed points on
`S^1`. It has infinite order with exactly two fixed points iff it corresponds to a hyperbolic
element.

**3b. The double cover.** Let `D : S^1 → S^1`, `D(x) = 2x`, and `ρ = r_{1/2} ∈ T`. Let `C` be
the centralizer of `ρ` in `T`.
- *Descent.* For `f ∈ C` there is a unique homeomorphism `f̄` with `D ∘ f = f̄ ∘ D`. It exists
  because `Dx = Dx'` iff `x' ∈ {x, x + 1/2}`, and `f` commutes with `ρ`. Uniqueness and the rule
  `(ff')‾ = f̄ f̄'` hold because `D` is onto. So `π : C → Homeo^+(S^1)`, `f ↦ f̄`, is a homomorphism.
- *Kernel.* If `f̄ = id`, then `f(x) ∈ {x, x + 1/2}` for every `x`. By continuity `f ∈ {id, ρ}`.
  So `ker π = {1, ρ}`.
- *Lifting.* Let `ψ ∈ T`, and let `Ψ : R → R` be a lift with `Ψ(x+1) = Ψ(x) + 1`. Put
  `Ψ_2(x) = Ψ(2x)/2`.
  - `Ψ_2(x + 1/2) = Ψ_2(x) + 1/2`.
  - The slopes of `Ψ_2` are those of `Ψ`, so they lie in `2^Z`.
  - The breakpoints of `Ψ_2` are half the breakpoints of `Ψ`, so they lie in `Z[1/2]`, finitely
    many mod 1.
  - `Ψ_2(Z[1/2]) = Ψ(Z[1/2])/2 = Z[1/2]`.

  So `Ψ_2` descends to `f ∈ C`. Also `D(f(x)) = Ψ(2x) mod 1 = ψ(Dx)`, so `π(f) = ψ`. Hence
  `π(C) ⊇ T`.

(This agrees with `ι_1` of `lifted-thompson-t-quotients-are-rotation-centralizers`. It is not
imported, since the argument above is complete.)

Put `Λ̃ = π^{-1}(Λ) ≤ C ≤ T`. It maps onto `Λ ≅ PSL(2,Z)`, which contains `F_2`. So `Λ̃` is
nonamenable.
(Nonamenability of `PSL(2,Z)`: Sanov's matrices `[[1,2],[0,1]]` and `[[1,0],[2,1]]` generate a
free group of rank 2. This is standard.)

**3c. Lifts of hyperbolic elements lie in no conjugate of Λ.** Let `k ∈ Λ̃` with `ψ = π(k)`
hyperbolic, with fixed points `a ≠ b`. Choose `ã, b̃` with `Dã = a`, `Db̃ = b`. Since
`D ∘ k = ψ ∘ D`, `k` permutes `D^{-1}(a) = {ã, ã + 1/2}` and `D^{-1}(b)`.
- *Case 1: `k(ã) = ã`.* Then `k(ã + 1/2) = ã + 1/2`, since `k` commutes with `ρ`. Being an
  orientation-preserving homeomorphism fixing both ends, `k` maps the open arc
  `A = (ã, ã + 1/2)` onto itself. `D|_A` is a bijection onto `S^1 ∖ {a}`, so `A` contains exactly
  one point of `D^{-1}(b)`, say `b̃`. Then `k(b̃) ∈ A ∩ D^{-1}(b) = {b̃}`, and also
  `k(b̃ + 1/2) = b̃ + 1/2`.

  If `k(x) = x`, then `ψ(Dx) = Dx`, so `x ∈ D^{-1}{a, b}`. So `k` has exactly four fixed points.
- *Case 2: `k(ã) = ã + 1/2`.* If `k` fixed a point of `D^{-1}(b)`, then Case 1 with `a` and `b`
  exchanged would make `k` fix `ã`, a contradiction. So `k` swaps both pairs and has no fixed
  point.

In both cases `k` has infinite order, because `π(k^n) = ψ^n ≠ id`. By (M), `k ∉ gΛg^{-1}` for
every `g ∈ T`.

**3d. Subgroups of PSL(2,Z) without hyperbolic elements are amenable.** Let
`L ≤ PSL(2,Z)` contain no hyperbolic element.
- *Two parabolic fixed points.* Suppose `L` contains parabolics `P, Q` with fixed points
  `p ≠ q`. Conjugate in `PSL(2,R)` so that `p = ∞` and `q = 0`. Then
  `P = ±[[1,s],[0,1]]` and `Q = ±[[1,0],[t,1]]` with `st ≠ 0`. So `P^n Q^n` has trace
  `±(2 + n² s t)`, which is hyperbolic for large `n`. This is impossible.
- *Elliptic and parabolic.* Suppose `L` contains an elliptic `e` (finite order, nontrivial) and a
  parabolic `P` fixing `p`. Then `ePe^{-1}` is parabolic and fixes `e(p) ≠ p`, since elliptics
  have no fixed point. This reduces to the previous case, so it is impossible.
- *Some parabolic.* If `L` contains a parabolic, then all its nontrivial elements are parabolics
  with one common fixed point `p`. So `L` is conjugate into the unipotent group
  `{±[[1,s],[0,1]]} ≅ (R,+)`, and is abelian.
- *No parabolic.* Otherwise `L` is a torsion group. Let `Γ̄` be the image in `PSL(2,Z)` of
  `{A ∈ SL_2(Z) : A ≡ I mod 4}`. It is normal of finite index.
  - `Γ̄` is torsion-free. A torsion element `±A` has `tr A ∈ {0, ±1}`, while
    `A ≡ ±I mod 4` forces `tr A ≡ ±2 mod 4`.
  - So `L ∩ Γ̄ = 1`, and `L` embeds in the finite group `PSL(2,Z)/Γ̄`.

In all cases `L` is amenable.

**3e. Conclusion.** Fix `g ∈ T`, and put `S = Λ̃ ∩ gΛg^{-1}`.
- By 3c, `π(S) ≤ Λ` contains no hyperbolic element.
- By 3d, applied to `φ^{-1}π(S)φ`, the group `π(S)` is amenable.
- `ker(π|_S) ≤ {1, ρ}` is finite, so `S` is amenable.

Suppose some `H ≤ Λ` were co-amenable in `T`. Then `Λ` would be co-amenable: push the invariant
mean forward along `T/H → T/Λ`. By (A) with `K = Λ̃`, `Λ̃` would be amenable, a contradiction.
For a conjugate `cΛc^{-1}`, apply the same argument to `c^{-1}Hc`. ∎

## What this does and does not show

- (A) is a one-line restriction principle, and it is sharp: `K = H` itself is a nonamenable `K`
  whose intersection with the conjugate `H` is `H`.
- (B2) does not decide whether a witness exists. It shows that a witness from a tame class would
  prove amenability of `F`, which is open (`thompson-f-is-not-amenable`).
- The measurable analogue for (MT) witnesses `X` would read: "the `F`-action on `X` is not
  Zimmer-amenable unless `F` is amenable". It needs the theorem that Koopman representations of
  Zimmer-amenable actions are weakly contained in the regular representation (Kuhn). That theorem
  is not imported here, so the analogue is left open.
