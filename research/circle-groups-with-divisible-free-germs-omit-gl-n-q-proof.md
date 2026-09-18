---
rg: 2
id: circle-groups-with-divisible-free-germs-omit-gl-n-q-proof
kind: route
target: circle-groups-with-divisible-free-germs-omit-gl-n-q
requires: []
---

Direct proof. Not independently reviewed. Notation as in the claim: `Γ <= Homeo_+(S^1)` satisfies (DF).
`rot : Homeo_+(S^1) -> R/Z` is Poincaré's rotation number.

## Step 0. Facts about rotation numbers

Let `g, h in Homeo_+(S^1)`.

- **(R1) Conjugacy invariance.** `rot(h g h^-1) = rot(g)`.
- **(R2) Fixed points.** `rot(g) = 0` if and only if `g` has a fixed point (Poincaré).
- **(R3) Finite order.** If `g` has finite order and a fixed point, then `g = 1`. Each arc of
  `S^1 \ Fix(g)` is `g`-invariant, since its endpoints are fixed and `g` preserves orientation. On such an arc
  `g` moves every point in one direction, so no power of `g` fixes a point there.
- **(R4) Powers.** If `rot(g) = 0` and `k >= 1`, then `Fix(g^k) = Fix(g)`, by the same arc argument.
- **(R5) Abelian groups.** If `A <= Homeo_+(S^1)` is abelian, then `rot|_A : A -> R/Z` is a homomorphism.

  *Proof of (R5).* `A` is amenable, so it preserves a Borel probability measure `μ`. Let `μ~` be the lifted
  measure on `R`. For `t in R` put `F(t) = μ~([0, t))` if `t >= 0` and `F(t) = -μ~([t, 0))` if `t < 0`.
  Then `F` is nondecreasing, `F(t + 1) = F(t) + 1`, and `F(v) - F(u) = μ~([u, v))` for `u < v`. A lift `a~`
  of `a in A` preserves `μ~`, so `F(a~(v)) - F(a~(u)) = F(v) - F(u)`. Hence `F(a~(t)) - F(t) = τ(a~)` is
  independent of `t`. Hence `τ` is additive on lifts of elements of `A`. Also
  `|F(t) - t| <= 1`, so `(a~^m(t) - t)/m -> τ(a~)`. So `rot(a) = τ(a~) mod 1`, which is additive.

## Step 1. Item 1

Let `D <= Γ` be divisible with `rot|_D = 0`. By (R3), every element of finite order in `D` is trivial.
Suppose `d in D` has infinite order.

**The rank-one hull.** By divisibility choose `d_1 = d` and `d_(m+1)` in `D` with
`d_(m+1)^(m+1) = d_m`. The subgroup `D_1 = <d_1, d_2, ...>` is abelian, since each `d_m` is a power of
`d_(m+1)`. It is locally cyclic and divisible, and it is not torsion because `d` has infinite order. So
`D_1 ≅ (Q,+)`, and `rot|_(D_1) = 0`.

**A common fixed set.** For nontrivial `e, e' in D_1` there are nonzero integers `α, β` with `e^β = e'^α`
(both lie in one cyclic subgroup `<d_m>`). By (R4), `Fix(e) = Fix(e^|β|) = Fix(e'^|α|) = Fix(e')`. So every
nontrivial element of `D_1` has the same fixed set `F`. It is closed, and nonempty by (R2).

**Trivial germs on `F`.** Let `y in F`. Every `e in D_1` fixes `y`, so the right germ map
`D_1 -> G^+_y(Γ)` is a homomorphism, and its image is divisible. By (DF) the image is trivial. So each
`e in D_1` is the identity on some `[y, y + ε_e)`, and likewise on some `(y - ε'_e, y]`. Hence `y` is an
interior point of `Fix(e) = F`.

**Conclusion.** `F` is open, closed and nonempty, and `S^1` is connected, so `F = S^1`. Then `d = 1`, a
contradiction. So `D = 1`.

## Step 2. Item 2

Let `A <= Γ` be abelian and divisible, and let `s in N_Γ(A)` with `φ(a) = s a s^-1`. Define
`ψ : A -> A` by `ψ(a) = φ(a) a^-1`. It is a homomorphism because `A` is abelian, and its image `ψ(A)` is
divisible. By (R1) and (R5), `rot(ψ(a)) = rot(φ(a)) - rot(a) = 0`. By Item 1, `ψ(A) = 1`, so `s`
centralizes `A`.

## Step 3. Item 3

Let `H <= Γ'` be one of the listed groups. `H ∩ Γ` has index at most 2 in `H`, so it contains every square of
`H`, and in particular every divisible subgroup of `H`. In each case we give a divisible abelian `A <= H` and an
`s in H` whose square acts on `A` nontrivially. Then `s^2` and `A` lie in `Γ`, contradicting Item 2.

| `H` | `A` | `s` | action of `s^2` on `A` |
|---|---|---|---|
| `GL_n(Q)`, `n >= 2` | `{I + q E_12 : q in Q}` | `diag(2, 1, ..., 1)` | `q -> 4q` |
| `SL_n(Q)`, `n >= 2` | same | `diag(2, 1/2, 1, ..., 1)` | `q -> 16q` |
| `PGL_n(Q)`, `PSL_n(Q)` | the image of the same group | the image of the same `s` | `q -> 4q`, `q -> 16q` |
| `Aff(Q)` | translations `x -> x + q` | `x -> 2x` | `q -> 4q` |
| `B_2(Q)` | `{[[1,q],[0,1]]}` | `diag(2, 1)` | `q -> 4q` |
| `U_3(Q)` | `{[[1,a,c],[0,1,0],[0,0,1]]} ≅ Q^2` | `I + E_23` | `(a, c) -> (a, c - 2a)` |
| `Q x|_a Z`, `a ≠ ±1` | `Q` | the generator of `Z` | `q -> a^2 q` |

Two checks.
- The unipotent group meets the scalars trivially, so it maps isomorphically into `PGL_n(Q)` and `PSL_n(Q)`.
- In `U_3(Q)` a direct computation gives `(I + E_23)(I + aE_12 + cE_13)(I + E_23)^-1 = I + aE_12 + (c - a)E_13`, because `E_12 E_23 = E_13` and the other products vanish.

For `Q x|_(-1) Z` inside `Γ` itself, the generator lies in `Γ` and acts by `q -> -q`, which is nontrivial.
Item 2 excludes this case directly.

## Step 4. Item 4

Gluing the endpoints of `[0,1]` gives a circle on which every element of `Γ <= Homeo_+([0,1])` fixes the glued
point `p`. Right germs at `p` are right germs at `0`, and left germs at `p` are left germs at `1`. So (DF) for
the interval, including the endpoints, is (DF) for the circle, and Items 1 to 3 transfer. For
`Γ <= Homeo_+(R)`, identify `R` with `(0,1)`; the germs at `-∞` and `+∞` become the germs at the endpoints.

## Step 5. The cases in "When (DF) holds"

- **Finitely piecewise groups.** Let `γ in Stab_Γ(y)`. Take the arc of `S^1 \ B_γ` that starts at `y` (or
  contains `y`), and let `δ in Δ` be the piece of `γ` there. Then `γ = δ` on `[y, y + ε)` by continuity, and
  `δ(y) = y`. `δ` is determined by the right germ of `γ` at `y`, by the identity principle: two pieces that
  agree on `[y, y + ε)` agree on a nonempty open set. For `γ, γ'` in the stabilizer, `γ'` maps a small
  `[y, y + ε')` into `[y, y + ε)`, so the piece of `γγ'` at `y` is `δ δ'`. Thus the right germ group embeds in
  `Δ`, and it has no nontrivial divisible subgroup. The left side is the same.
  - For finitely generated piecewise-projective `Γ`, all pieces lie in the finitely generated group `Δ`
    generated by the pieces of the generators (products and inverses, as in the proof of
    `germ-extensions-omit-standard-gl-n-q`). `Δ` is linear and finitely generated, hence residually finite
    (Mal'cev). A divisible subgroup of a residually finite group is trivial, because its image in every finite
    quotient is a finite divisible group, which is trivial.
- **PL groups.** Near a fixed point `y`, a PL homeomorphism is `x -> y + λ (x - y)` on a right neighbourhood, in
  an affine chart. Composition multiplies slopes, so the right germ group at `y` embeds in the slope group
  `Λ <= R_{>0}`.
  - A finitely generated subgroup of `R_{>0}` is free abelian of finite rank.
  - `Q_{>0}` is free abelian on the primes.
  - Neither has a nontrivial divisible subgroup.

∎
