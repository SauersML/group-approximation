# Twin deep models: stabilizers cannot coincide macroscopically (2026-09-13)

Lane ex3-dyadic-twin-deep-approx. Unreviewed.

Notation: `A = PSL_2(Z[1/2])`, `L = PSL_2(Q_2)`, `T` its 3-regular Bruhat–Tits tree, `v_0` and
`v_1` adjacent vertices, `K = Stab_L(v_0)`, `K_1 = Stab_L(v_1)`, `C_0 = A ∩ K = PSL_2(Z)`,
`C_1 = A ∩ K_1 = gC_0g^(-1)`, `V_0 = A·v_0` (the type-0 vertices, at even distance from `v_0`).
`S = S_0 ∪ S_1` with `S_i` a finite generating set of `C_i`. For a subgroup `H <= A`, `Fix(H)` is
its fixed subtree.

## 1. Fixed trees of vertex-group subgroups

**Lemma 1.** If `H` has finite index in `C_0` (or in `C_1`, or in any `A`-conjugate of them), then
`Fix(H)` is a finite nonempty subtree.

*Proof.* `H` fixes `v_0`, so the tree is nonempty. It is convex. If it were infinite, local finiteness
and König's lemma would give a ray `[v_0, ξ)` fixed pointwise. `H` would then lie in the stabilizer
of the end `ξ`, which is a Borel subgroup of `L`, so `H` would be solvable. But `H` has finite index
in `PSL_2(Z)` and contains a nonabelian free group. ∎

The center `z(H)` of the finite tree `Fix(H)` (a vertex or an edge midpoint) satisfies
`z(aHa^(-1)) = a·z(H)`. Let `Φ` be the `A`-equivariant Markov kernel from subgroups of this class to
`V_0`: `δ_z` if `z ∈ V_0`, uniform on the three neighbours if `z` is a type-1 vertex, and the
type-0 endpoint if `z` is an edge midpoint.

## 2. A quantitative spectral gap for `A` on `ℓ^2(V_0)`

**Proposition 2.** There is `λ_A > 0` with `max_(s∈S) ||sf − f|| >= λ_A ||f||` for every
`f ∈ ℓ^2(V_0)`.

*Step (i): almost invariance forces near-radiality.* As a `C_0`-representation,
`ℓ^2(V_0) = ⊕_j ℓ^2(S_(2j)(v_0))`. `K` acts transitively on each sphere through a finite
quotient, `C_0` is dense in `K`, and the stabilizers contain `Γ(2^(2j))`. So each summand is
`ℓ^2(C_0/Π_j)` with `Π_j` congruence. Selberg's property `(τ)` for `C_0` with respect to congruence
subgroups (the import in `sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`) gives `κ_0 > 0` with
`max_(s∈S_0) ||sφ − φ|| >= κ_0 ||φ − avg φ||` on each summand. Summing over the summands,

```text
||f − P_K f||  <=  (|S_0|^(1/2) / κ_0) · max_(s∈S_0) ||sf − f||  =: c_0 · max_(s∈S_0)||sf − f||,
```

where `P_K` averages over the spheres around `v_0`. Conjugating by `g`, the same holds for `C_1`,
`P_(K_1)` and the spheres `S_(2j+1)(v_1) ∩ V_0`, with a constant `c_1`.

*Step (ii): no vector is radial around two adjacent vertices.* Let `f_0` be radial around `v_0`
with value `a_j` on `S_(2j)(v_0)`. The sphere `S_(2j+1)(v_1) ∩ V_0` consists of `2^(2j)` points at
distance `2j` from `v_0`, on the side away from `v_1`, and `2^(2j+1)` points at distance `2j+2`,
on the side of `v_1`. Each point of `V_0` occurs in exactly one such sphere. So `P_(K_1)f_0` takes the
value `b_j = (a_j + 2a_(j+1))/3` there, and

```text
||f_0 − P_(K_1) f_0||^2 = Σ_j [4^j (2/3)^2 + 2·4^j (1/3)^2] (a_j − a_(j+1))^2 = (2/3) Σ_j 4^j (a_j − a_(j+1))^2.
```

Put `x_j = 2^j a_j`. Then `4^j (a_j − a_(j+1))^2 = (x_j − x_(j+1)/2)^2`, so the sum is at least
`(||x|| − ||x||/2)^2 = ||x||^2/4`. Also `||f_0||^2 = a_0^2 + (3/2)Σ_(j>=1) 4^j a_j^2 <= (3/2)||x||^2`. Hence

```text
||f_0 − P_(K_1) f_0||  >=  (1/3) ||f_0||.                                              (R)
```

*Step (iii).* Let `max_(s∈S)||sf − f|| = δ||f||` and put `f_0 = P_K f`. `P_(K_1)f_0` is the nearest
`K_1`-radial vector to `f_0`, and `P_(K_1) f` is `K_1`-radial, so
`||f_0 − P_(K_1)f_0|| <= ||f_0 − f|| + ||f − P_(K_1)f|| <= (c_0 + c_1)δ||f||`. By (R) and
`||f_0|| >= (1 − c_0δ)||f||`, we get `δ >= 1/(4c_0 + 3c_1) =: λ_A`. ∎

(This is the quantitative form of the standard fact that `PSL_2(Z)` is not co-amenable in
`PSL_2(Z[1/2])`.)

**Corollary 3 (Reiter).** For every finitely supported probability `ν` on `V_0`,
`max_(s∈S) ||s_*ν − ν||_1 >= λ_A^2`.

*Proof.* Put `f = √ν`. Powers–Størmer gives `||sf − f||_2^2 <= ||s_*ν − ν||_1`, and `||f||_2 = 1`. ∎

## 3. Non-coincidence

**Theorem 4.** Let `W` be a finite set with actions `ρ_0` of `C_0` and `ρ_1` of `C_1`, and put
`H_i(w) = Stab_(ρ_i(C_i))(w)`. Then

```text
|{w ∈ W : H_0(w) = H_1(w)}|  <=  (1 − λ_A^2/4) |W|.
```

*Proof.* Let `p` be the coincident fraction and `μ_i` the law of `H_i(w)` for uniform `w`. Since
`H_i(ρ_i(c)w) = cH_i(w)c^(-1)`, `μ_i` is exactly invariant under conjugation by `C_i`. The coupling
through `w` gives `TV(μ_0, μ_1) <= 1 − p`. For `s ∈ S_1`,
`TV(s_*μ_0, μ_0) <= TV(s_*μ_0, s_*μ_1) + TV(μ_1, μ_0) <= 2(1 − p)`. For `s ∈ S_0` it is `0`.
Markov kernels contract total variation, so `ν = Φ_*μ_0` satisfies
`||s_*ν − ν||_1 <= 4(1 − p)` for all `s ∈ S`. Corollary 3 gives `λ_A^2 <= 4(1 − p)`. ∎

No depth hypothesis is used, and neither is the normal subgroup theorem.

## 4. Consequences for `(TD_(R,ε))`

Let `(W, ρ_0, ρ_1)` be a twin deep model, `S_Δ` the generating set of `Δ_R`, and `H ⊆ W × W` the
diagonal. At a point deep on both sides, `H_0(w) = H_1(w)` iff the two `Δ_R`-stabilizers agree, which
is the coincidence of Lemma G in `expanding-matchings-need-a-shared-stabilizer`. By Lemma G applied
orbit by orbit, with total defect at most `|S_Δ|ε|W|`:

**Corollary 5.** For every `h > 0`, at least `(λ_A^2/4 − 2ε − |S_Δ|ε/h)|W|` points `w` are deep
on both sides, have `H_0(w) ≠ H_1(w)`, and lie in a diagonal `Δ_R`-orbit of `(w,w)` whose Cheeger
constant is below `h`.

**Readings.**
* *Exact models* (`ε = 0`): every point is coincident, contradicting Theorem 4. This reproves part
  (b) of `twin-deep-vertex-models-give-homogeneous-microstates` from Selberg `(τ)` and tree geometry,
  without the normal subgroup theorem.
* *Expander ansätze are dead in all forms.* If the diagonal `Δ_R`-orbits of a family have a uniform
  Cheeger constant `h`, Corollary 5 forces `ε >= λ_A^2 h / (4(2h + |S_Δ|))`. Lemma G alone left a
  coincidence loophole; Theorem 4 closes it. Any successful family must carry a fixed fraction
  `λ_A^2/4` of its mass on non-coincident diagonal orbits with vanishing Cheeger constant, while
  being asymptotically free.
* The constant `λ_A` does not depend on `R`. Only `|S_Δ|` grows with the depth.
