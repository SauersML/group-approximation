# sk-free-2, part 2: the orbit-module actions are classified by orbits (2026-09-13)

Lane sk-free-2. Continues part 1 (`research/artifacts/sk-free-2-maximal-subgroups-2026-09-13-part1.md`), with the same setting and notation: `G = EL_3(R)`, `R = LC(X,F_2) ⋊_T Z`, X infinite minimal, `V_x` the orbit module, `Ω_x = V_x^3 ∖ {0}`, `H_x = Stab_G(δ_0 e_1)`. Status: ESTABLISHED by the proof below, UNREVIEWED.

## Theorem D
For `x, y ∈ X` the following are equivalent:
1. `H_x` and `H_y` are conjugate in `G`;
2. `Ω_x` and `Ω_y` are isomorphic `G`-sets;
3. `V_x ≅ V_y` as left `R`-modules;
4. `x` and `y` lie in one `T`-orbit.

So the conjugacy classes of the maximal subgroups `H_x` of part 1 correspond bijectively to the `T`-orbits in `X`. Every point stabilizer of `Ω_x` is conjugate to `H_x`, by transitivity.

## Proof
**(4) ⇒ (3).** If `y = T^m x`, then `δ_n ↦ δ_{n−m}` is an `R`-module isomorphism `V_x → V_y`, since `f(T^n x) = f(T^{n−m} y)`.

**(3) ⇒ (2).** An `R`-isomorphism `ψ_0 : V_x → V_y` gives the `G`-equivariant bijection `ψ_0^{⊕3}` on nonzero vectors.

**(2) ⇔ (1).** Transitive `G`-sets are isomorphic iff their point stabilizers are conjugate.

**(2) ⇒ (3).** Let `φ : Ω_x → Ω_y` be `G`-equivariant and bijective, and extend it by `φ(0) = 0`.

- *Step a: `φ` is additive.*
  - For distinct `v, w ∈ Ω_x`, let `G_{v,w}` be the pointwise stabilizer. It fixes `v`, `w` and `v + w`.
  - If `z ∉ span{v,w}`, then `(v,w,z)` is independent. By Theorem A (part 1) with `k = 3`, `G_{v,w}` is transitive on the infinite set `{z′ : (v,w,z′) independent}`, so it moves `z`.
  - Hence `Fix(G_{v,w}) = {v, w, v+w}`. Equivariance gives `G_{φv,φw} = G_{v,w}`, so `φ(v+w)` lies in `Fix(G_{φv,φw}) = {φv, φw, φv + φw}`.
  - `φ` is injective, so `φ(v+w) = φv + φw`. So `φ` is `F_2`-linear.
- *Step b: `φ` is diagonal.*
  - `e_12(r)(v_1,v_2,v_3) = (v_1 + r v_2, v_2, v_3)`, so the common fixed points of `U_12 = e_12(R)` and `U_13` in `Ω_x` are `{v : v_2 = v_3 = 0} ∖ {0}` (take `r = 1`). The same holds for `e_2` (`U_21, U_23`) and `e_3` (`U_31, U_32`).
  - `φ` maps fixed sets to fixed sets, so `φ(V_x e_i) = V_y e_i`. Being linear, `φ = diag(φ_1, φ_2, φ_3)` with `F_2`-linear bijections `φ_i : V_x → V_y`.
- *Step c: `φ` is `R`-linear.* Equivariance for `e_12(r)` on `(0, v, 0)` gives `(φ_1(r v), φ_2 v, 0) = (r φ_2 v, φ_2 v, 0)`. With `r = 1`, `φ_1 = φ_2`, and then `φ_1(r v) = r φ_1(v)` for all `r ∈ R`. So `φ_1` is an `R`-module isomorphism `V_x → V_y`.

**(3) ⇒ (4).** Let `ψ_0 : V_x → V_y` be `R`-linear and bijective, and take `z = T^n x`.
- `f δ_n = f(z) δ_n` for all `f ∈ LC(X,F_2)`. So `v = ψ_0(δ_n) = Σ_m c_m δ_m ≠ 0` satisfies `f v = f(z) v`.
- For every `m` with `c_m ≠ 0` this gives `f(T^m y) = f(z)` for all clopen indicators `f`, so `T^m y = z`.
- So the orbit of `x` lies in the orbit of `y`, and by symmetry they are equal. ∎

## Consequences and remarks
- **Corollary.** `G_X` has continuum many conjugacy classes of maximal subgroups of the form `Stab(v)`, `v ∈ Ω_x`. They are in bijection with the orbit space `X/Z`, which has cardinality continuum: each orbit is countable and `X` has cardinality continuum.
- **Structure used:** independent-triple transitivity (Theorem A); the coordinate root subgroups, which recover the coordinate decomposition; and the diagonal action of `LC(X,F_2)`, which recovers the orbit.
- **Not claimed:**
  - whether every maximal subgroup of `G_X` containing a root subgroup is a parabolic (part 1, Theorem C) or conjugate to some `H_x`;
  - the stabilizers of the non-free summands `e_1 e_W R`.
