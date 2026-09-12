# Self-similarity does not lift exactly: equivariant intertwiners and amplification defects

Lane `gk-l3-corner`, 2026-09-12. Supports `self-similar-leavitt-intertwiners-have-no-exact-lift`.
It also records where the amplification route to `ternary-anti-invariant-swap-corner-is-full`
loses exactness.

## 0. Setting

- `p` is a prime and `R = L_(F_p)(1,2)`, with `t_i s_j = delta_ij` and `s0 t0 + s1 t1 = 1`.
- `G = R^x`, `k` is any field, and `S = k[G]`.
- `Theta : M_2(R) -> R`, `Theta((a_ij)) = sum_(i,j) s_i a_ij t_j`, is a unital algebra
  isomorphism with inverse `r -> (t_i r s_j)`.

For an injective homomorphism `phi : G -> G`, call `V` in `S`:

- *left phi-equivariant* if `V [g] = [phi(g)] V` for all `g` in `G`;
- *right phi-equivariant* if `[g] V = V [phi(g)]` for all `g`.

The two self-similar endomorphisms:

```text
delta(g) = s0 g t0 + s1 g t1 = Theta(g I_2),      iota(g) = s0 g t0 + s1 t1 = Theta(diag(g, 1)).
```

Both are injective, since `t0 delta(g) s0 = t0 iota(g) s0 = g`. Neither is surjective:
`u = 1 + s0 t1 = Theta([[1,1],[0,1]])` is a unit that is neither scalar nor diagonal.

At the level of `R` the Leavitt isometries intertwine them with the identity:

```text
s_i r = delta(r) s_i,     r t_i = t_i delta(r)          (r in R, i = 0, 1),
s0 g = iota(g) s0,        g t0 = t0 iota(g)             (g in G).
```

So `s_i` is a left and `t_i` a right `delta`-equivariant element of `R`, and `s0`, `t0` are
`iota`-equivariant.

## 1. No equivariant lift

**Lemma 1.1.** `G` has no proper subgroup of finite index.

*Proof.*
- `G` is perfect (`leavitt-gl-equals-el-and-perfect-unit-group`), and `PG = G/F_p^x` is
  infinite and simple (`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`).
- Let `H <= G` have finite index, and let `N` be its normal core, also of finite index. The
  image of `N` in `PG` is normal, so it is `1` or `PG`.
- If it is `1`, then `N` lies in the finite group `F_p^x` and `G` is finite, which is false.
- So `N F_p^x = G`. Then `G/N` is a quotient of `F_p^x`, hence abelian, and perfectness forces
  `N = G`. QED

**Theorem 1.2.** Let `phi : G -> G` be an injective homomorphism that is not surjective. The only
left or right `phi`-equivariant element of `k[G]` is `0`.

*Proof.* Write `V = sum_y v(y) [y]`, with `v` finitely supported.

- *Left.* `V[g] = sum_x v(x g^-1) [x]` and `[phi(g)] V = sum_x v(phi(g)^-1 x) [x]`. Equality for
  all `g`, and the substitution `x = y g`, give `v(y) = v(phi(g)^-1 y g)` for all `y, g`.
  - `g . y = phi(g) y g^-1` is an action of `G` on itself, because `phi` is a homomorphism, and
    `v` is constant on its orbits.
  - The support of `v` is finite and a union of orbits, so every orbit meeting it is finite.
  - For such a `y`, the stabilizer `{g : phi(g) = y g y^-1}` has finite index, hence equals `G`
    by Lemma 1.1.
  - Then `phi = Ad(y)` is surjective, a contradiction. So `v = 0`.
- *Right.* `[g] V = V [phi(g)]` gives `v(y) = v(g y phi(g)^-1)`. `g . y = g y phi(g)^-1` is an
  action, and the same argument gives `phi(g) = y^-1 g y` for all `g`, again a contradiction. QED

**Corollary 1.3.** No element of `k[G]` is an exact `delta`-equivariant or `iota`-equivariant lift
of `s_i`, `t_i`, `s0` or `t0`, apart from `0`. This holds even inside the anti-central summand
`S_- = eps_- S` for odd `p`: the equations read the same for `V = eps_- V`.

## 2. Where the amplification route loses exactness (p = 3)

Notation of `ternary-leavitt-swap-problem-splits-at-central-involution`: `z = -1`,
`eps_(+-) = 2(1 +- [z])`, `S_- = eps_- S`, `pi : S -> R` the Leavitt evaluation, which factors
through `S_-`. The delta-amplification (gk-l3-units' matrix-ring node) is the unital injective
homomorphism

```text
Phi : M_2(S_-) -> S_-,     Phi(x (x) E_ab) = delta(x) F_ab,
```

with `F_ab` matrix units spanned by `eps_-[1], eps_-[w], eps_-[d], eps_-[wd]`,
`w = s0 t1 + s1 t0`, `d = s0 t0 - s1 t1`.

**2.1. Amplification lifts `Theta` and carries defects injectively.** `pi(delta(x)) = delta_R(pi(x))`
and `pi(F_ab) = Theta(E_ab)`, so

```text
pi o Phi = Theta o M_2(pi).
```

At the image level `Theta` is an isomorphism. In `S_-`, `Phi` is injective and not surjective.

Take lifts with `gamma_i beta_j = delta_ij eps_- + D_ij`, where `D_ij` lies in `ker pi`. Amplifying
gives lifts in `M_2(S_-)`, and their images under `Phi` have defects `Phi(D)`. These are nonzero
whenever `D` is nonzero. So amplification never cancels a defect; it only moves the lifting problem
between `S_-` and `M_2(S_-)`.

The matrix-ring theorem already identifies those two problems: fullness of the corner is equivalent
to a unital two-pair Cohn family in `S_-`, and at every matrix size. So the recursion is stationary.

**2.2. Equivariant lifts are excluded.** The image-level Cohn family `t_i s_j = delta_ij` is
`delta`-equivariant. By Corollary 1.3 no nonzero lift of any of `s0, s1, t0, t1` is equivariant. So
an exact family in `S_-` must break `delta`-equivariance at some `g`, with the breaking terms in
`ker pi`. Uniform self-similarity cannot supply them.

**2.3. The dyadic constants are locally finite.** Put `Theta_m : M_(2^m)(R) -> R`, the depth-`m`
prefix-code isomorphism, and

```text
L = union_m Theta_m(GL_(2^m)(F_3)),
```

a directed union, since `A -> A (x) I_2` is compatible with the isomorphisms. `L` contains `z`,
`w`, `d` and every depth-`m` constant, so it contains every matrix unit the amplification uses.

`L` is locally finite, so `k[L]` is a directed union of finite-dimensional algebras and is stably
finite. Hence no one-sided pair, and in particular no Cohn family of `S_-`, has its support inside
`L`. This is a special case of the census rule that a witness together with `z` and `w` generates a
subgroup that is not `F_3`-linear sofic. It is recorded because it is exactly the part of `G` that
self-similarity reaches.

A witness needs elements of non-uniform prefix depth: prefix-code bijections between codes of
different depth profiles (Thompson-type units), or perturbations `1 + lambda S[alpha]T[beta]` with
`t_beta s_alpha = 0` that mix depths.

**2.4. The corner embedding.**
- The augmentation vanishes on `S_-`, since `eps(eps_-) = 0`. So `pi o iota` restricted to `S_-`
  is `r -> s0 pi(r) t0`, a non-unital corner map.
- `iota(eps_-) = 2(1 - [z d])` because `iota(z) = -d = z d`. It has components in both `S_+`
  and `S_-`, and `pi(iota(eps_-)) = s0 t0`.
- `iota` carries any Cohn family forward, as an algebra map, but by Corollary 1.3 it has no
  finitely supported intertwiner. So it does not realize the isometry `s0` exactly.

**2.5. The Klein splitting sees `S_+` only.**
- The adjoint evaluation `rho([g]) = g (x) (g^-1)^op` sends `z` to `1`, so it kills `S_-`.
- The operator splitting `rho(e_K) = delta_R Psi` of `projective-ternary-klein-idempotent-is-full`
  therefore carries no information about `S_-`.
- Its Kraus operators are the Leavitt isometries `s_i`, `t_i`, and Corollary 1.3 excludes their
  equivariant lifts. It is the same wall at operator level.

## 3. What is left for an exact family in `S_-`

It must:
- use group elements outside the locally finite dyadic subgroup `L`;
- break `delta`-equivariance, with all breaking terms in the evaluation kernel;
- together with `z` and `w`, generate a subgroup that is not `F_3`-linear sofic.

No construction is known. Self-similarity reduces the target (to the swap-free Cohn form and
to scalar size) but cannot close it.
