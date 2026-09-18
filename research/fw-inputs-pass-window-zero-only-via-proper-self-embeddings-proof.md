---
rg: 2
id: fw-inputs-pass-window-zero-only-via-proper-self-embeddings-proof
kind: route
title: Transfix the graph of a near-equivariant map, then count finite orbits along the shift
target: fw-inputs-pass-window-zero-only-via-proper-self-embeddings
requires: []
artifacts:
  - research/artifacts/gq-bh-bh-shell-kazhdan-rigidity-attempt.md
---

Notation as in the claim.

## Lemma T: property (T) implies FW

Let `P` have (T), `X` a `P`-set, and `M ⊆ X` commensurated.
- On the real Hilbert space `ℓ²(X)` let `pi` be the permutation representation, `pi(g)1_A = 1_(gA)`.
- Then `b(g) = 1_(gM) - 1_M` lies in `ℓ²(X)`, since `gM △ M` is finite, and it is a 1-cocycle: `b(gh) = pi(g)b(h) + b(g)`.
- By Delorme–Guichardet, (T) implies property FH for countable groups (Bekka–de la Harpe–Valette, Thm 2.12.4; not re-read here). So the affine action `xi ↦ pi(g)xi + b(g)` has a fixed point `xi_0`, and then `b(g) = xi_0 - pi(g)xi_0`.
- Hence `pi(g)(1_M + xi_0) = 1_M + b(g) + pi(g)xi_0 = 1_M + xi_0`, so `h = 1_M + xi_0` is `P`-invariant as a function on `X`.
- The set `M' = {x : h(x) > 1/2}` is `P`-invariant.
- Every `x ∈ M △ M'` has `|xi_0(x)| >= 1/2`, and there are only finitely many such `x` because `xi_0 ∈ ℓ²(X)`. `∎`

## Lemma 0 (finite changes)

If partial bijections `f, f'` from `X` to `Y` agree on a cofinite `C ⊆ dom f ∩ dom f'`, then `ind f = ind f'`.

Indeed `ind f = |Y \ f(C)| - |X \ C|`, because `f` restricts to a bijection from `dom f \ C` onto `im f \ f(C)`. `∎`

## Item 1

Let `P` act diagonally on `X × Y`, and let `G_f = {(x, f(x)) : x ∈ dom f}`.
- For `g ∈ S`, `gG_f △ G_f` is finite: `(gx, g f(x)) ∈ G_f` whenever `f(gx) = g f(x)`, which fails for only finitely many `x`. So `G_f` is commensurated.
- By FW there is a `P`-invariant `G' ⊆ X × Y` with `G' △ G_f` finite.
- Let `U ⊆ X` be the points whose fibre `G' ∩ ({x} × Y)` has exactly one element, and `V ⊆ Y` the points whose fibre `G' ∩ (X × {y})` has exactly one element. Both are `P`-invariant, since `G'` is.
- `X \ U` is finite. Every `x ∈ dom f` has a one-point fibre in `G_f`, `dom f` is cofinite, and `G'` changes only finitely many pairs. Likewise `Y \ V` is finite.
- `G'' = G' ∩ (U × V)` is invariant and is the graph of a bijection `e: U'' -> V''`, where `U'' = {x ∈ U : its partner lies in V}` and `V''` is defined symmetrically. Invariance of `G''` makes `e` equivariant, and `U''`, `V''` are invariant and cofinite.
- `e` agrees with `f` off a finite set, because `G''` and `G_f` differ in finitely many pairs.
- Put `F_X = X \ U''` and `F_Y = Y \ V''`: finite invariant sets. Then `ind f = ind e = |F_Y| - |F_X|` by Lemma 0. `∎`

## Item 2

Let `A` be an infinite orbit and `B ⊆ A` a set of vertices with finite coboundary in the Schreier graph `Gamma_A`.
- For `g ∈ S`, every point of `gB △ B` is an endpoint of a coboundary edge. So `B` is commensurated by `S`, hence by `P`.
- FW gives an invariant `B'` with `B △ B'` finite. `A` is transitive, so `B' ∈ {∅, A}`, and `B` is finite or cofinite.
- So `Gamma_A` has no finite-coboundary set that is infinite and co-infinite, that is, at most one end. It has at least one end, being infinite, connected and locally finite. `∎`

## Lemma S (orbit types are preserved)

Let `f: X ⇀ Y` be a near-equivariant partial bijection between `P`-sets. Then `f(I(X)) = I(Y)` and `f(Fin(X)) = Fin(Y)` up to finite sets.

**Proof.**
- Let `E` be the finite set of points where some defining identity fails or `f` is undefined, for some `g ∈ S^±`.
- *Orbits away from `E`.* An orbit of `X` disjoint from `E` is mapped by `f` equivariantly and injectively, hence bijectively, onto an orbit of `Y` of the same size.
- *Orbits meeting `E`.* Only finitely many orbits meet `E`. Take an infinite one, `O`. Its Schreier graph minus `E` has finitely many components, because the graph is connected and locally finite. Each infinite component is mapped along edges into a single orbit of `Y`, which is therefore infinite. The finite components and a finite orbit meeting `E` contribute finitely many points.
- So `f(I(X)) ⊆ I(Y)` up to a finite set. The same argument for `f^-1` gives the reverse inclusion. The complements then correspond too, because `dom f` and `im f` are cofinite. `∎`

## Items 3 and 4

**Two elementary facts about `psi`.**
- `I(rho∘psi^m) ⊆ I(rho)` and `Fin(rho) ⊆ Fin(rho∘psi^m)`, as subsets of `N`. A point in a finite `P`-orbit lies in a finite `psi^m(P)`-orbit.
- The window relation iterates: `s^(-m eps) rho_g s^(m eps) = rho_(psi^m(g))` near infinity for every `g` and every `m >= 0`. Both sides are homomorphisms into `NearSym(N)`, and the relation holds on generators.

**Item 3 (`eps = 1`).**
- From `rho_g s = s rho_(psi(g))` near infinity, `s` is a near-equivariant partial bijection from `X = rho∘psi` to `Y = rho`, with `ind(s) = 1`.
- **Downward closure.** By Lemma S, `I(rho) = s(I(rho∘psi)) = I(rho∘psi) + 1 ⊆ I(rho) + 1`, up to a finite set. So `I(rho)` is near downward closed: for all but finitely many `x ∈ I(rho)`, also `x - 1 ∈ I(rho)`.
- **So `I(rho)` is empty or cofinite.** Suppose `I(rho) ≠ ∅`. It is a union of infinite orbits, so it is infinite. Let `L` bound the exceptions. For every `y >= L`, pick `x >= y` in `I(rho)` and descend step by step; this puts `[L, ∞)` inside `I(rho)`, so `I(rho)` is cofinite.
- **The finite parts are finite.** Then `Fin(rho)` is finite, and by Lemma S so is `Fin(rho∘psi)`.
- **Counting finite orbits.** The equivariant bijection `e` of item 1 maps finite orbits onto finite orbits. So `|Fin(rho∘psi)| - |F_X| = |Fin(rho)| - |F_Y|`, which gives

      ind(s) = |F_Y| - |F_X| = |Fin(rho)| - |Fin(rho∘psi)| <= 0,

  by the inclusion `Fin(rho) ⊆ Fin(rho∘psi)`. This contradicts `ind(s) = 1`. Hence `I(rho) = ∅`. `∎`

**Item 4 (`eps = −1`).**
- From `s rho_g = rho_(psi(g)) s` near infinity, `s` is a near-equivariant partial bijection from `rho` to `rho∘psi`, with `ind(s) = 1`.
- **Upward closure.** By Lemma S, `I(rho) + 1 = I(rho∘psi) ⊆ I(rho)` up to a finite set. So `I(rho)` is near upward closed, and, being nonempty, infinite and closed under `+1` beyond some point, it is cofinite.
- **Counting.** So `Fin(rho)` is finite, and so is `Fin(rho∘psi)`, since it agrees with `Fin(rho) + 1` up to a finite set. Counting finite orbits as before gives `1 = ind(s) = |Fin(rho∘psi)| - |Fin(rho)|`.
- **Powers.** Applying the same argument to `s^m`, which has index `m` and intertwines `rho` with `rho∘psi^m`, gives `|Fin(rho∘psi^m)| = |Fin(rho)| + m`.
- **Not an automorphism, and infinite index.** If `psi` were an automorphism, then `Fin(rho∘psi) = Fin(rho)`. If `[P : psi(P)] = d` were finite, then `[P : psi^m(P)] = d^m` is finite, since `psi` is injective. A finite-index subgroup has only infinite orbits inside an infinite `P`-orbit, so again `Fin(rho∘psi^m) = Fin(rho)`. Both contradict the count. `∎`

## Item 5

`P` has no proper subgroup of finite index, and neither does `psi^m(P) ≅ P`. So the finite orbits of `rho` and of every `rho∘psi^m` are fixed points.

**Sign and counts.**
- The near action is faithful and `P` is infinite, so `rho` is not a union of fixed points. It therefore has an infinite orbit, and item 3 excludes `eps = 1`.
- Item 4 gives `[P : psi(P)] = ∞` and `|Fix(psi^m(P))| = |Fix(rho)| + m`.

**The sets `D_m`.**
- Put `D_m = Fix(psi^m(P)) \ Fix(rho) ⊆ I(rho)`. Then `|D_m| = m` and `D_m ⊆ D_(m+1)`, so exactly one point is added at each step.
- Let `e_m` be the equivariant bijection of item 1 for `s^m`, from `rho` to `rho∘psi^m`. It maps `I(rho)` bijectively onto `I(rho∘psi^m) = I(rho) \ D_m`, sending `P`-orbits to `psi^m(P)`-orbits.

**Transitivity on each orbit, when there are finitely many.** Suppose `rho` has finitely many orbits, and let `r` be the number of infinite ones.
- Then `psi^m(P)` has exactly `r` orbits on `I(rho) \ D_m`.
- Each infinite `P`-orbit `O` contains at least one of them.
- Hence `O \ D_m` is a single `psi^m(P)`-orbit, for every `O` and every `m`.

**One orbit collects infinitely many new points.**
- Some infinite `O` meets `D = ∪ D_m` in an infinite set.
- Order `D ∩ O` as `z_1, z_2, ...` by the step at which each point enters `D_m`.
- Since one point enters per step, each initial segment `{z_1, ..., z_i}` equals `D_m ∩ O` for some `m`.
- Then `psi^m(P)` fixes `z_1, ..., z_i` and is transitive on `O \ {z_1, ..., z_i}`.

**Conclusion.**
- So the pointwise stabilizer `P_(z_1...z_i)` is transitive on `O \ {z_1, ..., z_i}`, for every `i >= 0`.
- The standard induction then gives `k`-transitivity for every `k`: a group transitive on `O` whose point stabilizer is `(k-1)`-transitive on the complement is `k`-transitive.
- So `P` acts highly transitively on `O`. `∎`

## Item 6

- **Automorphism twists.** An automorphism twist with sign `−1` contradicts item 4, and one with sign `+1` contradicts item 3, for any input with an infinite orbit. For an infinite simple input every faithful action has one, since a union of fixed points would make the action trivial.
- **Reduced inputs.** The reduced inputs are infinite, simple and Kazhdan, hence FW by Lemma T, so item 5 applies. `∎`
