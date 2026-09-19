---
rg: 2
id: free-compatible-wreath-actions-are-bernoulli-absorptions-proof
kind: route
title: Quotient by the off-identity coordinates, cut a clopen fundamental domain for the remaining free H-action, and spread it by the shift; read the measure off site permutations lifted through the absorption
target: free-compatible-wreath-actions-are-bernoulli-absorptions
requires: []
---

Notation as in the target. `K = H^G`, `1` is its identity, and `h_(g)` is the element of `K` equal to `h` at `g` and
`1` elsewhere. A *sliding map* is a continuous shift-equivariant map between subshifts. By Curtis-Hedlund, it has a
finite memory `M`: its output at `g` depends only on the input on `gM`. So it moves a finite change on `S` to a
change inside `S M^-1`.

**Step 1 (quotient).** Let `*` be a free compatible action, and let `K' = {k in K : k_1 = 1}`, a closed subgroup.
Then `K = K' x H_(1)`, a direct product, since distinct coordinates commute.
- `Q = A^G / K'` is compact and Hausdorff, because `K'` is compact. Let `q` be the quotient map.
- `Q` is zero-dimensional. For a clopen `C`, the saturation `K' * C` is closed, as the image of the compact set
  `K' x C`, and open, as a union of homeomorphic images of `C`. So `q(C)` is clopen.
- Given `q(u)` inside an open `V`, the compact orbit `K' * u` lies in the open set `q^-1(V)`. In the
  zero-dimensional compact space `A^G`, some clopen `C` satisfies `K' * u ⊆ C ⊆ q^-1(V)`. Then `q(C)` is a clopen
  neighbourhood of `q(u)` inside `V`.
- `H` acts on `Q` by `h q(u) = q(h_(1) * u)`. This is well defined because `H_(1)` commutes with `K'`.
- The action of `H` on `Q` is free. If `q(h_(1) * u) = q(u)`, then `h_(1) * u = k' * u` for some `k'`. By
  freeness, `k'^-1 h_(1) = 1`, so `h = 1`.

**Step 2 (clopen fundamental domain).** A free action of a finite group `H` on a zero-dimensional compact Hausdorff
space `Q` has a clopen set `D` with `Q = ⊔_{h in H} hD`.
- For each `p`, the points `hp` are distinct. So some clopen `U_p ∋ p` has the translates `hU_p` pairwise disjoint.
- Take a finite subcover `U_1, ..., U_m`. Set `D_i = U_i \ ∪_{l<i} ∪_{h} hU_l` and `D = ∪_i D_i`.
- *Disjoint.* The translates `hD_i` are pairwise disjoint because `D_i ⊆ U_i`. For `l < i`, `D_i` misses every
  `hU_l ⊇ hD_l`, so `hD_l` misses `h'D_i` for all `h, h'`.
- *Covering.* Given `p`, take the least `i` for which the orbit `Hp` meets `U_i`, say `hp in U_i`. Then `hp` lies in
  no `h'U_l` with `l < i`, so `hp in D_i`.
- Put `s̄(hp) = h` for `p in D`. It is locally constant, and `s̄(h'x) = h' s̄(x)`.

**Step 3 (decoder, (a)).** Let `s = s̄ ∘ q : A^G -> H`. Then `s` is continuous, `s(k' * u) = s(u)` for
`k' in K'`, and `s(h_(1) * u) = h s(u)`. Put `sigma(u)_g = s(lambda_g^-1 u)`.
- *Equivariant.* `sigma(lambda_a u)_g = s(lambda_{a^-1 g}^-1 u) = sigma(u)_{a^-1 g} = (a.sigma(u))_g`. Since it
  is also continuous, `sigma` is a cellular automaton `A^G -> H^G`.
- *Covariant.* By compatibility, `lambda_g^-1 (k * u) = (g^-1.k) * (lambda_g^-1 u)`, and `(g^-1.k)_1 = k_g`. Split
  `g^-1.k = (k_g)_(1) k'` with `k' in K'`. Then `sigma(k * u)_g = k_g s(lambda_g^-1 u) = k_g sigma(u)_g`.
- *Absorption.* Let `Y = sigma^-1(1)`. It is closed and shift-invariant, since `1` is shift-fixed, so it is a
  subshift. Define `Psi(u) = (sigma(u), sigma(u)^-1 * u)`. Its second coordinate lies in `Y`, since
  `sigma(sigma(u)^-1 * u) = sigma(u)^-1 sigma(u) = 1`.
- The map `(k, y) -> k * y` inverts `Psi`, because `sigma(k * y) = k`. So `Psi` is a continuous bijection of
  compact Hausdorff spaces, hence a homeomorphism.
- `Psi` is equivariant, because `(g.sigma(u))^-1 * lambda_g u = lambda_g(sigma(u)^-1 * u)`.
- `Y` meets the orbit of `u` exactly at `sigma(u)^-1 * u`: if `y` and `k * y` both lie in `Y`, then `k = 1`. So
  `|Y|` is the number of orbits.

**Step 4 (Theorem A).**
- *(2) implies (1).* Compose Step 3 with the coordinatewise relabelling `H^G -> A^G` induced by `beta^-1`. This
  commutes with the shift. Non-transitivity gives `|Y| >= 2`.
- *(1) implies (3).* Given `Psi : A^G -> A^G x Y` and any `H` of order `n`, let `k * u = Psi^-1(k . x, y)`, where
  `Psi(u) = (x, y)`. This is continuous and compatible, since translation is compatible and `Psi` is
  equivariant. It is free, since translation is free. It is not transitive, since the orbits are the sets
  `Psi^-1(A^G x {y})` and `|Y| >= 2`.
- *(3) implies (2)* is trivial.
- *(b), and (2) implies (4).* Let `c` be a constant configuration, so `lambda_g c = c`. Then
  `O_c(k) = k * c` satisfies `lambda_g O_c(k) = (g.k) * c = O_c(g.k)`. It is continuous, and injective by
  freeness. So `tau = O_c ∘ beta`, where `beta` acts coordinatewise, is an injective cellular automaton on `A^G`,
  by Curtis-Hedlund. Its image is the orbit of `c`. So it is onto iff the action is transitive.
- *(4) implies (2).* `tau` is not onto, so the orbit of `c` is not everything.

**Step 5 (Theorem B).**
- *If.* The transported action on `X` is continuous, since `tau^-1` is continuous on `X`. It is compatible:
  `lambda_g tau(k . u) = tau((g.k) . lambda_g u)`. It is transitive on `X`. If it extends to a free compatible action
  on `A^G`, then `X` is one orbit and `X != A^G`. Theorem A (2) gives an absorption.
- *Only if.* Given an absorption, use the action of Step 4, "(1) implies (3)", with `H` identified with `A` by
  `beta`. Put `tau'(x) = Psi^-1(x, y_0)`, where `y_0` is the shift-fixed point of `Y`. It exists: counting
  constants in `A^G = A^G x Y` gives `n = n |Fix_G(Y)|`. Then `tau'` is injective, and not onto since `|Y| >= 2`.
  Also `k * tau'(x) = Psi^-1(k . x, y_0) = tau'(k . x)`. So the global action extends the one transported by
  `tau'`.

**Step 6 (Theorem C (i), measure splitting).** Let `Psi = (sigma, zeta)` be an absorption. `Psi` and `Psi^-1` are
sliding maps; `Psi^-1` is defined on the subshift `A^G x Y`. Let their memories be `M` and `M'`.
- Fix `e in G` and a permutation `pi` of `A`. Let `R = Psi^-1 ∘ (pi_e x id) ∘ Psi`, where `pi_e` applies `pi` at
  site `e`. It is a homeomorphism of `A^G` of finite order, so `R^-1` is a power of `R`.
- `Psi(u)` and `Psi(R u)` differ only at `e`. So `u` and `R u` differ only inside `S = e M'^-1`.
- `(R u)|_S` depends only on `u|_{S'}`, with `S' = S ∪ S M' M` finite.
- For each context `w` on `S' \ S`, `R` therefore acts on the configurations with that context through a map
  `A^S -> A^S`. That map is a bijection, because `R` and `R^-1` fix the context. So `R` permutes the cylinders on
  every finite set containing `S'`, and `R_* mu = mu`.
- So `m = Psi_* mu` on `A^G x Y` is invariant under every `pi_e x id`. For finite `F ⊂ G`, a pattern `p` on `F`,
  and Borel `B ⊆ Y`, the number `m([p] x B)` is invariant under `Sym(A)^F`. That group is transitive on patterns.
  So `m([p] x B) = n^-|F| nu(B)`, and hence `m = mu x nu`.
- *Full support.* `mu` has full support and `Psi` is a homeomorphism, so `mu x nu` has full support. Hence so has
  `nu`.
- *No atoms.* Suppose `nu({y}) = a > 0`. The sets `Psi^-1(A^G x {g y})` are disjoint for distinct points `g y`,
  and each has measure `a`. So the orbit `G y` is finite, and `L = Stab(y)` has finite index.
  - `Fix_L(A^G)` is finite, of size `n^{[G:L]}`. `Psi` maps it bijectively onto `Fix_L(A^G) x Fix_L(Y)`. So
    `Fix_L(Y)` is a single point.
  - It contains `y` and the shift-fixed point `y_0`, so `y = y_0`.
  - Then `E = Psi^-1(A^G x {y_0})` is shift-invariant with `mu(E) = a > 0`. The Bernoulli shift over the infinite
    group `G` is mixing, hence ergodic, so `mu(E) = 1`.
  - Then `nu = delta_{y_0}`, and full support forces `Y = {y_0}`. This contradicts `|Y| >= 2`.

**Step 7 (Theorem C (ii)).**
- An isolated point `y` of `Y` has `nu({y}) > 0`, by full support. Step 6 excludes this, so `Y` is perfect.
- `Y` is compact, metrizable, zero-dimensional and nonempty, so it is a Cantor set.
- If `G y` is finite, the "no atoms" argument of Step 6 shows `y in Fix_L(Y) = {y_0}`, with `L = Stab(y)`.

**Step 8 (Theorem C (iii)).** Let `c` be a constant configuration of `A^G`.
- The set `sigma^-1(c)` is shift-invariant, because `c` is shift-fixed. `zeta` restricts to an equivariant
  homeomorphism `sigma^-1(c) -> Y`, with inverse `y -> Psi^-1(c, y)`.
- `sigma^-1(c)` is the set of `u` such that the local rule of `sigma` on `u|_{gM}` outputs `c_g` for every `g`.
  So it is a subshift of finite type, with forbidden patterns on `M`.
- `iota(y) = Psi^-1(c, y)` is continuous, equivariant (because `c` is fixed) and injective, and
  `zeta ∘ iota = id_Y`. So `Y` is an equivariant retract of `A^G`.
- *Strong irreducibility.* `Y = zeta(A^G)`, with `zeta` a sliding map of memory `M_0`. Let `y_1 = zeta(z_1)` and
  `y_2 = zeta(z_2)`, and let `E_1, E_2` be finite with `E_1 M_0 ∩ E_2 M_0 = ∅`. Take `z` equal to `z_1` on `E_1 M_0`
  and to `z_2` on `E_2 M_0`. Then `zeta(z)` agrees with `y_1` on `E_1` and with `y_2` on `E_2`.

**Step 9 (the class kill).** Each listed construction yields a `Y` that violates (i), (ii) or (iii).
- A finite, countable or isolated-point `Y` violates (ii). A countable compact `Y` has an isolated point, by Baire.
- A second finite orbit violates (ii).
- A disjoint union `Y = Y_1 ⊔ Y_2` of nonempty closed invariant sets violates (iii).
  - Both pieces are clopen in `Y`. Pick `y_i in Y_i` and a finite `F` with each cylinder `[y_i|_F]` meeting `Y`
    only inside `Y_i`.
  - Since `G` is infinite, choose `g` with `F M_0 ∩ g F M_0 = ∅`. Strong irreducibility gives `y in Y` that agrees
    with `y_1` on `F` and with `lambda_g y_2` on `gF`.
  - Then `y in Y_1`. But `lambda_g^-1 y` agrees with `y_2` on `F`, so it lies in `Y_2`. This contradicts invariance
    of `Y_1`.
