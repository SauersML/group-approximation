---
rg: 2
id: contraction-trap-groups-are-sofic-proof
kind: route
title: Unfold the centralizing letter along the ascending chain into iterated centralizing HNN extensions, carry separability down the chain, and read the trap group as a locally residually finite group extended by Z
target: contraction-trap-groups-are-sofic
requires:
  - centralizing-hnn-is-residually-finite-iff-edge-is-separable
  - elek-szabo-sofic-permanence
  - sofic-implies-hyperlinear
artifacts:
  - experiments/contraction-trap-soficity-2026-09-17/stallings_trap.py
  - experiments/contraction-trap-soficity-2026-09-17/output.txt
---

The notation follows the target. `F` is finitely generated and residually finite, and `phi : F -> F` is
injective. Put `H_j = phi^j(F)`, so that `F = H_0 ⊇ H_1 ⊇ H_2 ⊇ ...`. Each `H_j` is closed in the
profinite topology of `F`. "Closed" always means closed in the profinite topology of the ambient group
named; for a residually finite ambient group, every finite subset is closed. For `K` a group and `L <= K`,
write

```text
HNN(K, L) = < K, v | [v, l] = 1  (l in L) >,
r : HNN(K, L) -> K,   v -> 1   (the retraction).
```

## Classical inputs

* **(B) Britton's lemma** (Lyndon-Schupp, *Combinatorial Group Theory*, IV.2.1). In an HNN extension
  `< K, v | v a v^(-1) = alpha(a), a in A >`, a word `k_0 v^(n_1) k_1 ... v^(n_s) k_s` with `s >= 1`, all
  `n_i != 0`, and no pinch is `!= 1`. A pinch is `v k_i v^(-1)` with `k_i in A`, or `v^(-1) k_i v` with
  `k_i in alpha(A)`. The base `K` embeds. For `HNN(K, L)` both associated subgroups are `L`.
* **(H) M. Hall** (*Coset representations in free groups*, Trans. AMS 67 (1949)). Every finitely generated
  subgroup of a free group is closed. This is used only to confirm the hypothesis of the target for free
  `F`, since `phi^j(F)` is finitely generated.
* **(CS1)** `centralizing-hnn-is-residually-finite-iff-edge-is-separable`. For `K` residually finite and
  `L <= K`, `HNN(K, L)` is residually finite iff `L` is closed in `K`.
* **(ES)** `elek-szabo-sofic-permanence`. Sofic groups are closed under subgroups and direct limits, and
  `N ◁ G` with `N` sofic and `G/N` amenable gives `G` sofic. Residually finite groups are sofic.
* **(SH)** `sofic-implies-hyperlinear`.

## Step 1. Separability passes down the edge of a centralizing HNN extension

**Lemma A.** Let `K` be residually finite, `L <= K` closed, `Gamma = HNN(K, L)`, and `L' <= L` a subgroup
that is closed in `K`. Then `Gamma` is residually finite, and `L'` is closed in `Gamma`.

*Proof.* `Gamma` is residually finite by (CS1).

Let `x in Gamma \ L'`. We find a finite quotient of `Gamma` in which the image of `x` is outside the image
of `L'`.

For a finite-index normal subgroup `N ◁ K`, put `K_N = K/N` and `L_N = LN/N`, and form
`Gamma_N = HNN(K_N, L_N)`. The quotient map `K -> K_N` sends the relators `[v, l]` to relators, so it
extends to `theta_N : Gamma -> Gamma_N` with `v -> v`. Also `r_N theta_N = theta_N r`, where `r_N` is the
retraction of `Gamma_N`. `K_N` is finite and `L_N` is a finite subgroup, so it is closed. Hence (CS1)
makes `Gamma_N` residually finite.

*Case 1: `r(x) notin L'`.* `L'` is closed in `K`, so there is `N` with `r(x) notin L'N`. The composite
`Gamma -> K -> K/N` sends `L'` into `L'N/N` and `x` outside it.

*Case 2: `r(x) = l in L'`.* Put `y = x l^(-1)`. Then `r(y) = 1`, and `y != 1` because `x notin L'`.
* **`y` has a stable letter.** Write `y = k_0 v^(n_1) k_1 ... v^(n_s) k_s` with all `n_i != 0` and `s`
  minimal. Then `k_i notin L` for `0 < i < s`: otherwise `k_i` commutes with `v`, and
  `v^(n_i) k_i v^(n_(i+1)) = k_i v^(n_i + n_(i+1))` shortens the form. If `s = 0`, then `y = k_0 in K`
  and `k_0 = r(y) = 1`, a contradiction. So `s >= 1`.
* **Choice of `N`.** `L` is closed in `K`. So for each of the finitely many `k_i` (`0 < i < s`) there is
  a finite-index normal subgroup `N_i` with `k_i notin L N_i`. Let `N` be their intersection.
* **`y` survives in `Gamma_N`.** The image `theta_N(y) = k̄_0 v^(n_1) k̄_1 ... v^(n_s) k̄_s` has
  `k̄_i notin L_N` for `0 < i < s`. So it has no pinch, and by (B) in `Gamma_N`, `theta_N(y) != 1`.
* **`x` avoids `L'` in `Gamma_N`.** Suppose `theta_N(x) = theta_N(y) theta_N(l)` lay in `theta_N(L')`,
  which is contained in `K_N`. Then `theta_N(y)` would lie in `K_N`. But `r_N(theta_N(y)) = theta_N(r(y)) = 1`,
  and `r_N` is the identity on `K_N`. So `theta_N(y) = 1`, a contradiction.
* **Finishing.** `theta_N(L')` is a finite subgroup of the residually finite group `Gamma_N`, so it is
  closed. A finite quotient of `Gamma_N` therefore separates `theta_N(x)` from `theta_N(L')`. Composing
  with `theta_N` gives the required quotient of `Gamma`. ∎

## Step 2. The unfolded kernel groups are residually finite

For `0 <= m <= infinity`, define

```text
M_m = < F, e_0, e_1, ..., e_m | [e_j, h] = 1   (h in H_j, 0 <= j <= m) >
```

(for `m = infinity`, the indices `j` range over all of `N`). Then `M_0 = F x <e_0>`, and
`M_m = HNN(M_(m-1), H_m)` with stable letter `e_m`. Here `H_m` means its image in `M_(m-1)`, and
`F -> M_(m-1)` is injective by induction and (B). `M_infinity` is the directed union of the `M_m`.

**Lemma B.** For every finite `m`, `M_m` is residually finite, and every `H_j` with `j > m` is closed in `M_m`.

*Proof.* Induction on `m`.

*Base `m = 0`.* `F x Z` is residually finite. Let `(f, n) notin H_j x {0}`.
* If `n != 0`, the projection to `Z/(2|n|)` separates `(f, n)` from `H_j x {0}`.
* If `n = 0`, then `f notin H_j`. Since `H_j` is closed in `F`, a finite quotient `F -> Q` separates `f`
  from `H_j`, and `F x Z -> Q` does the same for `(f, 0)` and `H_j x {0}`.

*Step `m-1 -> m`.* By induction, `M_(m-1)` is residually finite and `H_m` is closed in it. For `j > m`,
`H_j ⊆ H_m`, and `H_j` is closed in `M_(m-1)`. Lemma A, applied with `K = M_(m-1)`, `L = H_m` and
`L' = H_j`, gives that `M_m` is residually finite and `H_j` is closed in `M_m`. ∎

By (B), each `M_(m-1) -> M_m` is injective, so `M_infinity` is a directed union of the residually finite
groups `M_m`.

## Step 3. The trap group is an ascending HNN extension of `M_infinity`

**Subgroup fact (from (B)).** Let `K' <= K` and `L <= K'`. Then the natural map `HNN(K', L) -> HNN(K, L)`
is injective. A pinch `v^(±1) k v^(∓1)` with `k in K'` has the same condition, `k in L`, in both groups. So
a word that is pinch-free in `HNN(K', L)` is pinch-free in `HNN(K, L)`, and (B) makes it `!= 1` there.

**The shift `psi`.** Define `psi : M_infinity -> M_infinity` by `psi(x) = phi(x)` for `x in F` and
`psi(e_j) = e_(j+1)`. The relator `[e_j, h]` with `h in H_j` goes to `[e_(j+1), phi(h)]`, and
`phi(h) in H_(j+1)`. So `psi` is a homomorphism.

**`psi` is injective.** For `k >= 0`, let `Q_k` be the abstract group
`< H_1, e_1, ..., e_k | [e_j, h] = 1  (h in H_j, 1 <= j <= k) >`, so that `Q_0 = H_1`. Since `phi : F -> H_1`
is an isomorphism with `phi(H_j) = H_(j+1)`, it induces `M_m ≅ Q_(m+1)`. Under this isomorphism,
`psi|M_m` becomes the natural map `iota_(m+1) : Q_(m+1) -> M_(m+1)`. We show by induction that every
`iota_k` is injective.
* `iota_0 : H_1 -> F x <e_0>` is the inclusion.
* For `k >= 1`, `Q_k = HNN(Q_(k-1), H_k)` and `M_k = HNN(M_(k-1), H_k)`, both with stable letter `e_k`.
  By induction `iota_(k-1)` embeds `Q_(k-1)`, and its image contains `H_1 ⊇ H_k`. So the subgroup fact
  applies, and `iota_k` is injective.

Hence `psi` is injective on each `M_m`, and so on `M_infinity`.

**Tietze moves.** Let `A = < M_infinity, t | t y t^(-1) = psi(y)  (y in M_infinity) >`. Define two maps:
* `alpha : T -> A` by `x -> x` (`x in F`), `e -> e_0`, `g -> t`. The relators hold, since
  `t x t^(-1) = psi(x) = phi(x)`, and `[e_0, x] = 1` because `H_0 = F`.
* `beta : A -> T` by `x -> x`, `e_j -> g^j e g^(-j)`, `t -> g`. In `T`, `g^j F g^(-j) = phi^j(F) = H_j`.
  So `g^j e g^(-j)` commutes with `H_j`, and conjugation by `g` realises `psi` on the generators.

`beta alpha` is the identity on `F`, `e` and `g`. `alpha beta (e_j) = t^j e_0 t^(-j) = psi^j(e_0) = e_j`.
So `T ≅ A`, an ascending HNN extension of `M_infinity` along the injective endomorphism `psi`. By (B),
`M_infinity` embeds in `T`.

## Step 4. CT1: soficity

In `A`, `t m = psi(m) t` and `m t^(-1) = t^(-1) psi(m)`. So the set `{ t^(-r) m t^s : r, s >= 0, m in M_infinity }`
is closed under products and inverses. It contains the generators, so it is all of `A`. The homomorphism
`A -> Z` with `t -> 1` sends `t^(-r) m t^s` to `s - r`. Its kernel is therefore

```text
K = union over r >= 0 of  t^(-r) M_infinity t^r,
```

an increasing union, because `t M_infinity t^(-1) = psi(M_infinity) ⊆ M_infinity`.
* Each `t^(-r) M_infinity t^r ≅ M_infinity` is a directed union of residually finite groups (Steps 2
  and 3). So `K` is a directed union of residually finite groups.
* Residually finite groups are sofic. By (ES), `K` is sofic, being a direct limit of sofic groups.
* `T/K ≅ Z` is amenable, so (ES) makes `T` sofic. The section `1 -> g` gives `T = K ⋊ <g>`.
* By (SH), `T` is hyperlinear. ∎ (CT1)

## Step 5. CT2: the trap is exact

`T = < B, g | g x g^(-1) = phi(x)  (x in F) >` is an HNN extension of `B = F x <e>` with associated
subgroups `F` and `phi(F)`. Let `x in F \ phi(F)`. Then

```text
w_x = [e, g^(-1) x g] = e · g^(-1) · x · g · e^(-1) · g^(-1) · x^(-1) · g .
```

The three possible pinches are all absent:
* `g^(-1) x g` would need `x in phi(F)`;
* `g e^(-1) g^(-1)` would need `e^(-1) in F`, which is false in `F x <e>`;
* `g^(-1) x^(-1) g` would need `x^(-1) in phi(F)`.

By (B), `w_x != 1`.

Let `theta : T -> Q` with `Q` finite. Then `theta(g) theta(F) theta(g)^(-1) = theta(phi(F)) ⊆ theta(F)`.
Both sides have the same finite cardinality, so they are equal. Then `theta(g^(-1) x g) in theta(F)`,
which commutes with `theta(e)`, so `theta(w_x) = 1`.

So `T` is not residually finite. When `F` is free of finite rank, `T` is finitely presented. For a finitely
presented group, a local embedding into a finite group of a finite set containing the generators, the
relator prefixes and a given element is a homomorphism that is nontrivial on that element. So LEF implies
residually finite, and `T` is not LEF. ∎ (CT2)

## Step 6. CT3: the EL_3(J) trap

`stallings_trap.py` folds the six loops `phi_C(a1), ..., phi_C(d)` at a base vertex. The folded core graph
has 16 vertices and 21 edges, so `H_1 = phi_C(F_6)` is free of rank `21 - 16 + 1 = 6`. The script also
checks that the folded graph reads each image.
* **Injective.** `phi_C : F_6 -> H_1` is a surjection between free groups of rank 6. Composed with an
  isomorphism `H_1 ≅ F_6`, it is a surjective endomorphism of `F_6`, which is injective because finitely
  generated free groups are Hopfian.
* **Proper.** The graph does not read `a1`, so `a1 notin H_1`.
* **Infinite index.** The graph is not a covering, so the index is infinite.

`F_6` is residually finite, and by (H) every `phi_C^j(F_6)` is closed. Steps 4 and 5 therefore apply:
`Gamma_3 = T(F_6, phi_C)` is sofic and hyperlinear, and `w = [e, g^(-1) a1 g] != 1` in it. ∎ (CT3)

**Class kill.** A sofic approximation `sigma_n` of `T(F, phi)` satisfies
`Hamming(sigma_n(w_x), id) -> 1` for every `w_x != 1`. In any argument that uses only the relations of the
certificate, the step "the witness dies in every sofic model" is therefore contradicted by the universal
group. The same holds in the hyperlinear setting with `tau(sigma_n(w_x)) -> 0`, by (SH).
