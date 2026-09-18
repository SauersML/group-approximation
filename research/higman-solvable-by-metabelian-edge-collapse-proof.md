---
rg: 2
id: higman-solvable-by-metabelian-edge-collapse-proof
kind: route
title: Tracking finite-rank error terms through the two-sided module argument lets the metabelian collapse run over any finite-Hirsch-length solvable second derived subgroup
target: solvable-by-metabelian-edge-images-collapse-higman-quotients
requires:
  - nontrivial-higman-quotients-keep-all-four-bs-subgroups
  - nilpotent-edge-images-collapse-higman-quotients
  - virtually-metabelian-edge-images-collapse-higman-quotients
artifacts:
  - experiments/higman-solvable-by-metabelian-2026-09-17/README.md
---

Conventions: `x^y = y^-1 x y` and `[x,y] = x^-1 y^-1 x y = x^-1 x^y`. The rank of an abelian group `U`
is `dim_Q (U ⊗ Q)`. For a solvable group `S`, `h(S)` is the Hirsch length. We use the standard
facts (Lennox--Robinson, *The theory of infinite soluble groups*, §1.3):
- **(H1) Additivity.** `h(S) = h(K) + h(S/K)` for `K ⊴ S`.
- **(H2) Monotonicity.** `h(T) <= h(S)` for `T <= S`, and `h` is invariant under isomorphism.
- **(H3) Abelian images.** The image of `S` under a homomorphism to an abelian group has rank at
  most `h(S)`. This is (H1) together with the fact that an abelian group has `h` equal to its rank.

We also use one module fact.
- **(M) Cyclic modules.** A cyclic module over the PID `Q[T^±1]` is either finite-dimensional over `Q`
  or free of rank 1. On a free one, `f(T)` is injective for every nonzero `f`.

Let `Q = H4/R` with `Q != 1`, and write `a, b, c, d` for the images. They have infinite order
(`nontrivial-higman-quotients-keep-all-four-bs-subgroups`, item 1). Fix `m >= 1`, and put

```text
alpha = a^m,  gamma = c^m,  P = 2^m,  A = <alpha, gamma>,  N = A'',  z = [gamma, alpha] = gamma^-1 gamma^alpha.
```

**Assume** `N` is solvable with `h(N) < ∞`. Then `A` is solvable, since `A/N` is metabelian. We derive
`Q = 1`.

Put `V = (A'/N) ⊗ Q`, which is a `Q`-vector space because `A'/N = A'/A''` is abelian. The group `A`
acts on `V` by conjugation through `A/A'`. Let `X` and `Y` be the commuting operators induced by
`alpha` and `gamma`, and let `zbar` be the image of `z`.

## Step 1 (relations)

This is Step 1 of `higman-metabelian-edge-collapse-proof`. Conjugation `phi` by `g = b^P` is an
injective endomorphism of `Q`, with `phi(gamma) = gamma^(2^P)` and `phi(gamma^alpha) = (gamma^alpha)^2`.
Conjugation `phi'` by `g' = d^P` satisfies `phi'(alpha) = alpha^(2^P)` and `phi'(alpha^gamma) = (alpha^gamma)^2`.

## Step 2 (the `b` side: the `Y`-span of `zbar` is finite-dimensional)

**Setup.**
- Let `M = <gamma, gamma^alpha> = <gamma, z>`.
- Let `W = < z^(gamma^j) : j in Z >`. Then `W <= A'`, so `W' <= A'' = N`.
- `W` is normalized by `gamma^(±1)` and contains `z`, so `W ⊴ M`, `M = <gamma> W`, and `M/W` is cyclic.
- Let `V_W ⊆ V` be the `Q`-span of the image of `W`. It equals `span_Q { Y^j zbar : j in Z }`, which is a
  cyclic `Q[Y^±1]`-module. By flatness of `Q`, `dim V_W` is the rank of `WN/N`, so `dim V_W <= h(W)` by (H3).

**Claim.** `V_W` is finite-dimensional.

*Proof.*
1. **`phi(z)`.** From `gamma^alpha = gamma z` and the free-group identity `(gamma z)^2 = gamma^2 z^gamma z`
   (checked in `identities.g`):

   ```text
   phi(z) = phi(gamma)^-1 phi(gamma^alpha) = gamma^(-2^P) (gamma z)^2 = gamma^e w_0,   e = 2 - 2^P != 0,   w_0 = z^gamma z in W.
   ```

   Also `phi(M) <= M`, since `phi(gamma)` and `phi(gamma^alpha)` are powers of the generators.
2. **The intersection `D`.** Let `D = phi(W) ∩ W`. Since `W ⊴ M` and `phi(W) <= M`, `D` is normal in
   `phi(W)`, and `phi(W)/D ≅ phi(W)W/W <= M/W` is cyclic. By (H1), (H2) and the injectivity of `phi`,

   ```text
   h(W) = h(phi(W)) <= h(D) + 1.
   ```

3. **Splitting `h(D)`.** By (H1), `h(D) = h(D ∩ N) + h(D/(D ∩ N)) <= h(N) + dim V_D`. Here `V_D ⊆ V_W` is the
   `Q`-span of the image of `D`, because `D/(D∩N) ≅ DN/N` is abelian.
4. **Commutator estimate.** Put `k = phi(z) = gamma^e w_0`, so `gamma^e = k w_0^-1`. Take `w in D`. The
   free-group identity `[w, k u^-1] = [w, u^-1] · [w, k]^(u^-1)`, with `u = w_0` (checked in `identities.g`),
   gives

   ```text
   [w, gamma^e] = [w, w_0^-1] · beta,    beta = [w, k]^(w_0^-1).
   ```

   - Since `w, w_0 in W`, `[w, w_0^-1] in W' <= N`.
   - Since `w, k in phi(W)`, `[w,k] in phi(W)' = phi(W')`, so `beta in B := phi(W')^(w_0^-1)`. `B` is
     isomorphic to `W' <= N`, so `B` is solvable with `h(B) <= h(N)`.
   - `[w, gamma^e] in A'`, because `w in A'` and `A' ⊴ A`. Also `[w, w_0^-1] in N <= A'`. Hence `beta in A' ∩ B`.

   In `V` this reads `(Y^e - 1) wbar = betabar`. Let `U ⊆ V` be the span of the image of `A' ∩ B`. By (H3)
   and (H2), `dim U <= h(A' ∩ B) <= h(N)`. So `(Y^e - 1) V_D ⊆ U`.
5. **Conclusion.** By (M), `V_W` is either finite-dimensional, and we are done, or free. Suppose it is
   free. Then `Y^e - 1` is injective on `V_W`, since `e != 0`, and `V_D ⊆ V_W`, so
   `dim V_D <= dim U <= h(N)`. By steps 2–3, `h(W) <= 1 + 2 h(N)`, so `dim V_W <= h(W) < ∞`. This
   contradicts freeness. ∎

So `Y` has a nonzero minimal polynomial `p` on `V_W`, and `p(Y) zbar = 0`.

## Step 3 (the `d` side: the `X`-span of `zbar` is finite-dimensional)

Apply Step 2 with `(gamma, d, alpha)` in place of `(alpha, b, gamma)` and `phi'` in place of `phi`, to
`M_d = <alpha, alpha^gamma> = <alpha, z_d>`, where `z_d = [alpha, gamma] = z^-1`, and to
`W_d = < z_d^(alpha^j) : j in Z > <= A'`. The error subgroup is the same `N = A'' = <gamma, alpha>''`, and
the vector space is the same `V`. The span `span_Q { X^j zbar }` is therefore finite-dimensional, and
some nonzero `q` has `q(X) zbar = 0`.

## Step 4 (`A` has finite Hirsch length)

`A'` is the normal closure in `A` of `z^-1 = [alpha, gamma]`. So `V = Q[X^±1, Y^±1] · zbar`. Since `X` and
`Y` commute, `p(Y)` and `q(X)` kill `V`, and `dim V <= deg p · deg q`. By (H1),

```text
h(A) = h(A/A') + h(A'/A'') + h(A'') <= 2 + deg p · deg q + h(N) < ∞.
```

## Step 5 (item 1)

`A` is solvable of finite Hirsch length and contains `alpha = a^m`, `gamma = c^m`. Step 5 of
`higman-metabelian-edge-collapse-proof` uses only these facts and the relations of `Q`, so it gives
`Q = 1`. (That step is the solvable eigenvalue count of `higman-nilpotent-edge-collapse-proof`, run on
`u_k = gamma^(alpha^k)` and `b^(P^K)`.) For `<b^m, d^m>`, apply the automorphism
`theta : a -> b -> c -> d -> a` of `H4`, as in that proof.

## Step 6 (item 2)

Let the image `S` of `<a,c>` have a normal subgroup `S_0` of finite index `m` with `S_0''` solvable and
`h(S_0'') < ∞`. Then `x^m in S_0` for all `x in S`. So `A = <a^m, c^m> <= S_0`, and `A'' <= S_0''` is
solvable with `h(A'') <= h(S_0'')` by (H2). Step 5 gives `Q = 1`. The case `<b,d>` is the same.

SbM is closed under subgroups. If `T <= S`, then `T ∩ S_0` is normal of finite index in `T`, and
`(T ∩ S_0)'' <= S_0''`.

## Step 7 (item 3)

Suppose `Q != 1` acts on a tree without inversions and fixes no vertex. By item 2 of
`nilpotent-edge-images-collapse-higman-quotients` (the Helly tree gate), some edge stabilizer `E`
contains `<a,c>` or `<b,d>`. If `E` is SbM, so is that subgroup, and Step 6 gives `Q = 1`, a
contradiction. A nontrivial amalgam or HNN splitting gives a Bass--Serre tree without a global fixed
point, with edge stabilizers conjugate to the edge group.

## Gap analysis (derived length 3 with `A''` of infinite rank)

Every use of `h(N) < ∞` is essential to this argument:
- in `dim U`;
- in `h(D ∩ N)`;
- in Step 5, which needs `h(A) < ∞`.

**Why not level 2.** Rerunning at the next derived level would need an element of `A''` whose
`phi`-image is a power of `gamma` times a controlled correction, as for `z`. The generators
`[z^(gamma^i), z^(gamma^j)]` of `W'` map to `[(gamma^e w_0)^(gamma^(2^P i)), (gamma^e w_0)^(gamma^(2^P j))]`. In this commutator the `gamma^e` factors cancel modulo `W'`-type terms, so no nonzero eigen-shift `e` survives.

**Route (i), Mal'cev/unipotent.** When `A'` is nilpotent, `W` and `phi(W)` lie in different nilpotent
subgroups (`A'` and `phi(A')`). `D = W ∩ phi(W)` is not `gamma^e`-invariant, so no single nilpotent Lie
algebra carries both filtrations.

**Route (ii), `h(W ∩ phi(W))`.** This is the route used here. It closes exactly when the bottom
`A''` is of finite Hirsch length.

**Positive direction.** An SbM-free amenable edge image must have infinite-rank second derived
subgroup in every finite-index subgroup.

**Best next test.** Look for an element of `A''` with a genuine eigen-scaling under `b^P`. For example,
`phi` of `[z, z^alpha]` involves `gamma^e` and `(gamma^alpha)^e`-type factors that need not cancel. A
two-variable version of Step 2 might control the `X,Y`-span of `[z, z^alpha]` in `A''/A''' ⊗ Q`.
