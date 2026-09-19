---
rg: 2
id: higman-gamma-3-2e-is-a-reducible-lattice-for-e-at-most-7-proof
kind: route
title: Proof that both tree kernels of Gamma(3,2^e) contain b^(m/4), that Gamma(3,2^e) is reducible for e <= 7, and that the reduction of ord(a) to Abar_e holds for e <= 6 and fails for e >= 9
target: higman-gamma-3-2e-is-a-reducible-lattice-for-e-at-most-7
requires:
  - higman-torsion-generator-quotients-factor-through-tree-lattices
  - higman-edge-relator-twist-breaks-tree-lattice-freiheitssatz
artifacts:
  - experiments/higman-b-splitting-2026-09-18/pathstab.py
  - experiments/higman-b-splitting-2026-09-18/ball.py
  - experiments/higman-b-splitting-2026-09-18/d1.g
  - experiments/higman-b-splitting-2026-09-18/d1-output.txt
  - experiments/higman-b-splitting-2026-09-18/d3.g
  - experiments/higman-b-splitting-2026-09-18/d3-output.txt
  - experiments/higman-b-splitting-2026-09-18/enum.g
  - experiments/higman-b-splitting-2026-09-18/twists.py
  - experiments/higman-b-splitting-2026-09-18/twists.g
  - experiments/higman-b-splitting-2026-09-18/twists-e3-output.txt
  - experiments/higman-b-splitting-2026-09-18/twists-e4-output.txt
  - experiments/higman-b-splitting-2026-09-18/twists-e5-output.txt
  - experiments/higman-b-splitting-2026-09-18/twists-e6-output.txt
  - experiments/higman-b-splitting-2026-09-18/hfail.py
  - experiments/higman-b-splitting-2026-09-18/hfail-output.txt
---

Notation is that of the target. In the target, `m = 2^e`, `e >= 3` and `t = 3^-1 mod m`. The unit
`3` has order exactly `m/4` in `(Z/m)^x`, and so does `t`.

## 0. Exact factorization and push rules

**Exact factorization.** By the geometry item of
`higman-torsion-generator-quotients-factor-through-tree-lattices`, `Gamma` acts on `T_A x T_B`
freely and transitively on squares and without inversions.
- Let `e_A` be the edge of `T_A` with stabilizer `A`, and `e_B` the edge of `T_B` with stabilizer `B`.
- Then `A ∩ B = Stab(e_A x e_B) = 1`.
- For an edge `f` of `T_B`, transitivity on squares gives `g` with `g(e_A x e_B) = e_A x f`.
  Then `g in Stab(e_A) = A`, and `g e_B = f`.
- So `A` is transitive on `Gamma/B`, and `Gamma = A · B`.

Every element is therefore uniquely `alpha beta` with `alpha in A` and `beta in B`. The edges of
`T_B` are the cosets `alpha B`, one for each element of `A = Z/m * Z/m`, that is, for each reduced
word in `a, c`.

**Transversal.** Applying `sigma^3` to the amalgam item `K1 = ⊔_j b^j A` gives `L1 = ⊔_j a^j B`.
The vertex `v = L1` and its `m` edges `a^j B` are described by `ball.py`: vertices at distance `r`
from `v` are the words `a^(j1) c^(k1) a^(j2) ...` of syllable length `r`, with `k1, j2, ... != 0`.

**Push rules.** From `b^a = b^3` and `c^b = c^3`, and their images under `sigma^2`:
- `b^q a^i = a^i b^(q 3^i)`;
- `b^q c^k = c^(k t^q) b^q`;
- `d^q c^i = c^i d^(q 3^i)`;
- `d^q a^k = a^(k t^q) d^q`.

So for `beta in B` and an `A`-word `alpha`, `beta alpha = alpha' beta'` is computed syllable by
syllable, with the same syllable pattern. This is `left`/`push` in `pathstab.py`, `ball.py` and
`twists.py`.

## 1. Torsion in the kernels (every e >= 3)

Put `q = m/4`.
- `3^i q ≡ (-1)^i q (mod m)`, since `3^i ≡ (-1)^i (mod 4)`.
- `t^(±q) = 1`, since `t` has order `q`.

**`b^q` fixes every edge.** Let `alpha = a^(j1) c^(k1) a^(j2) ...`.
- Pushing `b^(±q)` through `a^j` gives `b^(±q (-1)^j)`.
- Pushing `b^(±q)` through `c^k` leaves `c^(k t^(±q)) = c^k` unchanged.
- Hence `b^q alpha = alpha b^(±q)`, so `b^q (alpha B) = alpha B` for every edge `alpha B`, and
  `b^q in Lambda_B`.

**The other generators.**
- `sigma^2` preserves the B-splitting (it swaps `L1` and `L2` and fixes `B`), so it preserves
  `Lambda_B`. Hence `d^q in Lambda_B`.
- `sigma` maps `A -> B`, `K1 -> L2` and `K2 -> L1`, so it carries `T_A` to `T_B` and
  `Lambda_A = sigma^-1(Lambda_B)`. Hence `a^q, c^q in Lambda_A`.

**The kernels are infinite.** `<b^q, d^q> = Z/4 * Z/4` inside `B = Z/m * Z/m`, and this is infinite.

**The product.**
- `Lambda_A ∩ Lambda_B <= A ∩ B = 1`, and both are normal. So `[Lambda_A, Lambda_B] = 1` and
  `N := Lambda_A Lambda_B = Lambda_A x Lambda_B` is normal.
- The map `A/Lambda_A x B/Lambda_B -> Gamma/N`, `(alpha, beta) -> alpha beta N`, is onto because
  `Gamma = A B`.
- It is injective. Suppose `alpha beta = alpha' beta' l_A l_B`. Write
  `beta' l_A = (beta' l_A beta'^-1) beta'` with `beta' l_A beta'^-1 in Lambda_A <= A`. Exactness then
  gives `alpha ∈ alpha' Lambda_A` and `beta ∈ beta' Lambda_B`.

**Relations.**
- `a^-1 b^q a = b^(3q) = b^(-q)`.
- `b^-q c b^q = c^(3^q) = c`.

**`L1` never embeds in `Q_B`.** The kernel of `L1 -> Q_B` is `Lambda_B`, which contains `b^q != 1`.

**`A` embeds in `Q_B`.** `A ∩ Lambda_B <= A ∩ B = 1`. ∎

## 2. Reducibility for e <= 7

**Setup.** Let `w = L2` be the other end of `e_B`. For `r >= 1` put `K_r(u) = Fix_Gamma(B(u,r))`.
- An element fixing `B(v,r)` fixes the edge `e_B`, so `K_r(v) <= B`. Also
  `K_r(v) = ker(rho_r : B -> Sym S_r(v))`.
- `K_r(v)` is normal in `Stab(v) = L1`, and `K_r(w)` is normal in `L2`.
- `sigma^2` swaps `v` and `w` and swaps `b` and `d`. So `rho_r^w(beta)` is conjugate, uniformly in
  `beta`, to `rho_r^v(sigma^2 beta)`.

**Criterion.** Suppose `|rho_r(B)| = |<(rho b, rho d), (rho d, rho b)>|`, where `rho = rho_r^v`.
- The right-hand group is the image of `B` in `Sym S_r(v) x Sym S_r(w)`.
- Equality means `ker rho_r^v <= ker rho_r^w`, that is, `K_r(v) <= K_r(w)`. Applying `sigma^2`
  gives the reverse inclusion.
- So `K := K_r(v) = K_r(w)` is normal in `<L1, L2> = Gamma`.
- A normal subgroup fixing one vertex of each type fixes all vertices, since `Gamma` is transitive
  on each type. So `K <= Lambda_B`. Trivially `Lambda_B <= K`, hence `K = Lambda_B`.
- It follows that `[B : Lambda_B] = |rho_r(B)|`.
- Also `[L1 : Lambda_B]` is the order of the image of `L1` on `S_r(v)`: fixing `v` and `S_r(v)`
  fixes `B(v,r)`, because geodesics in a tree are unique.

**Computation.**
- `d1.g` builds the three permutations of `a, b, d` on `S_2(v)` with `ball.py` for `e = 3..7`.
- The criterion holds at `r = 2` for `e = 3..6`, with logs 2, 4, 6, 9, and fails at `e = 7`.
- `d3.g` checks it at `r = 3` for `e = 7`, over 2064512 vertices: `|rho_3(B)| = |diag| = 2^13`, and
  `|L1bar| = 2^20`.
- `d1-output.txt` also records that `Bbar` is abelian with `b, d` of order `m/4` for `e <= 5`, so
  `Bbar = (Z/(m/4))^2`. It is nonabelian at `e = 6, 7`.

**Consequences.**
- `[Gamma : Lambda_A x Lambda_B] = [A : Lambda_A][B : Lambda_B] = [B : Lambda_B]^2`, by section 1 and
  `sigma`.
- Each factor is an infinite finite-index subgroup of `Z/m * Z/m`, which is virtually free of
  rank `>= 2`. So each factor is virtually `F_k` with `k >= 2`, and `Gamma` is commensurable with
  `F_p x F_q`.

**Downward closure.** Let `e' <= e`. The map `Gamma_e -> Gamma_(e')` maps `B` onto `B'` and
`L1` onto `L1'`. It therefore induces an equivariant map on vertex sets
`g L1 -> gbar L1'`, which is onto.
- So the image of `Lambda_B(e)` fixes every vertex of `T_B(e')`, and lies in `Lambda_B(e')`.
- It has finite index in `B'`. ∎

## 3. Reduction lemma (every e)

**The twist.** For `beta in B`, push `beta` leftward through the eight syllables of `R`. Each step
uses `beta_k x^j = x^(j') beta_(k+1)`, with `x in {a,c}`, from the push rules of section 0. This
gives `beta R = S_beta beta_8`, with `S_beta` an `A`-word of syllable length at most 8. Put
`beta'' = beta_8 beta^-1`, so that `beta R beta^-1 = S_beta beta''`. This is `twist` in `twists.py`.

**Setup.** Let `Q_B = Gamma/Lambda_B`.
- `A` embeds in `Q_B` by section 1.
- `Q_B = A · Bbar` exactly: if `alpha in B Lambda_B = B`, then `alpha = 1`.
- In `Q_B`, the element `beta R beta^-1` depends only on `beta Lambda_B`.

**Under (H_e).** Suppose every `beta''` lies in `Lambda_B`. Then in `Q_B`:
- `beta R beta^-1 = S_beta in A`. Every conjugate `(alpha beta) R (alpha beta)^-1` is an
  `A`-conjugate of some `S_beta`.
- So `M := <<R>>_{Q_B} = <<S_beta : beta in Bbar>>_A <= A`, and
  `A/M = < a, c | a^m, c^m, S_beta > = Abar_e`.
- In `Qbar_B = Q_B/M` we still have `Qbar_B = (A/M) · Bbar` exactly. If `alpha beta in M` with
  `alpha in A` and `beta in Bbar`, then `beta in A M = A`, so `beta = 1`. Hence the index is `|Bbar|`.
- `Gammabar_e = Gamma/<<R>>` maps onto `Gamma/(Lambda_B <<R>>) = Qbar_B`, and `a` maps into
  `A/M`. Hence `ord(a in Gammabar_e) >= ord(a in Abar_e)`.

**Single powers.** If `beta = b^q`, then every intermediate `beta_k` is a single power of `b`.
- Pushing through `a^i` multiplies the exponent by `3^i`, and pushing through `c^k` leaves it
  unchanged.
- The `a`-exponents of `R` sum to 0, so `beta_8 = b^q` and `beta'' = 1`.
- `beta = d^q` follows by `sigma^2`, which fixes `R` up to inversion and conjugation. ∎

## 4. Certificates for e = 3..6

**Scripts.**
- `enum.g`, with `r = 2`, which is valid by section 2:
  - Restricts `rho_2(B)` to a union of orbits on which it is still faithful. The size is re-checked
    against `|rho_2(B)| = |Bbar|`.
  - Uses `g -> perm(g)^-1`, which is a homomorphism, since GAP permutations act on the right.
  - Enumerates all of `Bbar` by breadth-first search, with one word in `b, d` per element. The count
    is re-checked against `|Bbar|`.
- `twists.py` computes `(S_beta, beta'')` for each word.
- `twists.g`:
  - (1) evaluates every `beta''` in the faithful representation of `Bbar`. It finds `0` failures
    out of `4, 16, 64, 512`, so (H_e) holds.
  - (2) forms `Abar_e`, with `2 + |Bbar|` relators, all twisted relators being distinct up to
    rotation and inversion.
  - (3) computes `EpimorphismPGroup(Abar_e, 2, k)` until the image of `a` has order `2^e`.
  - (4) re-evaluates every relator in that image.

**Results.**

| e | class | order |
|---|---|---|
| 3 | 3 | `2^9` |
| 4 | 4 | `2^14` |
| 5 | 7 | `2^47` |
| 6 | 9 | `2^114` |

These are recorded in `twists-e*-output.txt`.

**Conclusion.** Each result is a finite quotient of `Abar_e` in which `a` has order `m`. So
`ord(a in Abar_e) = m`, and by section 3 `ord(a in Gammabar_e) = m`. ∎

## 5. Obstruction: (H_e) fails for e >= 9

**`b^j in Lambda_B` iff `m/4 | j`.**
- If `m/4 | j`, then `b^j in Lambda_B` by section 1.
- If `b^j in Lambda_B`, then `b^j` fixes the vertex `c L1`. But `b^j c L1 = c^(t^j) b^j L1`, which
  equals `c^(t^j) L1`. Distinct powers `c^k` with `k` modulo `m` give distinct vertices, since
  `L2 = ⊔ c^k B`. So `t^j = 1`, and therefore `m/4 | j`.

**The contradiction.** Suppose (H_e) holds.
- By section 3, `Bbar` embeds in `Qbar_B` and meets `A/M` trivially.
- By `higman-edge-relator-twist-breaks-tree-lattice-freiheitssatz` item 4, `b^64` lies in `Abar`
  in `Gammabar_e`, hence in `A/M` in `Qbar_B`.
- So `b^64 = 1` in `Bbar`, that is, `b^64 in Lambda_B`. This means `m/4 | 64`, so `e <= 8`.

**Explicit witness (`hfail.py`).**
- For `e = 9` and `beta = b d`, `beta'' = b^320`, which sends `c L1` to the vertex `(0,257)`.
- For `e = 10`, `beta'' = b^832`.
- For `e = 7, 8`, `beta'' = b^64`, which is `b^(m/2)` at `e = 7` and `b^(m/4)` at `e = 8`, and lies
  in `Lambda_B`.
- For `e = 6`, `beta'' = 1`. ∎

## What is not proved

- (H_e) for `e = 7, 8`. The check at `e = 7` over all `2^13` elements of `Bbar` did not finish.
- Reducibility of `Gamma_e` for `e >= 8`.
- `ord(a) = 2^e` in `Gammabar_e` for infinitely many `e`.
