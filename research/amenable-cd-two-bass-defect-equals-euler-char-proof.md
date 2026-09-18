---
rg: 2
id: amenable-cd-two-bass-defect-equals-euler-char-proof
kind: route
title: Tensoring the length-two projective resolution with Q and with U(G) and comparing the two Euler characteristics identifies the Bass defect of the relation module with 1 - b_1 + b_2; the Hantzsche-Wendt Fox matrix gives a flat module of defect 1 that is not projective
target: amenable-cd-two-bass-defect-equals-euler-characteristic
requires:
  - amenable-fp-iff-affiliated-top-homology-vanishes
  - amenable-cd-two-kropholler-iff-locally-indicable
  - l2-small-projectives-with-rank-gap-are-finitely-generated
  - subexp-amenable-cd-two-kropholler-iff-no-intermediate-growth
---

Notation as in the target. `U = U(G)`, `dim = dim_U`, and `⊗ = ⊗_{Z[G]}` unless another ring is
indicated. Row vectors are used, and a matrix `A ∈ M_{k×n}(Z[G])` acts by right multiplication
`v ↦ vA`. `rank_U(A)` is `dim` of the image of `U^k → U^n`, and `ε : Z[G] → Z` is the
augmentation.

## Imports

- **(J1)–(J3), (J6)** as in `amenable-fp-iff-affiliated-top-homology-vanishes-proof`:
  - (J1) the additive, monotone dimension on all `U`-modules, where a finitely generated
    projective module of dimension 0 is zero;
  - (J2) `U` is von Neumann regular, so finitely generated submodules of projectives are direct
    summands;
  - (J3) for amenable `G`, `dim Tor_p^{Z[G]}(U, M) = 0` for `p >= 1`, and `dim(U ⊗ Z) = 0` if
    `G` is infinite;
  - (J6) if `cd G <= 2`, the kernel of any surjection from a projective resolution truncated at
    degree 1 is projective. Concretely, `0 → P → Z[G]^n → Z[G] → Z → 0` is a projective
    resolution (Brown VIII.2.1, Schanuel).
- **(J7) Cofinality.** If `M = ⋃ M_i` is a directed union of `U`-submodules, then
  `dim M = sup dim M_i` (Lück, *L²-invariants*, Theorem 6.7(3); transported to `U` as in (J1);
  recalled).
- **(J8) Operator ranks.** For `A ∈ M_{k×n}(Z[G])`, `rank_U(A) = dim_NG` of the closure of the
  image of `r_A : ℓ²(G)^k → ℓ²(G)^n` (Lück, Chapter 8; recalled). The adjoint of `r_A` is
  `r_{A^*}`, where `*` is the conjugate transpose with `g ↦ g^{-1}`.
- **(B) Bass conjecture for amenable groups** (A. J. Berrick, I. Chatterji, G. Mislin, *From
  acyclic groups to the Bass conjecture for amenable groups*, Math. Ann. 329 (2004); recalled, as
  used in Degrijse's Step B2 and recorded in the artifact of the fp-iff node).
  - For amenable `G` and a finitely generated projective `Z[G]`-module `M`, the Hattori–Stallings
    rank of `M` vanishes on every conjugacy class of elements of infinite order.
  - If `G` is torsion-free, then `dim(U ⊗ M) = κ(M) = rank_Z(Z ⊗ M) = rank_Q(Q ⊗ M)`, where `κ`
    is the Kaplansky trace. So `D(M) = 0`, and `dim(U ⊗ M)` is a non-negative integer.
- **(Ba) Big projectives** (H. Bass, *Big projective modules are free*, Illinois J. Math. 7
  (1963); recalled). Over a commutative noetherian ring with connected spectrum, every projective
  module that is not finitely generated is free.
- **(HW) The Hantzsche–Wendt group** (recalled, as in the artifact §6.2 and the LI node).
  - `HW` is torsion-free and finitely presented.
  - It contains a normal subgroup `A ≅ Z³` with `HW/A ≅ (Z/2)²`, acting on `A ⊗ Q = Q³` by
    `diag(1,−1,−1)`, `diag(−1,1,−1)` and `diag(−1,−1,1)`.
  - `H_1(HW; Z) = Z/4 ⊕ Z/4`, so `b_1(HW) = 0`.
  - It is amenable and has `cd = 3`.
- **(Ly) Lyndon.** A one-relator presentation whose relator is not a proper power is aspherical
  (recalled, as in `amenable-cd-two-aspherical-presentations-via-l2-rank-gap`).

## Step 1: the identity (item 1)

Let `G` be infinite, finitely generated and amenable, with `cd_Z G <= 2`, and fix generators
`x_1, …, x_n`. By (J6), `0 → P → Z[G]^n →∂ Z[G] → Z → 0` is a projective resolution, where
`∂(e_i) = x_i − 1`. `P` is a submodule of the countable module `Z[G]^n`, so it is countably
generated.

*Rational side.* Apply `Q ⊗ −` to the resolution with `Z` deleted. This gives
`Q ⊗ P →α Q^n →β Q`, whose homology is `H_*(G; Q)`. Here `β = 0`, since `ε(x_i − 1) = 0`.
Hence:
- `H_0 = Q`;
- `H_1 = Q^n / im α`, so `rank α = n − b_1`;
- `H_2 = ker α`, since there is no degree-3 term.

So `rank_Q(Q ⊗ P) = rank α + dim ker α = n − b_1 + b_2`, with value `+∞` when `b_2 = ∞`.

*`L²` side.* Apply `U ⊗ −`. This gives `U ⊗ P →α' U^n →β' U`, with homology `H_*(G; U)`. By
(J3), each `H_p(G; U)` has dimension 0 (`p = 0, 1, 2`), and every dimension below is finite.
Using additivity (J1):
- `dim(im β') = 1 − dim H_0 = 1`;
- `dim ker β' = n − 1`;
- `dim(im α') = dim ker β' − dim H_1 = n − 1`;
- `dim(U ⊗ P) = dim(im α') + dim(ker α') = n − 1 + dim H_2 = n − 1`.

Subtracting the two sides gives `D(P) = (n − b_1 + b_2) − (n − 1) = 1 − b_1 + b_2 = χ_Q(G)`.

*The general formula.* For arbitrary `G` with `cd_R G <= 2` (`R = Z` or `Q`), the same
computation over `R[G]` goes through without (J3). It gives
`dim(U ⊗ P) = n − 1 + b_0^(2) − b_1^(2) + b_2^(2)` whenever `b_2^(2) < ∞`, while the rational
side is unchanged. So `D(P) = χ_Q − χ^(2)`. ∎

**Remark (injectivity used below).** `ker α' = H_2(G; U)` is a submodule of dimension 0 of the
projective module `U ⊗ P`. That module is a direct summand of a free module. A zero-dimensional
submodule of a free `U`-module is zero: take `x ≠ 0` in it; then `Ux` is finitely generated,
hence projective by (J2), and nonzero, hence of positive dimension by (J1). So `U ⊗ P → U^n` is
injective.

## Step 2: the equivalence (item 2)

- **(a) ⇒ (b).** Assume (a) and let `G` be infinite, finitely generated and amenable with
  `cd_Z G <= 2`. By item 2 of the LI node, `G` is solvable. By item 1 of the LI node, `G ≅ Z` or
  `G ≅ BS(1,m) = ⟨a, t | t a t⁻¹ a⁻ᵐ⟩` with `m ≠ 0`.
  - `Z` has `b_1 = 1`, `b_2 = 0`.
  - `BS(1,1) = Z²` has `b_1 = 2`, `b_2 = 1`.
  - For `m ≠ 1`, `H_1(BS(1,m)) = Z ⊕ Z/|m − 1|`, so `b_1 = 1`. The presentation complex is
    aspherical by (Ly), so `1 − b_1 + b_2 = 1 − 2 + 1 = 0`, which gives `b_2 = 0`.

  In every case `b_1 = 1 + b_2`.
- **(b) ⇒ (c).** Immediate.
- **(c) ⇔ (d).** By Step 1, `D(P) = χ_Q(G)` for every finite generating set. So (d) for one
  generating set gives (c), and (c) gives (d) for every generating set.
- **(c) ⇒ (a).** Let `G` be finitely generated and amenable of cd 2. Then `G` is infinite (it is
  torsion-free and nontrivial), and (c) gives `1 − b_1 + b_2 <= 0`. In particular `b_2 < ∞` and
  `b_1 >= 1 + b_2 >= 1`, so `G` has infinite abelianization. This is statement (b) of item 2 of
  the LI node, which is equivalent to (a).

The equivalence of (a) with the rank-gap target is item 2(a) of the LI node. ∎

## Step 3: where the defect sits (item 3)

Suppose (a) fails. By item 3(i) of the LI node there is a finitely generated counterexample `K`
with finite abelianization. `K` is amenable with `cd_Z K <= 2`. It is torsion-free, because its
cohomological dimension is finite. It is infinite, because it is nontrivial. Fix `n` generators.

**(a)** Step 1 gives `D(P) = 1 − 0 + b_2(K) >= 1` and `dim(U ⊗ P) = n − 1`.

**(b)** Item 3 of the L2-small node gives `P = P_0 ⊕ P'`, where `P_0` is finitely generated and
`P'` has no nonzero finitely generated direct summand. Both `Q ⊗ −` and `U ⊗ −` commute with
direct sums, so `D(P) = D(P_0) + D(P')` and the dimensions add.

- By (B), `D(P_0) = 0`, and `s := dim(U ⊗ P_0) = rank_Q(Q ⊗ P_0)` is an integer.
- So `D(P') = D(P) = 1 + b_2(K)`, and `dim(U ⊗ P') = n − 1 − s` is an integer.
- `P' ≠ 0`: otherwise `P = P_0` and `D(P) = 0`.
- Take `0 ≠ c ∈ P'`. By the Remark after Step 1, the image of `1 ⊗ c` in `U^n` is `c ≠ 0`, so
  `U ⊗ P' ≠ 0`.
- `U ⊗ P'` is a direct summand of the projective module `U ⊗ P`, which injects into `U^n`. So
  for `0 ≠ y ∈ U ⊗ P'`, the submodule `Uy` is a nonzero finitely generated submodule of a free
  module. It is projective by (J2) and has positive dimension by (J1).
- Hence `dim(U ⊗ P') > 0`. Being an integer, it is at least 1, and so `s <= n − 2`.
- Finally, `rank_Q(Q ⊗ P') = rank_Q(Q ⊗ P) − s = n + b_2(K) − s`, by Step 1 with `b_1(K) = 0`.

**(c)** Assume `K` has no free subsemigroup. Let `N <= K` have index `m`. `N` is again NFS,
amenable and of `cd <= 2`, and it is not elementary amenable (otherwise `K`, virtually `N`, would
be). By item 1 of `subexp-amenable-cd-two-kropholler-iff-no-intermediate-growth`, a finitely
generated amenable NFS group of cd at most 2 with virtual infinite abelianization is
elementary amenable. Hence `b_1(N) = 0`.

Restricting the resolution to `N` gives the projective `Z[N]`-resolution
`0 → res P → Z[N]^{nm} → Z[N]^m → Z → 0`. Here:
- `dim_{U(N)}(U(N) ⊗_{Z[N]} res P) = m(n − 1)`, by the finite-index formula `U(K) ≅ U(N)^m`
  (Lück, Theorem 6.29; recalled);
- the rational computation of Step 1 applies verbatim, and with `b_0(N) = 1` it gives
  `rank_Q(Q ⊗_{Z[N]} res P) = nm − m + 1 − b_1(N) + b_2(N)`.

So `D(res_N P) = 1 − b_1(N) + b_2(N) = 1 + b_2(N) >= 1`.

**The reduction.** Suppose the open statement `l2-finite-projectives-over-amenable-groups-satisfy-weak-bass`
holds for `K`. Then `D(P') <= 0`, contradicting (b). So that statement implies (a). ∎

## Step 4: finite truncations (item 4)

Let `G` be infinite and finitely generated with `b_1(G) = 0`, with generators `x_1, …, x_n` and
defining relators `R`. The Fox matrix of all relators gives an exact sequence
`Z[G]^(R) →J Z[G]^n →∂ Z[G]` (J6).
- Its augmentation `ε(J)` presents `H_1(G; Z)`, which is finite. So `ε(J)` has rank `n` over `Q`,
  and finitely many rows already have rank `n`. Let `J_k` be the matrix of these `k` rows.
- The rows of `J_k` lie in `ker ∂`. Over `U`, they lie in `ker(U^n → U)`, which has dimension
  `n − 1` because `dim(U ⊗ Z) = 0` for infinite `G`. So `rank_U(J_k) <= n − 1`.

By (HW), `G = HW` qualifies. It is torsion-free and amenable. So the inequality
`rank_Q ε(A) <= rank_U(A)` fails for some matrix over the integral group ring of a torsion-free
amenable group.

In a counterexample `K` from Step 3, the same `J_k` exists. The rows of `J_k` span a finitely
generated submodule `P_k ⊆ P`, and the image of `Q ⊗ P_k → Q^n` already has rank `n > n − 1`.
So the finite data `(G torsion-free amenable, J_k, rows in ker ∂)` are realised both by `K` and by
`HW`. `HW` has `cd 3` and is not a counterexample. Any conclusion drawn from these finite data
alone would therefore also hold for `HW`. One such conclusion would be `b_1 >= 1`, and that is
false for `HW`. ∎

## Step 5: a flat module of defect 1 over `HW` (item 5)

Let `G = HW` and let `J = J_k` be as in Step 4 on `n` generators. The relators form a finite
presentation, so the sequence `Z[G]^k →J Z[G]^n →∂ Z[G] → Z → 0` is exact.
Put `B = J^* J ∈ M_n(Z[G])` and `M = colim(Z[G]^n →·B Z[G]^n →·B ⋯)`.

*Flat and countably generated.* `M` is a directed colimit of free modules, so it is flat. Its
generating set is countable.

*Rational rank.* `Q ⊗ −` commutes with colimits, so `Q ⊗ M = colim(Q^n →ε(B) Q^n → ⋯)`. Here
`ε(B) = ε(J)^T ε(J)`. This is positive definite, because `ε(J)` has rank `n`. So every map in the
system is an isomorphism, and `rank_Q(Q ⊗ M) = n`.

*`L²`-dimension.*
- `U ⊗ M = colim(U^n →B U^n → ⋯)`. Let `T = r_J : ℓ²(G)^k → ℓ²(G)^n`. Then
  `r_B = T T^*` by (J8).
- For every `m >= 1`, `ker r_{B^m} = ker(T T^*)^m = ker T^*`. So
  `rank_U(B^m) = rank(T T^*) = rank(T) = rank_U(J)`.
- Exactness at `Z[G]^n` gives `H_1(G; U) = ker(U^n → U) / im J`. This has dimension 0 by (J3),
  and `ker(U^n → U)` has dimension `n − 1`. So `rank_U(J) = n − 1`.
- The image of the `i`-th term `U^n` in the colimit is `U^n / ⋃_m ker(·B^m)`. The kernels
  increase, each has dimension `n − (n − 1) = 1`, and their union has dimension 1 by (J7). So
  each image has dimension `n − 1`.
- `U ⊗ M` is the directed union of these images, so `dim(U ⊗ M) = n − 1` by (J7).

Hence `D(M) = 1`.

*`M` is not projective.* Suppose `M` were projective over `Z[G]`. Then `res_A M` would be
projective over the commutative noetherian domain `Z[A] = Z[t_1^{±1}, t_2^{±1}, t_3^{±1}]`,
whose spectrum is connected.
- If `res_A M` is finitely generated, then `M` is finitely generated over `Z[G]` (index 4), hence
  a finitely generated projective module. Then `D(M) = 0` by (B), which contradicts `D(M) = 1`.
- Otherwise `res_A M` is free of infinite rank by (Ba), so `Q ⊗_{Z[A]} res_A M` has infinite
  `Q`-dimension. But
  `Q ⊗_{Z[A]} res_A M = Q[G/A] ⊗_{Z[G]} M = colim(Q[G/A]^n → ⋯)` has `Q`-dimension at most `4n`.
  This is a contradiction.

So `M` is flat, countably generated, not projective, and has `dim(U ⊗ M) = n − 1 < ∞` and
`D(M) = 1`.

*Cross-check without (B).* The rank of `Q[G/A] ⊗ M` can be computed character by character.
`Q[(Z/2)²]` splits into four characters `χ`.
- For the trivial character the stable rank is `n`.
- For a nontrivial `χ`, write `Q_χ` for `Q` twisted by `χ`. By Shapiro and (HW),
  `H_1(A; Q) = ⊕_χ H_1(G; Q_χ)`. Each nontrivial `χ` occurs exactly once in `Q³` and the trivial
  one does not, so `H_1(G; Q_χ) = Q`. Since `χ(∂) ≠ 0`, the matrix `χ(J)` has rank `n − 2`.
  Then `χ(B) = χ(J)^T χ(J)` has stable rank `n − 2`.

The total is `4n − 6`. A finitely generated projective `Z[A]`-module has constant rank, so its
coinvariant rank equals its `U(A)`-dimension. That dimension would be `4(n − 1) = 4n − 4`, and
`4n − 4 ≠ 4n − 6`. So the finitely generated case is excluded directly as well. ∎

**Why this kills the three kinds of argument in item 5.** Each of them uses the relation module
only through data that `M` also has.
- A Lazard–Govorov argument uses `P` only as a countably generated flat module of finite
  `L²`-dimension, written as a colimit of finitely generated free modules.
- A Følner or ball truncation of such a colimit uses only the transition matrices over a
  torsion-free amenable group.
- An argument from finitely generated submodules uses only matrices like `J_k` (Step 4).

For `M`, all these data are present and `D(M) = 1 > 0`. So a conclusion `D <= 0` drawn from them
is false. The distinguishing input is projectivity, and projectivity enters only through direct
summands of free modules. For summands, the defect is controlled by the Hattori–Stallings trace
when they are finitely generated (B). For countably generated summands of finite `L²`-dimension,
it is exactly the open statement.

## Step 6: `L²` data (item 6)

Step 1 computes the `U`-dimension profile `(n − 1, n, 1)` of `P, Z[G]^n, Z[G]` and shows that all
`L²`-homology has dimension 0, for every infinite amenable `G` with `cd <= 2`. `Z²` has the same
profile, with `P ≅ Z[Z²]^{n−1}` stably. For amenable `G`, `U`-dimensions of finitely presented
modules are Følner limits of normalised ranks on Følner pieces (Elek; recalled, as in the
target). An argument that uses only these numbers, or their Følner approximations, cannot tell a
counterexample from `Z²`. The only invariant that separates them is `χ_Q = D(P)`, which is not a
`U`-dimension.

Degrijse's Step B2 (import (J5) of the fp-iff proof) concludes `χ = χ^(2)` from (B). This needs
the Hattori–Stallings trace of a finitely generated `P`, and then says exactly `D(P) = 0`. When
`P` is not finitely generated, it is statement 2(d). ∎

## Step 7: calibrations

- **Finite `G` over `Q`.** Here `Q[G]` is semisimple and `cd_Q G = 0`.
  - `b_i = 0` for `i >= 1`, so the rational side is `n`.
  - `U(G) = C[G]` and `dim(U ⊗ Q) = 1/|G|`, so the image of `U^n → U` has dimension
    `1 − 1/|G|`.
  - Higher homology vanishes, so `dim(U ⊗ P) = n − 1 + 1/|G|`.

  So `D = 1 − 1/|G| = χ_Q − χ^(2)`.
- **`Z/2 ≀ Z` over `Q`.** The base is countable and locally finite, so it has `cd_Q <= 1` and no
  rational homology in positive degrees. So `cd_Q <= 2`, and `H_*(G; Q) = H_*(Z; Q)` gives
  `b_1 = 1`, `b_2 = 0`. The group is amenable and infinite, so all `L²`-Betti numbers vanish and
  `D = 0`.
- **`HW` in dimension 3.** It is orientable, so `b_3 = 1`, and `χ_Q = 1 − 0 + 0 − 1 = 0` while
  `b_1 = 0`.
- **The `FP_2` case.** If `P` is finitely generated, then (B) gives `D(P) = 0`. For finite
  abelianization this would mean `1 + b_2 = 0`, which is impossible. ∎
