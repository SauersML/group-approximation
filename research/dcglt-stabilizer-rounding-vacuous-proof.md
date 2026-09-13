---
rg: 2
id: dcglt-stabilizer-rounding-vacuous-proof
kind: route
title: Torsion-free finite index, free building action, and induction of sector tuples
target: dcglt-stabilizer-rounding-is-vacuous-at-torsion-free-index
requires: []
artifacts:
  - research/artifacts/solve-nh-dcglt-2026-09-13.md
---

Notation as in the target. Citations are to arXiv:1711.10238, TeX source read
on MSI; line numbers refer to that source.

**(TF1).** The source (line 943) states that such `Gamma` contains a
finite-index torsion-free subgroup; replace it by its normal core in `Gamma`,
which has finite index and is torsion free. Put `Lambda~ = pi^(-1)(Lambda)`
for `pi : Gamma~ -> Gamma`. It contains `ker pi = C(p)`, which is central in
`Gamma~` and hence in `Lambda~`. A finite-index subgroup of `Lambda~` has finite
index in `Gamma~`, so by the source Proposition (line 1075) it contains
the index-two subgroup of `C(p)`. For `p >= 5` that subgroup is nontrivial, so
`Lambda~` is not residually finite.

**(TF2).** The building `B` is contractible and `G(Q_p)` acts on it with
compact open cell stabilizers. `Lambda` is discrete, so `Lambda cap Stab(sigma)`
is finite for every cell `sigma`, hence trivial because `Lambda` is torsion
free. `Lambda` has finite index in the uniform lattice `Gamma`, so it is uniform.
The source (line 935) states that for a torsion-free uniform lattice the quotient
is a finite simplicial complex of dimension equal to the `K`-rank and the
lattice is its fundamental group. By line 1053, `G(Q_p) = Sp(2n, Q_p)` is split,
so the rank is `n`. `Lambda~` acts through `Lambda` with kernel `C(p)`, so its cell
stabilizers are exactly `C(p)`.

**(TF3), restriction.** Choose a finite presentation `<T | Q>` of `Lambda~`
with `z in T`, and for each `t in T \ {z}` a word `w_t` in `S cup {z}` equal to
`t` in `Gamma~`. Given `rho` on `S cup {z}` with `rho(z) = zeta I`, set
`rho'(t) = rho(w_t)` and `rho'(z) = zeta I`. For `q in Q`, the substituted word
`w_q` is trivial in `Gamma~`, so in the free group on `S cup {z}` it is a product
of conjugates of relators `r^(+-1)`, `r in R`. `Q` is finite, so the number of
factors is bounded by some `N`. Homomorphic extension gives
`rho(w_q) = prod_i rho(u_i) rho(r_i)^(+-1) rho(u_i)^(-1)` exactly. Unitary
invariance and `||XY - I|| <= ||X - I|| + ||Y - I||` for unitaries give
`||rho'(q) - I||_HS <= N max_r ||rho(r) - I||_HS`. Taking infima,
`sigma_(Lambda~)(d) <= N sigma_(Gamma~)(d)`.

**(TF3), induction.** Write `Gamma~ = t_1 Lambda~ ⊔ ... ⊔ t_k Lambda~` with
`t_1 = 1`. For a generator `g in S cup {z}` and each `j` there are a unique
`i = pi_g(j)` and a unique `lambda_(g,j) in Lambda~` with
`g t_j = t_i lambda_(g,j)`. Fix words for `lambda_(g,j)` in `T`. Given `rho'` on
`T` with `rho'(z) = zeta I`, define `Phi(g) in U(k d)` as the `k x k` block
matrix whose `(pi_g(j), j)` block is `rho'(lambda_(g,j))` and whose other blocks
vanish. It is unitary, as a permutation of unitary blocks.

- **The central generator.** `z` is central, so `z t_j = t_j z`, `pi_z = id` and
  `lambda_(z,j) = z`. Hence `Phi(z) = zeta I_(kd)`.
- **Products.** For generators `g, h`, `(g h) t_j = t_(pi_g pi_h (j)) lambda_(g, pi_h(j)) lambda_(h, j)`,
  so the block formula is multiplicative on words.
- **Relators.** For `r = g_1 ... g_m in R`, `Phi(r)` is a block permutation with
  permutation `pi_r`. That is the identity, since `r = 1` in `Gamma~` and the
  action on cosets is exact. Its `j`-th diagonal block is
  `rho'(lambda_1) ... rho'(lambda_m)` for the chain of `lambda`'s determined by
  `r` and `j`. The product `lambda_1 ... lambda_m = t_j^(-1) r t_j = 1` in
  `Lambda~`, so the corresponding word in `T` is a product of at most `N'`
  conjugates of relators `q^(+-1)`, `q in Q`. There are finitely many pairs
  `(r, j)`, so `N'` is uniform, and
  `||block_j - I||_HS <= N' max_q ||rho'(q) - I||_HS`.
- **Averaging.** The normalized HS norm on `C^(kd)` averages the `k` diagonal
  blocks, so `||Phi(r) - I||_HS <= N' max_q ||rho'(q) - I||_HS`. Taking infima,
  `sigma_(Gamma~)(k d) <= N' sigma_(Lambda~)(d)`.

The consequence stated in the target follows: a floor `sigma >= c > 0`
independent of `d` for one group gives one for the other, with `c` divided by
`N` or `N'`.

**(TF4).** The source defines stability for a finite presentation
(Definition `stabdef`, line 334): all maps `phi_k : S -> U(d_k)` with
`defect(phi_k) = max_r ||phi_k(r) - 1|| -> 0` satisfy
`homdist(phi_k) = inf_(psi in Hom) max_s ||phi_k(s) - psi(s)|| -> 0` (lines
300--318). For `p >= q_0(n)` the group `Gamma~` is 2-Kazhdan by source Theorem
`higherkazhdan` with source Proposition `kazhext` (line 919: a finite extension of
an `n`-Kazhdan group is `n`-Kazhdan), so it is Frobenius stable by source
Theorem `main2` (line 182). The hypothesis there is cohomological and does not
depend on the presentation, so we apply it to `<S cup {z} | R>`.

Suppose no `delta > 0` works. Then there are `rho_k : S cup {z} -> U(d_k)` with
`rho_k(z) = zeta I` and Frobenius defect tending to `0`. Stability gives
homomorphisms `psi_k : Gamma~ -> U(d_k)` with
`max_(s in S cup {z}) ||rho_k(s) - psi_k(s)||_Frob -> 0`.

- **`psi_k(z^2) = 1`.** The image `psi_k(Gamma~)` is a finitely generated
  subgroup of `GL_(d_k)(C)`, hence residually finite (Malcev). Each of its
  finite-index subgroups pulls back to a finite-index subgroup of `Gamma~`,
  which contains the index-two subgroup `<z^2>` of `C(p)`. So `psi_k(z^2)` lies
  in every finite-index subgroup of the image, and `psi_k(z^2) = 1`.
- **Contradiction.** For unitaries,
  `||A^2 - B^2|| <= ||A(A - B)|| + ||(A - B)B|| = 2||A - B||`. Hence
  `d_k^(1/2) |zeta^2 - 1| = ||zeta^2 I - I||_Frob = ||rho_k(z)^2 - psi_k(z)^2||_Frob <= 2 ||rho_k(z) - psi_k(z)||_Frob -> 0`.
  But the left side is at least `|zeta^2 - 1| > 0`, a contradiction.

Since `||A||_HS = d^(-1/2) ||A||_Frob`, the Frobenius floor `delta` gives
`sigma_(Gamma~)(d) >= delta d^(-1/2)`.
