# Deligne's multiplier in the rank metric: rigidity of scalar data (lane w4-deligne-projective, 2026-09-12)

Target: `deligne-cocycle-has-rank-approximate-projective-representations`. Notation as in
`deligne-twisted-group-algebras-2026-09-12.md`:

```text
1 -> C_3 = <z> -> E_3 -> Gamma = Sp_4(Z) -> 1,     s(g) s(h) = z^(a(g,h)) s(gh),     s(1) = 1,
```

so `a` is normalized. Fix a prime `p != 3`, `j in {1, 2}`, and a primitive cube root of unity `w` in an
algebraic closure `Fbar` of `F_p`.

Nothing here decides the target. What is proved:
- Section 0: exactness on one finite window of pairs is already fatal, for `Gamma` and for every finite-index
  subgroup (Lemma 0.1).
- Section 1: in any rank model, common invariant blocks of bounded dimension carry at most `m |R_0| eps` of the
  mass (Proposition 1.1).
- Section 2: a fixed finite-index subgroup can act by scalars only on a subspace of rank at most the defect
  (Proposition 2.1). Tensoring with exact finite-dimensional projective representations shifts the multiplier
  class and leaves the defect unchanged (Proposition 2.2).
- Sections 3 and 4 land separately: a rank version of the Schur-kernel transfer, conditional on a rank
  Gerstenhaber--Rothaus property, and where the attempt stops.

The common mechanism: a scalar mismatch on a subspace has rank equal to the dimension of that subspace. So
rank models see multipliers exactly on every sector where the operators involved act by scalars, and
Deligne's finite residual then applies with no analysis.

## 0. Conventions and the window lemma

A **model** on a finite `B <= Gamma` with `1 in B` is a map `rho : B -> GL_d(K)`, where `K` is a field of
characteristic `p` containing `w`. Its defect at `(g, h)` with `g, h, gh in B` is

```text
D_rho(g, h) = rank( rho(g) rho(h) - w^(j a(g,h)) rho(gh) ).
```

It is an **eps-model on** a set `R` of such pairs if `D_rho(g, h) <= eps d` for `(g, h) in R`. Rank-approximate
projective representations are eps-models on all pairs of `B`, for every `B` and `eps`. Rank does not change
under extension of scalars, so `K` may be taken finite or equal to `Fbar`.

For a finite-index `Lambda <= Gamma` let `E_Lambda` be its preimage in `E_3`. It contains `z` and has finite
index in `E_3`.

**Lemma 0.1 (window lemma).** For each finite-index `Lambda <= Gamma` there are a finite `B_Lambda <= Lambda`
containing `1` and a finite set `R_Lambda` of pairs `(g, h)` with `g, h, gh in B_Lambda` such that no field `K`
of characteristic `p` containing `w`, no `j in {1, 2}`, no nonzero finite-dimensional `W` and no map
`rho : B_Lambda -> GL(W)` satisfy

```text
rho(g) rho(h) = w^(j a(g,h)) rho(gh)     for all (g, h) in R_Lambda.          (EX)
```

*Proof.*
1. *Presentation.* `E_3` is finitely presented, being a finite central extension of the finitely presented
   `Sp_4(Z)` (Corollary S4b of `kl-schur-kernel-central-extensions-2026-09-11.md`). So its finite-index
   subgroup `E_Lambda` is finitely presented. Choose a finite symmetric `Y_Lambda <= Lambda` generating
   `Lambda`, and a finite presentation of `E_Lambda` on the generators `s(n)`, `n in Y_Lambda`, and `z`. Since
   `s(n)^(-1) = z^(-a(n, n^(-1))) s(n^(-1))`, every relator can be written as a positive word in these
   generators.
2. *Window.* For a relator `y_1 ... y_L`, write the value in `E_3` of the prefix `y_1 ... y_i` as
   `s(g_i) z^(k_i)`, with `g_0 = 1` and `k_0 = 0`.
   - Put `1`, all of `Y_Lambda` and all `g_i` into `B_Lambda`.
   - Put into `R_Lambda` the pair `(1, 1)` and, for every step with `y_(i+1) = s(n)`, the pair `(g_i, n)`.
     Then `g_i n = g_(i+1) in B_Lambda`.
3. *Evaluation.* Suppose (EX).
   - From `(1, 1)` and `a(1, 1) = 0`, `rho(1)^2 = rho(1)`, so `rho(1) = 1`.
   - Define `sigma(s(n)) = rho(n)` and `sigma(z) = w^j 1`. By induction on `i`,
     `sigma(y_1) ... sigma(y_i) = w^(j k_i) rho(g_i)`. A letter `z` multiplies both sides by `w^j` and raises
     `k_i` by one. A letter `s(n)` uses `s(g_i) z^(k_i) s(n) = s(g_i n) z^(k_i + a(g_i, n))` and (EX) at
     `(g_i, n)`.
   - At the end of a relator `g_L = 1` and `k_L = 0 mod 3`, so the relator evaluates to `rho(1) = 1`. Hence
     `sigma` is a homomorphism `E_Lambda -> GL(W)` with `sigma(z) = w^j 1 != 1`.
4. *Contradiction.* `sigma(E_Lambda)` is a finitely generated linear group, hence residually finite
   (`finitely-generated-linear-groups-are-residually-finite`). A finite quotient of it separating `sigma(z)`
   from `1` gives a finite-index `L <= E_Lambda` with `z notin L`. Then `L` has finite index in `E_3`, and its
   normal core in `E_3` is a finite-index normal subgroup missing `z`, against
   `deligne-triple-cover-finite-residual-is-center`. ∎

For `Lambda = Gamma` this is the finite-window form of Lemma 1.1 of the twisted-algebras artifact.

## 1. Bounded blocks carry vanishing mass

**Proposition 1.1** (`deligne-rank-models-carry-no-bounded-block-mass`). Put `B_0 = B_Gamma` and
`R_0 = R_Gamma`. Let `rho : B -> GL_d(K)` with `B >= B_0` be an eps-model on `R_0`, and suppose
`K^d = (+)_i V_i` with `rho(g) V_i = V_i` for all `g in B_0`. For `m >= 1` let `q_m` be the fraction of `d`
carried by the summands of dimension at most `m`. Then

```text
q_m <= m |R_0| eps.
```

*Proof.*
1. Each `rho(g)|_(V_i)` is injective, hence invertible. Each defect operator is block diagonal, so
   `D_rho(g, h) = sum_i D_i(g, h)`, where `D_i` is the defect of the restriction `rho_i` of `rho` to `V_i`.
2. Lemma 0.1 applied to `rho_i` gives, for every block, some `(g, h) in R_0` with `D_i(g, h) >= 1`.
3. So the number of blocks of dimension at most `m` is at most
   `sum_((g,h) in R_0) sum_i D_i(g, h) <= |R_0| eps d`, and `q_m d <= m |R_0| eps d`. ∎

*Consequences.*
- In any sequence of models with `eps -> 0`, the mass on blocks of dimension at most `m` tends to zero for
  every `m`, uniformly in the dimension and in the field.
- Direct sums of bounded-dimensional packets cannot give rank-approximate projective representations. That
  covers finite-field Weil or theta pieces and induced modules from bounded-index subgroups, and any
  bounded-degree construction. A model must be large-block on asymptotically all of its dimension.
- This is the rank analogue of `maslov-bounded-block-sector-gap`. There, compactness in each matrix size gives
  a constant `c_K` with no formula. Here integrality of rank gives the explicit constant `m |R_0|`.

## 2. Scalar data are rigid

**Lemma 2.0 (scalar mismatch).** If `V <= K^d` is invariant under `X` and `X|_V = mu 1_V` with `mu != 0`, then
`rank X >= dim V`. ∎

**Proposition 2.1** (`deligne-rank-models-have-no-fixed-level-scalar-sectors`). Let `Lambda <= Gamma` have finite
index, `B >= B_Lambda`, and `rho : B -> GL_d(K)` an eps-model on `R_Lambda`. Let `V <= K^d` be a subspace with
`rho(n) V = V` and `rho(n)|_V = lambda(n) 1_V` for every `n in B_Lambda`. Then `dim V <= eps d`.

*Proof.* For `(n, n') in R_Lambda` the defect operator restricted to `V` is
`(lambda(n) lambda(n') - w^(j a(n,n')) lambda(nn')) 1_V`. If `dim V > eps d`, Lemma 2.0 forces
`lambda(n) lambda(n') = w^(j a(n,n')) lambda(nn')` on `R_Lambda`. Then the one-dimensional map
`lambda : B_Lambda -> GL_1(K)` satisfies (EX), against Lemma 0.1. ∎

*Consequences and scope.*
- **Fixed congruence level.** Suppose the principal congruence subgroup `Gamma(m)` acts by scalars, for instance
  trivially, on a subspace of a model whose window contains `B_(Gamma(m))`. Then that subspace has rank at most
  the defect. So models assembled from representations of one finite quotient `Sp_4(Z/m)`, with the congruence
  kernel acting by scalars on a heavy sector, are dead.
- **Growing level.** `B_(Gamma(m))` grows with `m`. A family whose congruence level grows faster than its window
  escapes Proposition 2.1, and nothing here excludes it.
- **Comparison with the tracial setting.** In normalized Hilbert--Schmidt norm a scalar mismatch of size `delta`
  costs a fraction of the norm that shrinks with `delta`. Over a field in the rank metric any mismatch costs the
  whole sector, so the finite residual applies directly.

**Proposition 2.2** (`deligne-rank-realizability-is-invariant-under-fd-class-shifts`). Let `beta` be a normalized
2-cocycle of `Gamma` with values in `Fbar^x`, realized by an exact projective representation
`pi : Gamma -> GL_e(Fbar)`, `pi(g) pi(h) = beta(g,h) pi(gh)`. If a normalized cocycle `alpha'` has
rank-approximate projective representations in characteristic `p`, so do `alpha' beta` and `alpha' beta^(-1)`. So
does every cohomologous cocycle `alpha' . delta(lambda)`, `lambda : Gamma -> Fbar^x`.

*Proof.*
- For an eps-model `rho` of `alpha'` on `B`, put `rho' = rho (x) pi` on `B`. Then

  ```text
  rho'(g) rho'(h) - alpha'(g,h) beta(g,h) rho'(gh) = ( rho(g) rho(h) - alpha'(g,h) rho(gh) ) (x) beta(g,h) pi(gh),
  ```

  whose rank is `e` times the rank of the first factor. So the normalized defect is unchanged.
- The contragredient `pi^v(g) = (pi(g)^T)^(-1)` realizes `beta^(-1)`.
- Rescaling each `rho(g)` by `lambda(g)` turns an `alpha'`-model into an `alpha' . delta(lambda)`-model with the
  same defect. ∎

*Consequence.* Rank realizability of `w^(j a)` depends only on its class modulo the subgroup `R_p` of classes
realized by exact finite-dimensional projective representations over `Fbar`. Perturbing exact Weil or theta
representations of congruence quotients shifts the target class by an element of `R_p` and leaves the problem
exactly as hard. Over `C` the corresponding realizable subgroup is finite (`sp4-fd-projective-multiplier-is-finite`).
The analogous computation over `Fbar_p` has not been done here.
