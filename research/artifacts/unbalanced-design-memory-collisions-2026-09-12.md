# Unbalanced designs: memory letters certify strictness, and the screens a biased rule must pass

Lane `w3-bal-design`, 2026-09-12. Handwritten proofs; nothing was run. Supports
`unbalanced-effective-rule-certifies-strictness`, `unbalanced-forward-tables-identify-memory-letters`,
`gottschalk-via-unbalanced-table-memory-collisions` and
`unbalanced-table-memory-collisions-from-gottschalk`.

## 0. Conventions

These are the conventions of `canonical-table-groups-for-automaton-designs-2026-09-12.md`:
- designs `D = (A, S, M, nu, mu)`;
- realizations `rho`, forward tables `E_rho`, the up-set `𝓕_D`;
- table groups `U_E` with the realization `rho_E(a) = x_a`, where `x_(1_S)` and `x_(1_M)` are the empty word;
- the memory convention `tau(x)(g) = mu((x(g rho(m)))_(m in M))`.

- A rule `mu : A^M -> A` is **balanced** if `|mu^-1(a)| = |A|^(|M|-1)` for every `a`.
- The **collision partition** `kappa_rho` of `M` puts `m ~ m'` iff `rho(m) = rho(m')`. Let `q : M -> M/kappa_rho` be the quotient map. The **effective rule** is
  `mu_rho : A^(M/kappa_rho) -> A`, `mu_rho(z) = mu(z o q)`.
  So `tau_rho` is the automaton whose memory is the set `rho(M)`, of `|M/kappa_rho|` distinct
  elements, with rule `mu_rho`.
- For `E` in `𝓕_D`, write `kappa_E` for the collision partition of the letters `x_m` in `U_E`, and `mu_E` for the effective rule over `U_E`.

Let `lambda` be the uniform product measure. Distinct sites carry independent uniform symbols. So
`tau_rho(x)(g)` has law `(mu_rho)_*` of the uniform law on `A^(M/kappa_rho)`, and that law is
uniform iff `mu_rho` is balanced.

## 1. Balance certifies strictness, and only memory letters need checking

**Proposition 1 (balance certificate).** Let `E` be in `𝓕_D` and let `rho` be a realization with
`E_rho >= E`. If `mu_rho` is not balanced, then `tau_rho` is injective and not surjective.

*Proof.* Lemmas 1 and 2 of the canonical-table artifact give `sigma_rho tau_rho = id`, so `tau_rho`
is injective. Suppose `tau_rho` were surjective. Then it is bijective, and by
`bijective-ca-preserve-uniform-bernoulli-measure`, `(tau_rho)_* lambda = lambda`. The one-site
marginal of `(tau_rho)_* lambda` would then be uniform, so by Section 0 `mu_rho` is balanced. QED

**Corollary 2 (hinge-free strictness over the table group).** Let `E` be in `𝓕_D`. If `mu_E` is not
balanced, then `tau` over `U_E` is strict, and `U_E` is not surjunctive. In particular, if `mu` is
not balanced and the elements `1` and `x_m` (`m` in `M'`) are pairwise distinct in `U_E`, then `U_E`
is not surjunctive.

*Proof.* `E_(rho_E) >= E` by Lemma 5 there, and `kappa_(rho_E) = kappa_E`. Apply Proposition 1. QED

Compare Proposition C of the canonical-table artifact. There, strictness needs a surviving hinge
word `x_s'^-1 x_m'^-1 x_m x_s` for every minimal reverse partition. For an unbalanced rule no reverse
product is examined: the words `x_m^-1 x_m'` (with `x_(1_M) = 1`) suffice. In the holonomy normal
form (`table-groups-are-memory-holonomy-groups`) these are the generators of `Hol_M(E)` and their
pairwise quotients.

**Theorem 3 (Gottschalk as a memory-collision statement).** The following are equivalent.
1. Every group is surjunctive over every finite alphabet.
2. For every design `D` whose encoder rule `mu` is not balanced, and every minimal `E` in `𝓕_D`,
   two of the elements `1`, `x_m` (`m` in `M'`) coincide in `U_E`.

Group by group: `G` is surjunctive over every alphabet iff no design with unbalanced `mu` has a
realization in `G` with forward table in `𝓕_D` and `rho` injective on `M`.

*Proof.*
- **(1) implies (2).** If the elements are pairwise distinct in `U_E`, Corollary 2 makes `U_E` non-surjunctive.
- **(2) implies (1).** Let `tau` on `A^G` be injective and not surjective.
  - By `strict-automata-give-injective-ca-with-skewed-site-marginals` there is an injective `kappa`
    on `B^G`, `B = A^(k+1)`, whose one-site law is not uniform.
  - Let `M ⊂ G` be its memory, adjoining `1` as an unread address if needed, and `mu` its rule. `mu`
    is not balanced, because its pushforward of the uniform law is that one-site law, and adjoining
    an unread uniform coordinate does not change the law.
  - By Lemma 4 of the canonical-table artifact `kappa` has a left inverse with a finite memory `S`
    containing `1` and a rule `nu`. Put `D = (B, S, M, nu, mu)` with `rho` the inclusion.
  - Lemma 1 gives `E_rho` in `𝓕_D`. The lattice of marked partitions of `S x M` is finite, so some
    minimal `E` in `𝓕_D` has `E <= E_rho`.
  - Lemma 5 gives `pi : U_E -> G` with `pi(x_m) = m`. The elements of `M` are distinct in `G`, so
    `1` and the `x_m` are pairwise distinct in `U_E`. This contradicts (2).
- **Group by group.** The second argument produces the realization in `G` itself, with `rho`
  injective on `M`. Conversely, such a realization has `mu_rho = mu`, which is unbalanced, so by
  Proposition 1 `tau_rho` is strict. QED

**Remarks.**
- **What Theorem 3 changes.** Corollary B of the canonical-table artifact asks that, for every
  design and minimal `E`, the reverse table of `U_E` be reverse sufficient. Theorem 3 keeps only
  unbalanced rules and asks for one memory collision instead. Reverse products never enter.
- **Known collisions.**
  - **Triangular `E`.** Theorem D there makes every realization bijective, hence balanced, so an
    unbalanced rule over a triangular `E` collides memory letters.
  - **Amenable decoder holonomy `Hol_S(E)`.** The same holds by `amenable-decoder-memory-forces-surjectivity`.
  - **Connected `Gamma_E` with `b_1 <= 1`.** Distinct letters would give a non-sofic one-relator
    group (`unicyclic-strict-designs-present-nonsofic-one-relator-groups`).
- **Sofic quotients.** Let `Q` be a sofic quotient of `U_E`. The images of the letters realize `D`
  with forward table `>= E`, and `Q` is surjunctive, so by Proposition 1 the effective rule over `Q`
  is balanced. Every sofic quotient therefore identifies memory letters, in a pattern that balances
  `mu`. The abelianization is one such quotient, and it can be computed from `E` by linear algebra.
- **Robustly unbalanced rules.** Call `mu` robustly unbalanced if `mu_kappa` is unbalanced for every
  partition `kappa` of `M` with at least two classes. Then every sofic quotient of `U_E` kills every
  memory letter. When `Gamma_E` is connected, `U_E = Hol_M(E)` is generated by those letters
  (Corollary C' of the holonomy artifact), so `U_E` has no nontrivial sofic quotient.
  - **A criterion over `F_2`.** Write `mu = sum_T c_T x^T` in algebraic normal form. The weight of
    `mu_kappa` is odd iff `sum_(T ⊆ M, q(T) = M/kappa) c_T = 1`, since the weight's parity is the
    coefficient of the top monomial. A rule with at least two variables and odd weight is
    unbalanced.
  - **Examples.** Every rule of the form "affine part plus the top monomial `x^M`" is robustly unbalanced.
  - **Where this bites.** The screen is vacuous over groups with only trivial sofic morphisms, such as
    `R^x` (`leavitt-unit-group-has-only-trivial-sofic-morphisms`). Those are exactly the hosts where
    robustly unbalanced designs are not excluded.
