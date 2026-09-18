---
rg: 2
id: kazhdan-torsion-free-tarski-monster-satisfies-kk-proof
kind: route
title: Interleave the finitely many spectral-witness radii of each hyperbolic stage into the relator lengths of the Olshanskii--Osin--Sapir torsion-free Tarski monster construction
target: kazhdan-torsion-free-tarski-monster-satisfies-kk
requires:
  - kk-witness-counterexample-locus-is-marked-closed
  - hyperbolic-bcc-finite-wreath-products
---

**Sources.**
- **[OOS]** A. Yu. Olshanskii, D. V. Osin, M. V. Sapir, *Lacunary hyperbolic groups*, Geom. Topol.
  13 (2009), 2051--2140; arXiv:math/0701365. The arXiv TeX source was downloaded on 2026-09-17 and
  read. The quotations below are verbatim from it.
- **[Ols]** A. Yu. Olshanskii, *On residualing homomorphisms and G-subgroups of hyperbolic groups*,
  Internat. J. Algebra Comput. 3 (1993), 365--409. It is used only as cited inside [OOS] and was
  not re-read here.

Notation as in `kk-witness-counterexample-locus-is-marked-closed`. `S` is the finite generating
set of `G`, `d = |S|`, and `F = F(S)`. `N_i = ker(F -> G(i))`, `B_r ⊆ F` is the ball of radius
`r`, and `ω_1, ω_2, ...` is an enumeration of all witnesses over `Q[i][F]`. For a group with only
trivial projections, `r(N, ω)` is the radius of item A.4 there.

## 1. The construction being modified (import)

[OOS], theorem `ExoticQuotients`, part 2:

> Let $G$ be an arbitrary torsion free non--cyclic hyperbolic group with a finite set of generators
> $S$. Then there exists an infinite non-Abelian torsion free quotient group $Q_2$ of $G$ admitting
> a \gsc presentation and such that all proper subgroups of $Q_2$ are cyclic.

Its proof:

> To construct $Q_2$ we denote by $\mathcal F$ the set of all 2-generated subgroups of $G$ and
> enumerate all elements $p_1, p_2, \ldots$ of the set $\mathcal P = S \times \mathcal F$. We set
> $G(0)=G$ and proceed by induction. Suppose that a (torsion--free) hyperbolic group $G(i-1)$ and
> relators $R_1, \ldots , R_{i-1}$ are already constructed. [...] we can choose a word $R_i$ of the
> form $R_i\equiv X_0U^mX_1U^m\ldots X_lU^m$, [...] such that the set of all cyclic shifts of
> $R_i^{\pm 1}$ satisfies a $C(\varepsilon, \mu, \lambda, c, \rho)$-condition. Here
> $\lambda=\lambda_i >0$, the positive $\mu=\mu_i$ can be selected arbitrary small, and then
> $c=c_i\ge 0$ arbitrary large, then $\varepsilon=\varepsilon_i$ can be chosen arbitrary large, and
> afterwards $m$, and therefore $\rho=\rho_i$, can be chosen arbitrary large. Such a choice of the
> parameters is guaranteed by lemmas 4.2 and 6.7 of \cite{Ols}. Then
> $G(i)=\langle G(i-1)|R_i\rangle$, and the group $Q_2$ is defined to be the limit of the sequence
> $G=G(0)\to G(1)\to \dots \to G(i)\to \dots$. Hence, as in the first part of the proof, one can
> choose the parameters so that $Q_2$ has a \gsc presentation. As in \cite[Corollary 1]{Ols}, $Q_2$
> is a non-Abelian torsion free group with cyclic proper subgroups.

What is used from this.
- **(I1)** Every stage `G(i)` is a torsion-free hyperbolic group. This is the induction hypothesis
  "(torsion--free) hyperbolic group $G(i-1)$", maintained as in [Ols, Corollary 1].
- **(I2)** At step `i`, `ρ_i` is chosen after `λ_i, μ_i, c_i, ε_i` and `G(i-1)`, and it may be
  taken larger than any prescribed bound. The requirements on `ρ_i` for the graded small
  cancellation presentation are lower bounds in terms of the earlier parameters:
  - `μ_nρ_n > Kε_n` in condition `Q_2` of the definition `classQ` of [OOS];
  - `ρ > 2μ^{-1}(c+2ε)` in Lemma `primyk`.
  Condition `Q_3` bounds the *next* `ε_{n+1}` from below. So one more lower bound on `ρ_i` is
  compatible with the construction, and the conclusions (torsion-free, proper subgroups cyclic,
  graded small cancellation) are unchanged.
- **(I3)** Lemma `old-gamma-cell` of [OOS], quoted:

  > For any hyperbolic group $H$ and any $\lambda>0$, there is $\mu_0>0$ such that for any
  > $\mu\in (0,\mu_0]$ and any $c\ge 0$, there are $\varepsilon\ge 0$ and $\rho>0$ with the
  > following property: Let a finite symmetrized presentation $H_1 = \langle H|{\cal R}\rangle$
  > satisfy the condition $C(\varepsilon,\mu,\lambda,c,\rho)$, and $\Delta$ a minimal diagram over
  > $H_1$ whose boundary is a product of $(\lambda,c)$-quasi-geodesic paths $p$ and $q$. Then
  > provided $\Delta$ has an $\cal R$-cell, there exists an $\cal R$-cell $\Pi$ in $\Delta$ and
  > disjoint $\varepsilon$-contiguity subdiagrams $\Gamma_1$ and $\Gamma_2$ (one of them may be
  > absent) of $\Pi$ to $p$ and $q$, respectively, such that
  > $(\Pi,\Gamma_1,p)+(\Pi,\Gamma_2, q)>1-23\mu$.

  [OOS] applies this lemma with `H = G(j-1)`, `H_1 = G(j)` and the parameters of step `j`, in the
  Morse part of the same proof ("Let $\Pi$, $\Gamma_1$, $\Gamma_2$ be the $\mathcal R_j$--cell of
  $\Delta$ and the $\e_j$--contiguity diagrams [...] provided by Lemma \ref{old-gamma-cell}").
- **(I4)** Two facts about the condition `C(ε, μ, λ, c, ρ)` of [Ols], used in the proof of Lemma
  `primyk` of [OOS]: every relator word has length `≥ ρ`, and subpaths of relator boundaries are
  `(λ, c)`-quasi-geodesic in `H` ("since the path $q_1$ is $(\lambda,c)$-quasi-geodesic").
- **Conventions** ([OOS], Section "The Greendlinger lemma"):
  - An `ε`-contiguity subdiagram `Γ` of `Π` to `q` is bounded by `s_1q_1s_2q_2`, where `q_1` is a
    subpath of `∂Π`, `q_2` a subpath of `q`, `max(|s_1|, |s_2|) ≤ ε`, and `Γ` has no `R`-cells.
  - The contiguity degree is `(Π, Γ, q) = |q_1| / |∂Π|`.
  - A path is `(λ, c)`-quasi-geodesic when `λ|r| - c ≤ dist(r_-, r_+)` for its subpaths `r`.

## 2. Stages have only trivial projections

By (I1), each `G(i)` is torsion-free hyperbolic. By `hyperbolic-bcc-finite-wreath-products`, it
satisfies Baum--Connes with coefficients, so its assembly map is surjective. Kaad--Proietti,
*Index theory on the Miščenko bundle*, Kyoto J. Math. 62 (2022), Corollary 1.6, then gives only
the idempotents `0, 1` in `C*_r(G(i))`. This step is recorded as in
`rank-one-bcc-implies-charzero-idempotent-proof` and in item A.5 of
`kk-witness-counterexample-locus-is-marked-closed-proof`.

## 3. Injectivity radius of one step

**Lemma.** Let `H = G(i-1)` and `H_1 = G(i) = <H | R_i>`, where the cyclic shifts of `R_i^{±1}`
satisfy `C(ε, μ, λ, c, ρ)` with the parameters of (I3). Then every `g ≠ 1` in
`ker(H -> H_1)` has `|g|_S > λ(1 - 23μ)ρ - 2c - 4ε`.

*Proof.*
1. Let `W` be a geodesic word for `g` in `H`, and write `W ≡ W_1W_2` with `|W_1|, |W_2|` differing
   by at most `1`. Subwords of geodesic words are geodesic, hence `(λ, c)`-quasi-geodesic (a
   quasi-geodesic constant satisfies `λ ≤ 1` for any path of positive length).
2. Take a minimal diagram `Δ` over `H_1` with boundary `pq`, where `Lab(p) ≡ W_1` and
   `Lab(q) ≡ W_2`. It has an `R`-cell: otherwise it is a diagram over `H` and `g = 1` in `H`.
3. By (I3) there are an `R`-cell `Π` and disjoint contiguity subdiagrams `Γ_1, Γ_2` to `p, q`,
   with degrees `ψ_1 + ψ_2 > 1 - 23μ` (with `ψ_k = 0` if `Γ_k` is absent).
4. Fix `k` with `Γ_k` present, bounded by `s_1q_1s_2q_2`. Since `Γ_k` has no `R`-cell, the label
   of `q_2` equals that of `s_2^{-1}q_1^{-1}s_1^{-1}` in `H`, up to orientation. So
   `|q_2| ≥ dist_H(q_2 endpoints) ≥ dist_H(q_1 endpoints) - 2ε ≥ λ|q_1| - c - 2ε
   = λψ_k|∂Π| - c - 2ε`, using (I4). This is the estimate "$|q_2|\ge \lambda\psi|\partial\Pi|-c-2\varepsilon$"
   in the proof of Lemma `primyk` of [OOS].
5. The two contiguity arcs on `pq` are disjoint subpaths of `p` and of `q`, and `|∂Π| ≥ ρ` by (I4).
   So `|g| = |W| ≥ λ(ψ_1 + ψ_2)ρ - 2c - 4ε > λ(1 - 23μ)ρ - 2c - 4ε`. ∎

**Corollary.** If `λ(1 - 23μ)ρ - 2c - 4ε ≥ r`, then `N_i ∩ B_r = N_{i-1} ∩ B_r`. Indeed, a word
`w ∈ N_i \ N_{i-1}` with `|w| ≤ r` represents `g ≠ 1` in `ker(G(i-1) -> G(i))` with `|g| ≤ r`,
which contradicts the Lemma.

## 4. The interleaving

Run the construction of §1 and add one requirement at each step `i ≥ 1`. After `G(i-1)` and
`λ_i, μ_i, c_i, ε_i` are fixed, put

```text
r_i = max( r_{i-1},  max_{k ≤ i} r(N_{i-1}, ω_k) ),     r_0 = 0,
```

which is finite because `G(i-1)` has only trivial projections (§2, item A.4). Then choose `ρ_i`
(through `m`) so large that `λ_i(1 - 23μ_i)ρ_i - 2c_i - 4ε_i ≥ r_i`, besides the requirements of
[OOS]. This is possible by (I2). By the Corollary of §3, the injectivity radius of
`G(i-1) -> G(i)` on `B_{r_i}` is at least `r_i`, and `r_i` is nondecreasing and dominates every
`r(N_{i-1}, ω_k)` with `k ≤ i`.

All stages have only trivial projections (§2). So item A.6 of
`kk-witness-counterexample-locus-is-marked-closed` applies: the limit `Q = F / ∪N_i` lies in no
`P_ω`. By item A.3, `C*_r(Q)` has no projection other than `0, 1`. By (I2), `Q` is still a
torsion-free non-abelian group with cyclic proper subgroups and a graded small cancellation
presentation. It is lacunary hyperbolic by [OOS], Lemma `asc` (items (a), (c), (d): `δ_n = o(ρ_{n+1})`
and every nontrivial kernel element of `G_n -> G_{n+1}` has length `≥ (1 - o(1))ρ_{n+1}`) together
with Theorem `dl2` there (direct limits of hyperbolic groups whose injectivity radii outgrow the
hyperbolicity constants are lacunary hyperbolic). This proves items 1--3 of
the claim.

The characteristic-zero algebraic consequence follows as in
`rank-one-bcc-implies-charzero-idempotent-proof`. An idempotent of `k[Q]` has finitely many
coefficients, so it lives over a finitely generated subfield, which embeds in `C`. An idempotent
`e` of `C[Q] ⊆ C*_r(Q)` is similar in `C*_r(Q)` to a projection `p` (Kaplansky), and `p ∈ {0, 1}`
forces `e ∈ {0, 1}`.

## 5. The corollary

Let `G` be a torsion-free cocompact lattice in `Sp(n,1)`, `n ≥ 2`.
- Cocompact lattices in `Sp(n,1)` exist (arithmetic constructions), and Selberg's lemma gives a
  torsion-free finite-index subgroup.
- It is hyperbolic: it acts properly and cocompactly on quaternionic hyperbolic space, which is
  negatively curved.
- It is non-elementary (not virtually cyclic), so non-cyclic.
- It has property (T) (Kostant; Kazhdan).

The quotient `Q` then inherits (T), since a quotient of a Kazhdan group is Kazhdan. The remaining
bullets of the claim use only item 1:
- *No free subgroup, not amenable.* `F_2 ≤ Q` would be a proper subgroup (an infinite Kazhdan
  group is not free) that is not cyclic, contradicting item 1. An infinite Kazhdan group is not
  amenable, so `Q` is not virtually solvable.
- *Not hyperbolic.* A hyperbolic group is virtually cyclic (hence amenable) or contains `F_2`.
- *Not linear.* A finitely generated linear group is virtually solvable or contains `F_2` (Tits).
- *No proper action on a CAT(0) cube complex, not a-T-menable.* An infinite Kazhdan group has
  neither.

## 6. Scope and caveats

- **Imports.** (I1) and (I2) are quoted from [OOS] and rest on [Ols], Corollary 1 and Lemmas 4.2
  and 6.7, which were not re-read. The only new mathematical input is §3 (from (I3), (I4)) and §4.
- **Where the method stops.** The radius `r(N_{i-1}, ω_k)` depends on the stage, and nothing
  bounds it uniformly. So the argument gives KK for *suitably chosen* direct limits, not for every
  graded small cancellation or lacunary hyperbolic limit. A quantitative bound for torsion-free
  `δ`-hyperbolic groups, `r(N, ω) ≤ R(d, δ, ω)` with `R` of order `δ`, would be the natural input for
  extending this to every torsion-free lacunary hyperbolic group with `δ_i = o(r_S(G(i-1) -> G(i)))`.
- **Matrix form (remark, not established).** Replace witnesses by self-adjoint matrices
  `a ∈ M_n(Q[i][F])` and the window `[δ, 1-δ]` by `[k+δ, k+1-δ]`, `0 ≤ k < n`. The proofs of
  A.2--A.4 and A.6 go through verbatim with `τ_N ⊗ Tr`. The interleaving then yields
  `τ_*(K_0(C*_r(Q))) ⊆ Z` as soon as every stage has integer traces on matrix projections. For
  torsion-free hyperbolic groups, that integrality follows from assembly surjectivity and the
  `L²`-index theorem (Lück, Invent. Math. 149 (2002)), not re-read here. By
  `free-product-kk-iff-trace-conjecture-for-factors`, that would also give the root for `Q * Z`.
