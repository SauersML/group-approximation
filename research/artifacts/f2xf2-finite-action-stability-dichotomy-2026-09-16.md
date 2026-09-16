# F2 x F2: stability in finite actions versus Păunescu's class (2026-09-16)

This is lane `swarm-f2xf2-in-paunescu-class`. The target `f2xf2-in-paunescu-class` (every p.m.p. action of
`Γ = F_2 × F_2` is sofic) is still **OPEN**.

What this file proves:

* **Proposition A.** Stability in finite actions of a group passes from limit actions of sofic
  approximations to every Păunescu-sofic action on a standard space.
* **Corollary B.** Under stability in finite actions, an action not weakly contained in finite actions is
  nonsofic, and so is its free profinite upgrade.
* **Theorem C.** For `F_2 × F_2`, the target and stability in finite actions cannot both hold. So a proof of
  the target would answer Gohla--Thom Question 3.12 positively with an explicit residually finite group.

## 0. Sources

All quotes are verbatim. They were read on 2026-09-16 from the arXiv PDFs through `pypdf`, with ligatures
normalised.

### 0.1 Păunescu's definition

Păunescu, arXiv:1002.0605, Definition 1.4. It is quoted verbatim, together with Kun--Thom
arXiv:2608.06222 Definition 2.2, in `research/artifacts/kun-thom-2608-06222-verified.md` ("Păunescu's
notion"):

> An action α of a countable group G on a standard Borelian space (X,ℬ,μ) is called *sofic* if the crossed
> product L^∞(X)⋊_α G embeds in Π_{k→ω}M_{n_k}(ℂ) such that L^∞(X)⊂Π_{k→ω}D_{n_k}(ℂ) and
> G⊂Π_{k→ω}P_{n_k}(ℂ).

Here the embedding is unital, trace-preserving and `*`. `P_{n_k}` is the group of permutation matrices and
`D_{n_k}` the diagonal matrices.

### 0.2 Gohla--Thom, arXiv:2403.09582v2, *High-dimensional expansion and soficity of groups*

> **Definition 3.7.** We say that a group Γ is stable in finite actions if the limit action of any sofic
> approximation is weakly contained in the family of finite Γ-actions. Equivalently, the limit action of any
> sofic approximation of Γ is contained in a metric ultraproduct of finite Γ-actions.

> **Lemma 3.8.** Let Γ be a countable discrete group. Consider the following conditions:
> (i) The group Γ be stable in finite actions.
> (ii) For all K ⊂ Γ finite, d ∈ N, and ε > 0, there exists δ > 0 and F ⊂ Γ finite, such that for every
> n ∈ N, every map ϕ : Γ → Sym(n) satisfying d_n(ϕ(gh),ϕ(g)ϕ(h)) < δ ∀g,h ∈ F and d_n(1_n,ϕ(g)) > 1 − δ
> ∀g ∈ F \ {1_Γ}, and any partition {1,...,n} = A_1 ∪ ··· ∪ A_d, there exists a finite set X, a
> homomorphism ψ : Γ → Sym(X), and a partition X = B_1 ∪ ··· ∪ B_d such that
> | |A_i ∩ ϕ(g)A_j|/n − |B_i ∩ ψ(g)B_j|/|X| | < ε, ∀i,j ∈ {1,...,d}, g ∈ K.
> (iii) For all K ⊂ Γ finite and ε > 0, there exists δ > 0 and F ⊂ Γ finite, such that for every n ∈ N and
> every map ϕ : Γ → Sym(n) satisfying [the same two conditions], there exists m ∈ N, a set X of cardinality
> in [nm, (1+ε)nm], a subset X_0 ⊆ X of cardinality nm, a m-1-map π : X_0 → {1,...,n}, and a homomorphism
> ψ : Γ → Sym(X) such that |{x ∈ X_0 | π(ψ(g)x) ≠ ϕ(g)π(x)}| < ε|X_0|, ∀g ∈ K.
> Then, the following implications hold: (i) ⇔ (ii) ⇐ (iii).

Theorem 3.9, hypothesis (iii): "The group H is residually finite and amenable." Theorem 3.11, hypothesis
(iii): "The group Γ/Λ is amenable." Just after Theorem 3.9: "F2 × Z is an example of a group which is stable
in finite actions, but not flexibly stable".

> **Question 3.12.** Is there a residually finite group, which is not stable in finite actions?
> We believe the answer to this question should be positive; but it seems hard to come up with a concrete
> example, see also Remark 3.16.

Remark 3.14 (excerpts):

> By a result of Abért–Weiss [1], the Bernoulli action Γ ↷ ({0,1}^Γ, ν^{⊗Γ}) is weakly contained in any other
> free p.m.p. action. In particular, since Γ is residually finite, it is weakly contained in the pro-finite
> action Γ ↷ (Γ̂, μ_Haar).

> There is also a notion of soficity of a p.m.p. Γ-action on a standard probability space, see [15,
> Definition 1.3], which amounts to weak containment in the limit action of a sofic approximation of the
> group Γ.

Here [15] is Elek--Lippner, *Sofic equivalence relations*, J. Funct. Anal. 258 (2010).

> **Remark 3.16.** There are only few groups Γ for which all p.m.p. Γ-actions are weakly contained in the
> family of finite actions. Any such group is clearly stable in finite actions. These include free groups,
> surface groups, hyperbolic 3-manifold groups [8] and residually finite amenable groups but likely no groups
> with Kazhdan's property (T), see the discussion in [26, p. 465]. In particular, it is known that SL_n(Z)
> fails to have this property for n ≥ 3, see [30]. Thus, potentially, if any Kazhdan group can be shown to be
> stable in finite actions, then there exists a non-sofic p.m.p. action. Another test case for stability in
> finite actions is the group F2 × F2. By the recent refutation of the Connes' Embedding Conjecture [23], there
> do exist p.m.p. actions of F2 × F2 that are not weakly contained in finite actions. Again, any such action
> would be non-sofic if F2 × F2 was stable in finite actions.

Here [23] is Ji--Natarajan--Vidick--Wright--Yuen, MIP* = RE, arXiv:2001.04383.

### 0.3 Fournier-Facio--Willett, arXiv:2603.18456v2

*The Local Lifting Property, Property FD, and stability of approximate representations.*

> **Definition 5.8.** A group Γ has property FD … if the collection S of representations of Γ that factor
> through a finite quotient is dense in the Fell topology

> **Definition 5.10.** A group Γ is residually finite-dimensional (RFD) if the collection of finite-dimensional
> representations is dense in the Fell topology. As any representation that factors through a finite quotient
> decomposes as a direct sum of finite-dimensional representations, this is a weaker property than FD.

> **Remark 5.23.** The product F2×F2 is a free product of F2×Z with itself, amalgamated along a common copy of
> F2, which is a retract. Due to the negative solution of the Connes embedding problem [54], F2×F2 is not RFD
> [155] (and so also not FD).

Here [54] is de la Salle (Séminaire Bourbaki) and [155] is Ozawa, "About the QWEP conjecture", IJM 15 (2004).

Appendix A:

> **Definition A.1.** Let Γ be a finitely generated residually finite group. We say that Γ has property MD if
> every p.m.p. action of Γ is a weak limit of finite actions.

Page 68: "As remarked by Kechris [113], property MD implies property FD".

Remark A.4 (excerpt): "The definition is the same as property MD, except only for the p.m.p. actions arising
from sofic representations, hence property MD implies stability in finite actions by definition."

### 0.4 Alekseev--Thom, arXiv:2512.15494v1

*Remarks on approximability and stability for groups.*

> **Corollary C.** There exists a hyperbolic group that cannot be stable in finite actions, provided it is
> residually finite.

The introduction says: "it is also open whether there exists a residually finite group that is not stable in
finite actions; see the work of Gohla and the second author [13]."

### 0.5 Ioana, arXiv:2008.00554v2, *On sofic approximations of F2 × F2*

> **Theorem 1.5.** Let Γ = Fm × Fk, for some integers m,k ≥ 2. Then Γ admits a sofic approximation
> σn : Γ → Sym(Xn) with the following property: there are no homomorphisms τn : Γ → Sym(Yn) and maps
> θn : Xn → Yn, for some finite sets Yn, such that (a) lim dH(θn∘σn(g), τn(g)∘θn) = 0, for all g ∈ Γ, and
> (b) lim dH(θn∘σn(g), θn) = 1, for all g ∈ Γ \ {e}.

On [Io19b] = arXiv:1909.00282:

> [Io19b, Theorem D] shows that Γ = Fm × Fk is not weakly very flexibly stable … This amounts to the
> existence of a sofic approximation σn : Γ → Sym(Xn) with the following property: (⋆) there are no finite
> sets Yn, homomorphisms τn : Γ → Sym(Yn) and one-to-one maps θn : Xn → Yn such that
> lim dH(θn∘σn(g), τn(g)∘θn) = 0, for every g ∈ Γ.

## 1. Conventions

`Γ` is a countably infinite group. A **finite action** is a homomorphism `Γ → Sym(Y)`, with `Y` finite and
carrying the normalised counting measure. `F(Γ)` denotes the family of finite actions.

**(WC) Weak containment.** Let `a = Γ ↷ (X, μ)` be a p.m.p. action on a probability space, not necessarily
standard, and let `𝓕` be a family of p.m.p. actions. Then `a ≺ 𝓕` means the following. For all measurable
`A_1, …, A_r ⊆ X`, finite `K ⊆ Γ` and `ε > 0`, there are `b = Γ ↷ (Y, ν)` in `𝓕` and measurable
`B_1, …, B_r ⊆ Y` with

```text
| μ(g A_i ∩ A_j) − ν(g B_i ∩ B_j) | < ε        for all g ∈ K, i, j ≤ r.
```

This is Kechris's definition, extended to families as in FFW (12). For `𝓕 = F(Γ)`, allowing finite convex
combinations of members changes nothing:

* rational combinations of finite actions are finite actions (replicate each `Y_i`);
* statistics depend continuously on the weights.

Only measure-algebra actions are used, so an action defined modulo null sets is enough.

Three elementary facts:

* **(T) Transitivity.** If `a ≺ b` and `b ≺ 𝓕` then `a ≺ 𝓕`. Reproduce the statistics in `b` to within
  `ε/2`, then reproduce those in a member of `𝓕` to within `ε/2`.
* **(Fac) Factors.** If `π : (Y, ν) → (X, μ)` is a factor map of actions `b → a`, then `a ≺ b`. Take
  `B_i = π^{-1}(A_i)`.
* **(Den) Density.** Suppose `{E_i}` is dense in the measure algebra of `(X, μ)`, and `μ(A_j Δ E_{i_j}) < η`.
  Then `|μ(g A_j ∩ A_k) − μ(g E_{i_j} ∩ E_{i_k})| < 2η`. So in (WC) it suffices to take the `A_j` among the
  `E_i`.

**Limit action.** Let `ν` be a free ultrafilter on `N` and `τ_m : Γ → Sym(V_m)` a sofic approximation. This
means:

* `lim_m d_H(τ_m(gh), τ_m(g)τ_m(h)) = 0`;
* `lim_m d_H(τ_m(g), id) = 1` for `g ≠ 1`;
* `|V_m| → ∞`.

The **limit action** is the action of `Γ` on the Loeb space `(Π_ν V_m, μ_ν)` by
`g·[(x_m)] = [(τ_m(g) x_m)]`. It is an action on the measure algebra, because the defect sets have Loeb
measure `0`.

For internal sets `Â = [(A_m)]` and `Â' = [(A'_m)]`, the set `g Â'` is `[(τ_m(g) A'_m)]`, and
`μ_ν(Â ∩ g Â') = lim_ν |A_m ∩ τ_m(g) A'_m| / |V_m|`.

When the right side converges as an honest limit, the value does not depend on `ν`. So the proof below works
whichever free ultrafilter Gohla--Thom use to form limit actions.

**Matching Gohla--Thom's printed convention (referee addition, 2026-09-16).** GT §3.1 sets up sofic
approximations only for a *finitely presented* `Γ = F/⟨⟨R⟩⟩`: homomorphisms `σ_n : F → Sym(k_n)` with
`ℓ(σ_n(r)) → 0` for `r ∈ R` and `ℓ(σ_n(w)) → 1` for `w ∉ ker π`. Their limit action is the metric
ultraproduct of the measured Boolean algebras `2^{[k_n]}` (GT §2), and GT Definition 2.2 defines weak
containment as containment in a metric ultraproduct of members of the family. Alekseev--Thom
(arXiv:2512.15494v1, Definition 3.1) restate Definition 3.7 for arbitrary countable groups. The conventions
agree:

* For finitely presented `Γ`, a free-group sofic representation gives maps `ϕ_n(g) = σ_n(s(g))` through a
  set-theoretic section `s`. These are asymptotically multiplicative, since `s(g)s(h)s(gh)^{-1}` is a fixed
  product of conjugates of relators. They are asymptotically free. Conversely, maps `ϕ_n : Γ → Sym(n)` give
  `σ_n(x_i) = ϕ_n(π(x_i))` on free generators, and `σ_n(w) ≈ ϕ_n(π(w))` for each fixed word. In both
  directions the Γ-actions on the ultraproduct agree up to Hamming-null defects. This covers `F_2 × F_2`.
* The measure algebra of the Loeb space is the metric ultraproduct, because every Loeb-measurable set agrees
  a.e. with an internal set. The proof below uses only internal sets anyway.
* The direction of weak containment used in step 2 of the proof is "contained in a metric ultraproduct ⇒
  (WC)". Given `B_1, …, B_r` with images `[X^i_j]_j`, one has
  `μ_U(gφ(B_i) ∧ φ(B_k)) = lim_U μ_j(g X^i_j ∧ X^k_j)`, so some index `j` reproduces finitely many statistics
  to within `ε`. This needs no separability of `P`.

**Normalisations.**

* `d_H(σ, σ') = |{x : σx ≠ σ'x}| / n`.
* `tr` is the normalised trace.
* `‖x‖_2 = tr(x*x)^{1/2}`.
* `P_σ e_x = e_{σx}`, so `P_σ P_{σ'} = P_{σσ'}`.
* In the crossed product, `u_g f u_g* = f∘g^{-1}`, so `u_g 1_E u_g* = 1_{gE}`, and `τ(f u_g) = δ_{g,1} ∫ f dμ`.

## 2. Proposition A: stability in finite actions reaches every sofic action

**Proposition A.** Let `Γ` be a countably infinite group that is stable in finite actions, and let
`a = Γ ↷ (X, μ)` be a p.m.p. action on a standard probability space that is sofic in the sense of Păunescu
Definition 1.4. Then `a ≺ F(Γ)`.

Fix a unital, trace-preserving `*`-embedding `Θ : L^∞(X) ⋊ Γ → M := Π_ω M_{n_k}` with
`Θ(L^∞(X)) ⊆ Π_ω D_{n_k}` and `Θ(u_g) ∈ Π_ω P_{n_k}`. Here `ω` is an ultrafilter on `N`, and the proof does not
use that `ω` is free. Write `τ_ω` for the trace of `M`.

**Lemma 1 (sets).** For every Borel `E ⊆ X` there are sets `A_k ⊆ {1, …, n_k}` with `Θ(1_E) = [(1_{A_k})]`.

*Proof.*

1. `p = Θ(1_E)` is a projection in `Π_ω D_{n_k}`. Choose a representative `(b_k)` that is bounded in operator
   norm, and replace `b_k` by its self-adjoint part.
2. Let `f(t) = min(max(t, 0), 1)`. Polynomials commute with the quotient map. On a bounded interval `f` is a
   uniform limit of polynomials, and `‖·‖_2 ≤ ‖·‖_∞`. So `[(f(b_k))] = f(p) = p`.
3. Put `a_k = f(b_k)`. This is diagonal with entries in `[0, 1]`, and `p = p²` gives
   `lim_ω ‖a_k − a_k²‖_2 = 0`.
4. Let `A_k = {x : a_k(x) ≥ 1/2}`. Pointwise `|1_{A_k} − a_k| ≤ 2(a_k − a_k²)`:
   * if `a ≥ 1/2`, then `1 − a ≤ 2a(1 − a)`;
   * if `a < 1/2`, then `a ≤ 2a(1 − a)`.
5. Hence `‖1_{A_k} − a_k‖_2 ≤ 2 ‖a_k − a_k²‖_2 → 0` along `ω`. ∎

**Lemma 2 (group elements).** Choose permutations `σ_k(g) ∈ Sym(n_k)` with `Θ(u_g) = [(P_{σ_k(g)})]` and
`σ_k(1) = id`. This is allowed because `Θ(u_1) = 1 = [(P_id)]`. Then:

```text
lim_ω d_H(σ_k(gh), σ_k(g)σ_k(h)) = 0,        lim_ω d_H(σ_k(g), id) = 1   for g ≠ 1.
```

*Proof.*

* For permutation matrices, `‖P_σ − P_{σ'}‖_2² = 2 − 2 tr(P_σ* P_{σ'}) = 2 − 2 |Fix(σ^{-1}σ')| / n = 2 d_H(σ, σ')`.
* `Θ` is multiplicative, so `‖P_{σ_k(gh)} − P_{σ_k(g)σ_k(h)}‖_2 → 0` along `ω`.
* For `g ≠ 1`, trace preservation gives `lim_ω |Fix σ_k(g)| / n_k = τ_ω(Θ(u_g)) = τ(u_g) = 0`. ∎

This holds whether or not `a` is free: freeness of the lifted permutations comes from the trace.

**Lemma 3 (statistics).** Take `E, E'` Borel, with `A_k` and `A'_k` from Lemma 1. Then for all `g`:

```text
μ(E ∩ gE') = lim_ω |A_k ∩ σ_k(g) A'_k| / n_k.
```

*Proof.*

* `1_{E ∩ gE'} = 1_E u_g 1_{E'} u_g*`.
* `P_σ 1_A P_σ* = 1_{σA}`.
* `Θ(u_g)* = [(P_{σ_k(g)}*)]`.
* Apply `τ` and trace preservation:
  `μ(E ∩ gE') = τ_ω(Θ(1_E) Θ(u_g) Θ(1_{E'}) Θ(u_g)*) = lim_ω tr(1_{A_k} 1_{σ_k(g) A'_k})`. ∎

**Lemma 4 (sizes).** `{k : n_k ≥ m} ∈ ω` for every `m`.

*Proof.* Suppose not. Then `n_k = n` on a set in `ω`. For each `g`, the values `σ_k(g)` range over the finite
set `Sym(n)`, so some `s(g)` satisfies `{k : σ_k(g) = s(g)} ∈ ω`. The ultralimits in Lemma 2 are then exact:

* `s` is a homomorphism;
* `s(g)` has no fixed points for `g ≠ 1`.

So `s` is injective and `Γ` embeds in `Sym(n)`, contradicting that `Γ` is infinite. ∎

**Proof of Proposition A.**

*Setup.* `X` is standard, so its measure algebra is separable. Fix a dense sequence `E_1, E_2, …` in it, and an
enumeration `g_1 = 1, g_2, …` of `Γ`. For each `i`, let `A^{(i)}_k` be the sets given by Lemma 1 for `E_i`.

*Good indices.* For `m ≥ 1`, let `J_m` be the set of `k` such that:

* `n_k ≥ m`;
* `d_H(σ_k(g_a g_b), σ_k(g_a)σ_k(g_b)) < 1/m` for `a, b ≤ m`;
* `d_H(σ_k(g_a), id) > 1 − 1/m` for `2 ≤ a ≤ m`;
* `| |A^{(i)}_k ∩ σ_k(g_a) A^{(j)}_k| / n_k − μ(E_i ∩ g_a E_j) | < 1/m` for `i, j, a ≤ m`.

By Lemmas 2–4, `J_m` is a finite intersection of members of `ω`, so `J_m ∈ ω` and `J_m ≠ ∅`.

*A sofic approximation.* Choose `k_m ∈ J_m` and set `τ_m = σ_{k_m} : Γ → Sym(n_{k_m})`. By construction:

* `|V_m| = n_{k_m} ≥ m`;
* the multiplicativity defects on `{g_1, …, g_m}` are `< 1/m`;
* the freeness defects on `{g_2, …, g_m}` are `< 1/m`.

So `(τ_m)` is a sofic approximation of `Γ` in the sequence sense, and hence along any free ultrafilter.

*Exact statistics in the limit.* Let `P = Γ ↷ (Π_ν V_m, μ_ν)` be its limit action and
`Ê_i = [(A^{(i)}_{k_m})_m]`. For `m ≥ max(i, j, a)` the statistics error at stage `m` is `< 1/m`, so

```text
μ_ν(Ê_i ∩ g_a Ê_j) = lim_m |A^{(i)}_{k_m} ∩ τ_m(g_a) A^{(j)}_{k_m}| / n_{k_m} = μ(E_i ∩ g_a E_j).
```

*Conclusion.*

1. Given data `(A_1, …, A_r, K, ε)` for `a`, choose `E_{i_j}` with `μ(A_j Δ E_{i_j}) < ε/4`, and take
   `B_j = Ê_{i_j}`. The statistics are reproduced to within `ε/2` by (Den). So `a ≺ P`.
2. Stability in finite actions (Definition 3.7) gives `P ≺ F(Γ)`.
3. By (T), `a ≺ F(Γ)`. ∎

**Alternative.** Grant GT Lemma 3.8 (i) ⇒ (ii), whose proof I did not check. Then a finitary proof works
without Loeb spaces:

1. Refine the `A_j` to the atoms of the Boolean algebra they generate, a partition `C_1, …, C_d`.
2. Lift the partition by Lemma 1: take lifts of `C_1, …, C_{d−1}`, assign overlaps to the smallest index, and
   put the rest into the last set. The error vanishes along `ω`.
3. Pick one `k` with `σ_k` `(F, δ)`-sofic and statistics within `ε/2`.
4. Apply (ii).

## 3. Corollary B (nonsoficity and the free upgrade)

**Corollary B.** Let `Γ` be countably infinite and stable in finite actions, and let `a` be a p.m.p. action on
a standard probability space with `a ⊀ F(Γ)`.

1. `a` is not sofic.
2. If `Γ` is residually finite, then `a × (Γ ↷ Γ̂)` is not sofic. Here `Γ̂` is the profinite completion with
   Haar measure and `Γ` acts by left translation. This product is a free p.m.p. action on a standard nonatomic
   probability space. If `Γ` is not finitely generated, read `Γ̂` as the completion
   `lim Γ/N_i` along a decreasing chain of finite-index normal subgroups with `∩ N_i = 1`.

*Proof.* Part 1 is the contrapositive of Proposition A. For part 2:

* If `Γ` is finitely generated, it has countably many finite-index subgroups, so `Γ̂` is compact metrizable.
  (Referee correction, 2026-09-16: a general countable group can have uncountably many finite-index subgroups,
  as `⊕_N Z/2` does.) For general countable residually finite `Γ`, enumerate `Γ ∖ {1}`, choose a finite-index
  normal `N'_γ ∌ γ`, and put `N_i = N'_{γ_1} ∩ … ∩ N'_{γ_i}`. Then `K = lim Γ/N_i` is compact metrizable, and
  the argument below runs with `K` in place of `Γ̂`.
* Residual finiteness makes `Γ → Γ̂` injective, so the translation action is free at every point, and hence so
  is the product action.
* `Γ̂` is infinite, so its Haar measure is nonatomic. An atom would give every point the same positive mass.
* The projection `a × Γ̂ → a` is a factor map, so `a ≺ a × Γ̂` by (Fac).
* If `a × Γ̂ ≺ F(Γ)`, then `a ≺ F(Γ)` by (T), which is false. So `a × Γ̂ ⊀ F(Γ)`, and part 1 applies. ∎

## 4. Input: F2 x F2 has an action not weakly contained in finite actions

This is claim `f2xf2-lacks-kechris-property-md`, imported from the literature.

* **Primary statement.** GT Remark 3.16 (§0.2): "there do exist p.m.p. actions of F2 × F2 that are not
  weakly contained in finite actions", attributed to MIP* = RE. The remark gives no proof.
* **Independent chain (FFW, §0.3).**
  * Remark 5.23: `F_2 × F_2` is not RFD. Ozawa shows that RFD of `C*(F_2 × F_2)` would give Kirchberg's QWEP
    conjecture, equivalently Connes embedding, which MIP* = RE refutes.
  * Definition 5.10: FD implies RFD.
  * Page 68 (Kechris): MD implies FD.
  * So `F_2 × F_2` does not have MD. By GT Remark 3.16 and FFW Remark A.4, MD is exactly "every p.m.p. action
    is `≺ F(Γ)`".

**Mechanism behind MD ⇒ FD (Kechris; recalled, standard, not re-read in a primary source).**

1. **Statistics give Koopman coefficients.** Take `ξ = Σ c_j (1_{A_j} − μ(A_j))`. Then `⟨κ_0(g)ξ, ξ⟩` is a
   fixed polynomial in the statistics `μ(g A_i ∩ A_j)` and `μ(A_j)`. Hence `a ≺ F(Γ)` implies that the Koopman
   representation `κ_0^a` on `L²_0` is weakly contained in the Koopman representations of finite actions, and
   those factor through finite quotients.
2. **Gaussian actions.** For an orthogonal representation `π_R`, the Gaussian action `a_{π_R}` has
   `κ_0 ⊇ π_R ⊗ C` (first chaos).
3. **Conclusion.** Let `ρ` be a unitary representation, realified as `π_R`. Then `π_R ⊗ C ≅ ρ ⊕ ρ̄ ⊇ ρ`. So
   if every action is `≺ F(Γ)`, every `ρ` is weakly contained in finite-image representations; that is FD.

The contrapositive gives an explicit-modulo-`ρ` witness. If `ρ` is a unitary representation of `F_2 × F_2`
not weakly contained in finite-dimensional representations (one exists, since the group is not RFD), then the
Gaussian action of its realification is `⊀ F(Γ)`.

## 5. Theorem C (the dichotomy for F2 x F2)

`Γ = F_2 × F_2` is countably infinite and residually finite: free groups are residually finite, and
`(g, h) ≠ 1` is separated through a finite quotient of one coordinate.

**Theorem C.**

1. If `Γ` is stable in finite actions, then `Γ` has a free p.m.p. action on a standard nonatomic space that is
   not sofic. For instance, take `a_ρ × Γ̂` with `a_ρ` as in §4.
2. If every p.m.p. action of `Γ` is sofic (the target), then `Γ` is not stable in finite actions. This answers
   GT Question 3.12 positively.

*Proof.*

1. By §4 there is `a ⊀ F(Γ)`. Apply Corollary B(2).
2. If `Γ` were also stable in finite actions, Proposition A would give `a ≺ F(Γ)` for every p.m.p. action,
   contradicting §4. `Γ` is residually finite, so this is a residually finite group that is not stable in finite
   actions. ∎

Parts 1 and 2 are the same incompatibility, "stable in finite actions" versus "target", read in the two
directions. Part 1 adds the free upgrade.

**Novelty audit.**

* GT Remark 3.16 already states part 1 informally ("any such action would be non-sofic if F2 × F2 was stable
  in finite actions"), without a proof and without the free upgrade.
* Proposition A is folklore-level. Its content is Lemmas 1–4 plus a diagonal subsequence.
  * Gohla--Thom already use the transfer implicitly. Remark 3.14 reads Elek--Lippner soficity as "weak
    containment in the limit action of a sofic approximation", and Corollary 3.15 draws nonsoficity from
    stability. What is added here is the passage from Păunescu's crossed-product definition to that form.
  * The factor-map step in `sl3z-cocompact-nonsofic-from-stability-and-no-finite-approx` uses the same
    mechanism inline, for microstates.
* Part 2, read as "any proof of the target answers Q3.12 with an explicit group", is a straightforward
  contrapositive; I found it stated nowhere, but it may be implicit in GT Remark 3.16.

No novelty beyond the written proofs is claimed.

## 6. Remarks, each with its verification status

**R1. Converse of Proposition A (sketched here, not landed).** For countably infinite `Γ`: if every
Păunescu-sofic standard action is `≺ F(Γ)`, then `Γ` is stable in finite actions.

*Sketch.*

1. Let `P` be a limit action and `B_1, …, B_r` finitely many Loeb-measurable sets. They generate an invariant
   countably generated σ-algebra. The map `P → ({0,1}^{Γ×r}, pushforward)`, `z ↦ (1_{g^{-1}B_j}(z))_{g,j}`, is
   an equivariant factor onto a standard action `X'`.
2. Every Loeb-measurable set agrees a.e. with an internal set. `1_{[(A_m)]} ↦ [(1_{A_m})]` gives an
   equivariant, trace-preserving embedding of `L^∞(X')` into `Π_ν D_{|V_m|}`. Here `g` acts by
   `Ad [(P_{τ_m(g)})]`.
3. Together with `u_g ↦ [(P_{τ_m(g)})]`, whose trace vanishes for `g ≠ 1`, this extends to the crossed product
   by GNS uniqueness. So `X'` is sofic, and `X' ≺ F` reproduces the statistics of the `B_j`.

For residually finite `Γ`, the folklore converse "`a ≺ F(Γ)` ⇒ `a` sofic" also holds (residual amplification,
as in Alekseev--Thom Lemma 3.2, plus GT Remark 3.14). I did not write it out. It would give: for residually
finite `Γ`, stable in finite actions ⟺ {sofic actions} = {actions `≺ F(Γ)`}.

**R2. All standard sofic actions of F2 x F2 are ≺ F (recalled; no single source checked).**

* **Products** `a_1 × a_2` of `F_2`-actions: `F_2` has MD (FFW Theorem A.5, Kechris), and ≺ passes to products
  (rectangles are dense).
* **Factors** of such products, by (Fac) and (T).
* **Compact translation actions** `Γ → K` dense: factors of products of compact `F_2`-actions, through
  `H_1 × H_2 → K`, `(x, y) ↦ xy`, where `H_i` is the closure of the image of the `i`-th factor.
* **Bernoulli shifts**: Abért--Weiss, as quoted in GT Remark 3.14 (§0.2, checked), puts them `≺ Γ̂ ≺ F`.
* **Pullbacks through amenable quotients**: recalled only.

So no unconditional candidate for `f2xf2-not-stable-in-finite-actions` comes from known sofic actions.
Every finite-dimensional representation of `Γ` is weakly contained in finite-image representations
(tensor decomposition plus FD for `F_2`; recalled). So the non-RFD witnesses of §4 are genuinely
infinite-dimensional. Whether their Gaussian actions are sofic is open. A sofic one would prove
`f2xf2-not-stable-in-finite-actions` by Theorem C.

**R3. Lemma 3.8(iii) and Ioana (checked against §0.5).**

* **Case m = 1.** Condition (iii) with `m = 1` gives one-to-one `θ = π^{-1} : [n] → X`. For `x = θ(y)`,
  `π(ψ(g)x) ≠ ϕ(g)π(x)` holds exactly when `ψ(g)θ(y) ≠ θ(ϕ(g)y)`. So the case `m = 1` is the correction
  forbidden in (⋆) of [Io19b, Theorem D], with `|Y_n| ≤ (1+ε)|X_n|`. It fails for `F_m × F_k`, `m, k ≥ 2`.
* **General m.** Here the honest action covers the sofic approximation. Ioana's Theorem 1.5 is about the
  sofic approximation covering honest actions, the reverse direction, so it does not decide (iii).
* **The target question.** Condition (i) is statistics-only, and every obstruction in §0.5 is Hamming-level.
  None transfers.

**R4. Ioana's sofic approximations as test limit actions (undecided).**

* The approximations `σ̃_p` of arXiv:2008.00554v2 §4 are built for `F_m × F_k` with `m ≥ 5`, `k ≥ 3`, using
  `F_m = F_{m−1} ∗ Z`. The case `F_2 × F_2` is reached through finite-index subgroups (his Lemma 4.1). They
  extend `σ_p(g,h)x = ϕ_p(g) x ρ_p(h)^{-1}` for `g ∈ F_{m−1}` and `h ∈ F_k`. There `F_{m−1}` has property (τ)
  with respect to `ker ϕ_p`, and `F_k` does not with respect to `ker ρ_p`.
* For the asymptotic homomorphisms `σ_p`, the restriction to `F_{m−1} × F_k` is an honest finite action on
  `G_p`. I did not check how much of this survives the augmentation to `σ̃_p` or the induction to
  `F_2 × F_2` (referee caveat).
* Whether the full limit action is `≺ F` is the natural concrete test of `f2xf2-is-stable-in-finite-actions`.
  I found no argument either way.

**R5. The GT Theorem 3.13 engine does nothing for F2 x F2 (recalled, unverified).**

* Hypothesis (iii) of GT Theorem 3.13 needs a non-residually-finite central extension by a finite abelian group.
* `F_2 × F_2` should be good in the sense of Serre: free groups are good, and extensions of good groups by
  finitely generated good normal subgroups of type FP∞ are good.
* By Grunewald--Jaikin-Zapirain--Zalesskii (Duke 2008), extensions of good residually finite groups by finite
  groups are residually finite. I did not re-read the source.
* So the Remark 3.14 witness `{0,1}^{Γ̃/A}` does not exist for `F_2 × F_2`.

**R6. Inheritance theorems (checked against §0.2).**

* **Theorem 3.9** needs `H` amenable. In the obvious splitting `F_2 × F_2 = F_2 ⋊ F_2` the complement is
  `F_2`. Any splitting `Λ ⋊ H` with `H` amenable has `Λ` normal with amenable quotient, so the next bullet
  applies to `Λ`.
* **Theorem 3.11** needs `Γ/Λ` amenable. Any such normal `Λ ≤ F_2 × F_2` contains `N_1 × N_2` with
  `N_i = Λ ∩ F_2^{(i)}`. Each `F_2/N_i` embeds in `Γ/Λ`, so it is amenable and `N_i ≠ 1`. If `N_i` has
  infinite index it is free of infinite rank. So the reduction lands on a group that again contains a product
  of two nonabelian free groups, and stability of `Λ` is no easier to establish.
* **Amalgam.** No amalgamation theorem for stability in finite actions appears in GT, AT or FFW, so the
  splitting `(F_2 × Z) *_{F_2} (F_2 × Z)` gives nothing.
