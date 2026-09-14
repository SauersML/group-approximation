---
rg: 2
id: fp-simple-models-concentrate-on-template-constituents
kind: claim
title: Every finite-group hyperlinear model of a finitely presented infinite simple group puts definite weight on large irreducible constituents where some relator is non-scalar and all relators are nearly scalar
distinct_from:
  fp-simple-groups-have-no-gapped-finite-unitary-models: that assumes a character-ratio gap at every noncentral element of the target groups and concludes nonexistence; this assumes nothing about the targets and locates the constituents that must fail a gap (per constituent, at relator images, in large dimension), which is the form that passes to direct products
  gap-sofic-approximations-are-local-embeddings: that is the fixed-point-gap theorem for sofic approximations of any countable group; this is the constituent-level template for unitary models of finitely presented infinite simple groups, with a template on orbits as its permutation case
  simple-group-relator-templates-over-finite-simple-groups: that fixes relator-conjugate word templates for weak models under non-linear-soficity; this is a trace-metric statement about where hyperlinear models concentrate, with no soficity hypothesis
---

**ESTABLISHED (lane sk-trace-template, 2026-09-13, unreviewed).** Proof: `fp-simple-models-concentrate-on-template-constituents-proof`.

**Setting.** `S = ⟨X | R⟩` is finitely presented, infinite and simple, and `c = [x,y] ≠ e` for some `x,y ∈ X`. A *finite-group
hyperlinear model* of `S` consists of:
- finite groups `Q_k`, arbitrary maps `φ_k : X → Q_k`, unitary representations `ρ_k : Q_k → U(d_k)`;
- a nonprincipal ultrafilter `ω` such that `x ↦ (ρ_k(φ_k(x)))_ω` extends to an injective homomorphism
  `Π : S → ∏_ω (U(d_k), ‖·‖_2)`, where `‖·‖_2` is the normalized Hilbert–Schmidt norm.

Sofic models through finite permutation groups are the case where `ρ_k` is a permutation representation. For a word `w` in `X`,
`W_k(w) ∈ Q_k` is its evaluation at `φ_k`.
- Decompose `ρ_k = ⊕_σ m_σ σ` into irreducible representations `σ` of `Q_k`, with weights `p_σ = m_σ dim σ / d_k`.
- Write `χ̃_σ = χ_σ/χ_σ(1)`.
- Put `η = lim_ω ‖ρ_k(W_k(c)) − I‖_2`. It is positive by injectivity.

**Template constituents.** For `θ < 1` and `D ≥ 1`, `T_k(θ,D)` is the set of irreducible constituents `σ` of `ρ_k` with:
- `dim σ > D`;
- `|χ̃_σ(W_k(r))| > θ` for every `r ∈ R`, so each relator acts in `σ` within normalized distance `√(2−2θ)` of a scalar;
- `σ(W_k(r))` is not a scalar for at least one `r ∈ R`.

**Theorem.** For every `θ < 1` and `D ≥ 1`,
```text
lim_ω Σ_{σ ∈ T_k(θ,D)} p_σ ≥ η²/4 .
```

**Corollary 1 (one constituent).** There are irreducible representations `σ_k` of `Q_k` such that, along `ω`:
- `dim σ_k → ∞`, some relator is non-scalar in `σ_k`, and `max_r (1 − |χ̃_{σ_k}(W_k(r))|) → 0`;
- `x ↦ (σ_k(φ_k(x)))_ω` induces an injective homomorphism `S → ∏_ω (PU(dim σ_k), d_proj)`, where
  `d_proj(A,B) = min_{|λ|=1} ‖A − λB‖_2`;
- so the representations `σ_k ⊗ σ̄_k` of `Q_k` give a hyperlinear model of `S` through one irreducible representation tensored
  with its dual.

**Corollary 2 (constituent gaps).** Call an irreducible representation `σ` of a finite group *θ-gapped* if `|χ̃_σ(q)| ≤ θ`
whenever `σ(q)` is not a scalar. Suppose that for some `θ < 1` and `D`, every irreducible constituent of dimension `> D` of
every `ρ_k` is θ-gapped. Then `S` has no such model.
- This contains `fp-simple-groups-have-no-gapped-finite-unitary-models`. In a groupwise θ-gapped group, `σ(q)` non-scalar
  forces `σ` nontrivial and `q` noncentral (Schur), so every irreducible representation is θ-gapped.
- The per-constituent gap is what passes to direct products: `constituent-gapped-finite-groups-closed-under-products`.

**Permutation template.** Let `σ_k : X → Sym(Ω_k)` be a sofic model, with `Q_k = ⟨σ_k(X)⟩` and
`η = lim_ω d(σ_k(W_k(c)), 1) > 0` in the normalized Hamming metric. Call an orbit of `Q_k` a *template orbit* if:
- some relator acts nontrivially on it; and
- every relator moves fewer than a `(1−θ)`-fraction of its points.

Then the template orbits have total weight at least `η` along `ω`, and each has more than `2/(1−θ)` points.

**Model tests.**
- `G_X = EL_3(LC(X,F_2)⋊Z)` is simple but not finitely presented. Its models `SL_{3N}(F_2)` on vectors are gapped, and
  the theorem does not apply.
- `SL_3(Z)` is finitely presented but not simple. Its congruence models on `F_p^3` are gapped, and Step (i) of the proof fails.
- For abelian targets every irreducible constituent is one-dimensional, so `T_k` is empty. The theorem then says that a
  nonabelian `S` has no models through abelian groups, which is true.
- Alternating groups carry template constituents. In the standard representation of `A_m`, a 3-cycle has ratio
  `(m−4)/(m−1) → 1`. Sofic permutation models live there.

**Credit and novelty.** The ingredients are standard:
- the Markov bound on relator defects;
- Schur's lemma;
- Mal'cev's theorem that finitely generated linear groups are residually finite;
- the adjoint representation `A ↦ A ⊗ Ā`.

What is new here is the per-constituent formulation and the single-constituent projective corollary. The novelty check was
bounded to a grep of this graph for "template", "constituent", "Mal'cev" and the related gap nodes.
