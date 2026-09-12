# Quasitraces on Kazhdan block algebras: the corona and its trace-kernel ideal (2026-09-12)

Lane `quasitrace-nonexact-block-algebra`, swarm 5. The task was the negative side
of STW Problem I (`stw99-problem-i-quasitraces-are-traces`): build a non-additive
bounded 2-quasitrace on a non-exact block algebra `B ⊂ ∏_k M_{n_k}` coming from a
Kazhdan group, or prove that every bounded 2-quasitrace on such `B` is a trace.

**Outcome.** Neither side is settled. For Ozawa's block algebra of `SL(3,Z)`, the
question is reduced to one statement about one ideal:

> every bounded 2-quasitrace on `B` is a trace **iff** every bounded 2-quasitrace
> on the corona `A = B/⊕_k M_{n_k}` vanishes on the ideal `K` of block-trace-thin
> elements.

- `A` has exactly one tracial state `τ_0`, and `A/K ≅ C*_r(SL(3,Z))`.
- `K` is a nonzero ideal on which every trace of `A` vanishes.
- So a bounded 2-quasitrace on `A` that charges `K` is automatically not a trace,
  and refutes Problem I.
- Conversely, if bounded quasitraces cannot see `K`, then `B` is a new non-exact
  algebra with only tracial quasitraces.
- `K` is invisible to quasitraces if it is exact, or if its positive elements are
  infinitesimal in the Cuntz semigroup of `A`. Neither is known.

Conventions follow `research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md`.
"Quasitrace" means bounded 2-quasitrace. `QL(A)` means that every bounded
2-quasitrace on `A` is a trace.

## 0. Inputs

**From Cairn** (established on main):
- `kazhdan-fd-block-representation-algebras-are-not-exact`: `B` is not exact.
- `stw01-extensions-preserve-qt-linearity`: `QL(I)` and `QL(A/I)` give `QL(A)`.
- The axioms and elementary facts used in the stw01 region:
  - bounded 2-quasitraces are monotone on `A_+`;
  - they are additive on commuting positive elements;
  - they satisfy `|σ(a) − σ(b)| ≤ ‖a − b‖ σ(1)` for self-adjoint `a, b` in unital `A`;
  - the square-null set `N_σ = {x : σ(x*x) = 0}` is a closed two-sided ideal, and `σ`
    factors through `A/N_σ`.

  See `research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md`.
- Haagerup: quasitraces on unital exact C*-algebras are traces. It is imported on
  main in `blackadar-rordam-haagerup-k0-states-are-traces-citation`.
- `SL(3,Z)` has property A, so `C*_r(SL(3,Z))` is exact: [GHW04] via Willett §2.3,
  as used in `stw01-kun-thom-reduced-group-algebras-are-qt-linear`.

**External** (source status in §6):
- **Bekka's operator-algebraic superrigidity** (Invent. Math. 169 (2007)). For
  `Γ = SL(n,Z)`, `n ≥ 3`, every unitary representation `π` with `π(Γ)''` a finite
  factor is either finite-dimensional or extends to an isomorphism
  `L(Γ) ≅ π(Γ)''`.
- **Hulanicki–Reiter:** `1_H ≺ λ_H` iff `H` is amenable.
- **Dimension functions** (Blackadar–Handelman, as recalled in Milhøj–Rørdam §2,
  arXiv:2309.17412). For a bounded 2-quasitrace `σ` on unital `A`,
  `d_σ(x) = lim_n σ(x^{1/n})` on `M_∞(A)_+` is additive on orthogonal sums and
  monotone for Cuntz subequivalence.

## 1. The block ideal lies inside a Kazhdan block algebra

**Lemma 1.1 (Fell isolation).** Let `G` have property (T), and let `σ` be a
finite-dimensional irreducible unitary representation. If `σ ≺ π`, then `σ ⊂ π`.
Hence `σ` is an isolated point of `Ĝ`.

*Proof.*
1. `σ ≺ π` gives `σ ⊗ σ̄ ≺ π ⊗ σ̄`.
2. `σ ⊗ σ̄ ≅ HS(H_σ)` has the invariant vector `1`, so `π ⊗ σ̄` almost has
   invariant vectors.
3. By property (T) it therefore has a nonzero invariant vector.
4. `π ⊗ σ̄ ≅ HS(H_σ, H_π)` with `g·T = π(g) T σ(g)*`. So an invariant vector is a
   nonzero intertwiner `T : H_σ → H_π`.
5. `T*T` commutes with `σ`, so it is a nonzero scalar and `T` is a multiple of an
   isometric intertwiner. So `σ ⊂ π`.

For isolation, suppose `σ` lies in the closure of `Ĝ ∖ {σ}`. Then
`σ ≺ ⊕_{π ∈ Ĝ∖{σ}} π`, so `σ` embeds in that sum. Some coordinate projection of
the embedding is a nonzero intertwiner into an irreducible `π ≇ σ`, which is
impossible. ∎

**Lemma 1.2 (block ideal).** Setting:
- `G` has property (T);
- `σ_j` (`j ∈ N`) are pairwise inequivalent finite-dimensional irreducible unitary
  representations, with `n_j = dim σ_j`;
- `ρ = ⊕_j σ_j`, `B = C*_ρ(G) ⊂ ∏_j M_{n_j}`, and `I = ⊕_j M_{n_j}` (norm-null
  sequences).

Then `I ⊂ B`, and `B/I` has no finite-dimensional irreducible representation.

*Proof.* The spectrum `B̂` is the closed set of `π ∈ Ĝ` with `π ≺ ρ`, carrying the
relative topology. By Lemma 1.1 each `σ_j` is an open point of `B̂`.
- **Block ideals.** The open point `{σ_j}` corresponds to an ideal `J_j ⊂ B` with
  `Ĵ_j = {σ_j}`. So `J_j` is primitive, with faithful irreducible representation
  `σ_j|_{J_j}` into `M_{n_j}`, and `J_j ≅ M_{n_j}`.
- **Other coordinates vanish.** For `i ≠ j`, `σ_i(J_j)` is an ideal of
  `σ_i(B) = M_{n_i}`. If it were nonzero, `σ_i|_{J_j}` would be irreducible,
  hence equivalent to `σ_j|_{J_j}`, and the unique extension to `B` would force
  `σ_i ≅ σ_j`.
- **Conclusion.** `J_j` is the full block `M_{n_j}` in coordinate `j`, so `I ⊂ B`.

A finite-dimensional irreducible representation `τ` of `B/I` is one of `B` with
`τ ≺ ρ`. By Lemma 1.1, `τ ⊂ ρ`, so `τ ≅ σ_j` for some `j`. But `σ_j` does not
vanish on `J_j ⊂ I`, while `τ` does. ∎

**Corollary 1.3.** `QL(B) ⟺ QL(B/I)`.

*Proof.*
- **Quasitraces on `I` are traces.** Let `σ` be a bounded 2-quasitrace on `I`. Put
  `P_m = ⊕_{j ≤ m} 1_{n_j} ∈ I`, which is central in `∏ M_{n_j}`.
  - For `a ∈ I_+`, the elements `aP_m` and `a(1 − P_m)` lie in `I`, are positive and
    orthogonal. So `σ(a) = σ(aP_m) + σ(a(1 − P_m))`.
  - `‖a(1 − P_m)‖ → 0`, so boundedness gives `σ(a) = lim_m σ(aP_m)`.
  - `σ` restricted to the finite-dimensional unital corner `P_m I P_m` is a trace.
  - So `σ(a + b) = σ(a) + σ(b)` on `I_+`, and `σ` is a trace.
- **`⟸`** is `stw01-extensions-preserve-qt-linearity`.
- **`⟹`** holds because quasitraces on quotients pull back. ∎

## 2. Ozawa's `SL(3,Z)` blocks: the corona has one trace and a nonzero kernel

**Setting.**
- `Γ = SL(3,Z)`, and `p_k → ∞` are distinct primes.
- `X_k = P²(F_{p_k})` has `N_k = p_k² + p_k + 1` points.
- `σ_k` is the permutation representation on `ℓ²(X_k) ⊖ C1`. It is irreducible,
  of dimension `p_k² + p_k`, and the `σ_k` are pairwise inequivalent (main,
  `kazhdan-fd-block-representation-algebras-are-not-exact`).
- `B`, `I` are as in Lemma 1.2. Put `A = B/I`, with `q : B → A` and
  `ρ_∞ = q ∘ ρ`.

**Lemma 2.1 (trace asymptotics).** For `e ≠ g ∈ Γ`, `tr(σ_k(g)) → 0`.

*Proof.*
- **Formula.** `tr(σ_k(g)) = (Fix_{p_k}(g) − 1)/(N_k − 1)`.
- **Non-scalar `g` has few fixed points.** If `g mod p` is not scalar, each
  eigenspace has dimension at most 2 and eigenspaces are independent, so the
  projective fixed set has at most `p + 2` points.
- **`g mod p` is scalar only for finitely many `p`.**
  - If it were scalar for infinitely many `p`, every off-diagonal entry of `g`,
    and every difference of diagonal entries, would be divisible by infinitely
    many primes.
  - Then `g = dI` with `d³ = 1` and `d ∈ Z`, so `g = e`.

So `|tr(σ_k(g))| ≤ (p_k + 1)/(p_k² + p_k)` for large `k`. ∎

**Consequently** `τ_0(q(x)) := lim_k tr_{n_k}(x_k)` exists for `x ∈ B`.
- **Existence.** It exists on the dense subalgebra `ρ(C[Γ])`, and the maps
  `x ↦ tr(x_k)` are contractive.
- **Well defined on `A`.** It vanishes on `I`, since `‖x_k‖ → 0` there.
- **Properties.** It is a tracial state of `A` with `τ_0 ∘ ρ_∞ = δ_e`.
- **GNS.** Its GNS representation restricted to `Γ` is `λ_Γ`. So `λ ≺ ρ_∞`, and
  `π_{τ_0}(A) = C*_r(Γ)`.
- **Kernel.** Put `K := N_{τ_0} = ker(A → C*_r(Γ))`.

**Lemma 2.2 (unique trace).** `τ_0` is the only tracial state of `A`.

*Proof.* `T(A)` is the set of traces of `C*(Γ)` vanishing on
`J = ker(C*(Γ) → A)`. It is a closed face of `T(C*(Γ))`, since a convex
combination of traces vanishes on `J_+` only if both terms do. By Krein–Milman
it suffices to show that every extreme point `τ` of `T(A)` equals `τ_0`. Such a
`τ` is an extremal trace of `C*(Γ)`, so `π_τ(Γ)''` is a finite factor, and `π_τ`
vanishes on `J`. By Bekka, one of two cases holds.
- **`π_τ` is finite-dimensional.** Then it is a multiple of an irreducible
  finite-dimensional representation of `A`, which Lemma 1.2 excludes.
- **`π_τ` extends to `L(Γ) ≅ π_τ(Γ)''`.** Then `τ = δ_e = τ_0`. ∎

**Lemma 2.3 (`K ≠ 0`).**
- Let `P = Stab_Γ([1:0:0])`, the matrices with first column `(±1, 0, 0)ᵀ`. It
  contains a copy of `SL(2,Z)`, so it is not amenable.
- Then `λ_{Γ/P} ≺ ρ_∞`. In particular `A ≠ C*_r(Γ)`, so `K ≠ 0`.

*Proof.*
1. **The vectors.** Put `x_0 = [1:0:0]` and
   `ξ_k = (δ_{x_0} − N_k^{-1} 1)/(1 − N_k^{-1})^{1/2} ∈ ℓ²(X_k) ⊖ C1`.
2. **Their coefficients.**
   `⟨σ_k(g) ξ_k, ξ_k⟩ = (1_{g x_0 = x_0 mod p_k} − N_k^{-1})/(1 − N_k^{-1})`.
3. **Pointwise limit.** For fixed `g`, `g x_0 ≡ x_0 mod p` iff
   `p | g_21` and `p | g_31`. For large `p` this holds iff `g ∈ P`. So the
   coefficients converge pointwise to `1_P`.
4. **A state of `A`.** A weak* limit `ω` of the vector states `x ↦ ⟨x_k ξ_k, ξ_k⟩`
   on `B` vanishes on `I`. So `ω` is a state of `A` with `ω ∘ ρ_∞ = 1_P`. Its GNS
   representation is `λ_{Γ/P}`, so `λ_{Γ/P} ≺ ρ_∞`.
5. **`K ≠ 0`.** Suppose `K = 0`. Then `λ_{Γ/P} ≺ λ_Γ`.
   - Restricting to `P` gives `λ_{Γ/P}|_P ≺ λ_Γ|_P ≅ ∞·λ_P`.
   - `λ_{Γ/P}|_P` contains `1_P`, via `δ_P`.
   - So `1_P ≺ λ_P`, and `P` would be amenable (Hulanicki–Reiter). ∎

**Lemma 2.4 (bounded traces on ideals extend).** Let `J ⊂ A` be an ideal and `τ`
a bounded positive trace on `J`. Then `τ` extends to a trace `φ` on `A`.

*Proof.*
1. **Extension.** A norm-preserving positive extension `φ` exists. With `(e_λ)` an
   approximate unit of `J`, `φ(1) = ‖φ‖ = lim τ(e_λ)`, so `φ(1 − e_λ) → 0`.
2. **Approximation.** By Cauchy–Schwarz, `φ(z) = lim φ(e_λ z e_λ)`.
3. **One inequality.** For `y ∈ A`,
   `φ(y*y) = lim τ((y e_λ)*(y e_λ)) = lim τ(y e_λ² y*) ≤ φ(yy*)`.
4. **Trace.** By symmetry the two sides are equal. ∎

So `K` carries no nonzero bounded trace: its extension would be a multiple of
`τ_0`, which vanishes on `K`.

## 3. The dichotomy

**Theorem 3.1.** Let `B ⊂ ∏ M_{n_k}` be unital with `I ⊂ B`, and put `A = B/I`.
Suppose `A` has a unique tracial state `τ_0`, and `A/N_{τ_0}` is exact. Put
`K = N_{τ_0}`. Then

    QL(B)  ⟺  every bounded 2-quasitrace on A vanishes on K.

A bounded 2-quasitrace on `A` that charges `K` is not a trace, so it refutes Problem I.

*Proof.* By Corollary 1.3 it suffices to treat `QL(A)`.
- **`⟸`.** Let `σ` be a quasitrace on `A` with `σ(K) = 0`.
  - For `x ∈ K`, `x*x ∈ K`, so `K ⊂ N_σ`.
  - `σ` factors through `A/N_σ`, which is a quotient of the exact algebra `A/K`,
    hence exact.
  - By Haagerup the descended quasitrace is a trace, so `σ` is one.
- **`⟹`.** Suppose `σ(a) ≠ 0` for some `a ∈ K_+`. If `σ` were a trace, it would
  equal `σ(1) τ_0`. But `τ_0(a) = 0`. So `QL(A)` fails. ∎

**Corollary 3.2.** For Ozawa's blocks, `QL(B)` holds iff every bounded
2-quasitrace on `A` vanishes on `K = ker(A → C*_r(SL(3,Z)))`. This `K` is
nonzero and has no bounded trace. The hypotheses hold by Lemmas 2.1–2.3 and the
exactness of `SL(3,Z)`.

## 4. Two sufficient criteria for invisibility of `K`

**Proposition 4.1 (infinitesimal elements).** Let `a ∈ A_+` satisfy
`m·[(a − ε)_+] ≤ [1_A]` in `W(A)` for all `m ∈ N` and `ε > 0`. Then `σ(a) = 0`
for every bounded 2-quasitrace `σ`.

*Proof.*
1. `m d_σ((a − ε)_+) ≤ d_σ(1) = σ(1)` for all `m`, so `d_σ((a − ε)_+) = 0`.
2. For `0 ≤ x ≤ 1`, `x ≤ x^{1/n}`, so `σ(x) ≤ d_σ(x)`. Hence
   `σ((a − ε)_+) = 0` after scaling.
3. By the continuity estimate, `σ(a) = lim_{ε → 0} σ((a − ε)_+) = 0`. ∎

**Proposition 4.2 (exact kernel).** In Theorem 3.1, if `K` is exact, then every
bounded 2-quasitrace on `A` vanishes on `K`, and `QL(B)` holds.

*Proof.*
1. `σ` restricted to the unital exact subalgebra `C*(K, 1) ⊂ A` is a trace
   (Haagerup).
2. So `σ|_K` is a bounded positive trace on `K`.
3. By Lemma 2.4 it extends to a trace on `A`, equal to `c τ_0`, which vanishes on
   `K`. ∎

## 5. Where the attacks stop

1. **Charging `K` with a dimension function.** A quasitrace charging `K` needs
   some `a ∈ K_+` that is not infinitesimal in `W(A)` (Prop. 4.1).
   - That is a failure of comparison inside `A` for trace-thin elements.
   - In the ambient corona `∏M/⊕M` those elements are infinitesimal, using
     partial isometries outside `A`.
   - No mechanism was found that produces a lower semicontinuous state on `W(A)`
     charging `K`.
2. **Traceless unital corners.** The Milhøj–Rørdam route (a unital, stably
   finite, traceless algebra carries a non-trace quasitrace) is unavailable
   inside `A`.
   - Every unital C*-subalgebra of a corner `pQp` of `Q = ∏M/⊕M` has a trace,
     namely a limit of normalized rank traces on the corner.
   - So a counterexample on `A` must charge a non-unital part of `K`.
3. **Exactness of `K`** (Prop. 4.2). Open. No ambient exactness is available.
   - `B` lies in the uniform Roe algebra of `⊔_k X_k`, since the `ρ(g)` are
     permutation matrices of propagation `≤ |g|`.
   - The `X_k` form an expander family, by property (T).
   - A coarse union of expanders has no property A, and its uniform Roe algebra is
     not exact. This import was not re-read here.
   - Whether `A` itself is exact is also open. Non-exactness of `B` does not
     decide it, because the extension by the nuclear ideal `I` need not be locally
     split.
   - **The non-exactness certificate does not descend to `A`.** Take any faithful
     representation `π` of `A` and put `x = Σ_{s∈E} ρ_∞(s) ⊗ ρ̄(s)`. The
     `|E|`-eigenspace of `x` consists of intertwiners from some `σ_j` into
     `π ∘ ρ_∞`.
     - A nonzero one would make `σ_j` a finite-dimensional representation of `A`,
       which Lemma 1.2 excludes.
     - So `spec(x) ⊂ [−|E|, |E| − κ²/2]`, and the Kazhdan projection is zero in
       `A ⊗_min ∏ B(H̄_j)`.

     All of `B`'s known non-exactness may therefore sit in the extension by `I`.
     If `A` is exact, `K` is exact, and Prop. 4.2 gives `QL(B)`.
4. **Displacement.** Elements of `K` concentrated near finitely many low-height
   points or lines of `P²(Q)` admit, for every `m`, approximately orthogonal
   `Γ`-translates in `A`. So they are infinitesimal and invisible (Prop. 4.1).
   - This stops at generation: nothing shows `K` is generated as an ideal by such
     elements.
   - Expander geometry allows non-local ghost-type elements whose norms are not
     seen by local limits.
5. **Domination by traces** (Brown–Winter Lemma 3). A quasitrace charging `K` is
   dominated by no trace, so domination gives no leverage in either direction.
6. **The non-exactness certificate** of main lives in `B ⊗_min ∏ B(H̄_j)`, and
   says nothing about quasitraces. After Theorem 3.1, the only place a
   non-linear quasitrace on `B` can live is `K`.

## 6. Source status

- Bekka (Invent. Math. 169 (2007)) and Milhøj–Rørdam arXiv:2309.17412: the
  verification from PDF on MSI is recorded in the next section once complete.
- Hulanicki–Reiter, [GHW04] and Haagerup: standard; not re-read here.
- Novelty: none claimed for Lemma 1.1 (Wang 1975, Bekka–de la Harpe–Valette), for
  Lemma 2.4, or for Proposition 4.1. The assembly into Theorem 3.1 and
  Corollary 3.2 was not found in the sources read, but the search was not
  exhaustive.
