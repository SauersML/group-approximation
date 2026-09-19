# Panin's geometric presentation in the K₂ program: what LSV consume, and an elementary replacement for polynomial rings

Lane k2-panin, 2026-09-19. This is a lane proof and has not been reviewed.
Lean: `GroupApproximation/BooneHigmanLinear/PaninAffine/Statements.lean`, not yet built.
Board: `k2-poly.md`, piece GEO.

## 1. What LSV consume

Lavrenov–Sinchuk–Voronetsky (arXiv:2110.11087) use Panin's theorem once, in their Cor 2.9. It is
their Thm 2.8, taken from Panin, arXiv:1707.01756, Thm 1.2/2.5.

**Their Thm 2.8.** Setting:
- k is a field, R a domain smooth over k, and A = R_{M₁..M_n} a semilocalization;
- f ∈ ∩ Mᵢ.

Conclusion: there exist a monic h ∈ A[t], a domain S essentially smooth over k, and maps
τ: A[t] → S, p: R → S, δ: S → A and p': R_f → S_{τ(h)} such that:
- τ is étale and injective, and A[t]/h ≅ S/τ(h);
- δ∘τ = ev₀ and δ∘p = λ_M, the localization R → A;
- the localizations commute.

**How Cor 2.9 uses it.** Take g₁ ∈ K(R'), R' = R_{f'}, that dies in K(R'_f).
- (A3), Nisnevich excision for A[t] ⊂ S at h, gives g₂ ∈ Ker(K(A[t]) → K(A[t]_h)) with K(τ)g₂ = K(p)g₁.
- Lemma 2.7, monic injectivity, gives g₂ = 1.
- So g = K(δ)K(p)g₁ = ev₀(g₂) = 1.

**Why Panin in general is out of reach.**
- Panin's proof builds nice triples from Artin elementary fibrations and étale neighbourhoods.
- Over a finite field it adds Poonen's Bertini theorem ([Pan1] Prop 2.6, Def 2.7 conditions 1*/2*,
  Lemma 3.3).
- Mathlib has none of this.

## 2. Reduction A: finite field to infinite field (Lean, proved modulo named inputs)

`unstableNKAt_of_ratFunc`: let F be a field and B = F[s₁..s_k]. Then UnstableNK(B) follows from three inputs:
- UnstableNK(F(T)[s₁..s_k]);
- `RatFuncFinitaryAt`, a consequence of F.5;
- `HorrocksMonicAt(B[X])`, which is H.b with finite residue fields.

*Proof.* Let u ∈ K₂(r, B[X]) with u(0) = 1.
- Its image over F(T) is killed by X ↦ 0, so by UnstableNK over F(T) it is 1.
- F(T)[s][X] is the colimit of F[T]_g[s][X], so u already dies wherever some monic g ∈ F[T] is a unit.
- g stays monic in B[X][T], so Horrocks kills the constant image C(u) ∈ St_r(B[X][T]).
- Applying T ↦ 0 gives u = 1.

`unstableNKPolyFp_of_ratFunc` assembles this for all p. **Consequence: LSV need only be run over the
infinite field F_p(T).** Panin's finite-field machinery (Poonen's Bertini, conditions 1*/2*) is
not needed at all.

## 3. Reduction B: over an infinite field, a linear presentation replaces Panin and Nisnevich excision

Statement (`AffineMonicFibreStatement K`, K infinite). Let R = K[s₀..s_n], let M be maximal with
f ∈ M, f ≠ 0, and let f' ∉ M with gcd(f, f') = 1. Then a linear automorphism φ satisfies:
- (i) φf = c·(monic in s₀ over K[s₁..s_n]) with c ∈ K^×;
- (ii) (φf, φf') + 𝔭R = R, where 𝔭 = φ(M) ∩ K[s₁..s_n] (`FibreCoprime`).

**Proof of the statement (paper).**
- Let κ = R/M, and let x ∈ κ^{n+1} be the point.
- Put f̃(s) = f(x+s) and f̃'(s) = f'(x+s) in κ[s]. Then f̃(0) = 0 and f̃'(0) = f'(x) ≠ 0.
- **Step 1: the resultant of f and f' along lines through x is not identically zero.**
  - The substitution s = λ·v is an isomorphism κ[s][λ^{±1}] ≅ κ[v][λ^{±1}], sending s_i to λ v_i.
  - f̃ and f̃' are coprime in κ[s], because gcd is stable under field extension. So they stay
    coprime after inverting λ, and their images ψf̃, ψf̃' are coprime in κ[v][λ^{±1}].
  - Hence any common factor in κ[v][λ] is a power of λ. That is impossible, since ψf̃'(λ = 0) = f'(x) ≠ 0.
  - By Gauss's lemma, ψf̃ and ψf̃' are coprime in κ(v)[λ]. This gives a·ψf̃ + b·ψf̃' = D(v) with a, b ∈ κ[v][λ] and 0 ≠ D ∈ κ[v].
- **Step 2: choosing the direction.**
  - Write D = Σ eⱼDⱼ over a K-basis (eⱼ) of κ, and pick one Dⱼ ≠ 0.
  - K is infinite, so some v₀ ∈ K^{n+1} has Dⱼ(v₀)·f_top(v₀) ≠ 0. Then D(v₀) ≠ 0.
  - Let φ be the linear map with φ⁻¹(e₀) = v₀.
  - (i) holds: the s₀-leading coefficient of φf is f_top(v₀).
- **Step 3: the fibre condition.**
  - The s₀-line over π(x) is x + λv₀. Along it, f and f' satisfy a(v₀)f + b(v₀)f' = D(v₀) ∈ κ^×, so they are coprime in κ[λ].
  - Coprimality descends to κ₀[s₀], where κ₀ = K[s₁..s_n]/𝔭 ⊂ κ.
  - Lifting the Bézout identity gives (ii).

**Consumption, with no Panin and no Nisnevich excision.** In Cor 2.9 take R = K[s], a single maximal M,
and g₁ ∈ K(R_{f'}) dying at f. First move the factors of f outside M into f', so that
gcd(f, f') = 1. Apply the statement, then set:
- A = R_M, and p: R_{f'} → S := A[t]_{p(f')} with p(sᵢ) = sᵢ for i ≥ 1 and p(s₀) = s₀ + t;
- h = p(f), monic in t over A;
- δ = ev₀ on S, and τ the localization A[t] → A[t]_{p(f')}.

Then:
- (ii) gives (h, p(f')) + M_A[t] = A[t]. Since A[t]/h is finite over the local ring A, Nakayama
  gives (h, p(f')) = A[t].
- Therefore Zariski excision (LSV Lemma 2.6, for the coprime pair (p(f'), h) in the domain
  A[x][t]) replaces (A3).
- Lemma 2.6 follows from Tulenbaev's patching F.4. Given y ∈ K(R_a) with y ↦ 1 in K(R_ab), the
  compatible pair (y, 1) comes from z ∈ St_r(R), and z ∈ K₂ because R → R_a × R_b is injective.
- The rest of Cor 2.9 and Thm 2.2 go through unchanged: m = 0, 1, then LG (Lemma 2.4) and (A5) at
  E = Frac(R). R = K[s] is smooth of finite type, so Popescu is not needed.

## 4. Effect on the k2-poly tree

P1 now needs, over K = F_p(T):
- A1 = F.5;
- A2/LG (sk-k2-loc);
- A4, P¹-glueing for local domains with INFINITE residue fields (pal-q111; FR does not suffice
  here, and it did not suffice on the F_p route either, because maximal ideals of A[x] can have
  infinite residue fields);
- A5 for all fields (bh-pal-wire);
- F.4, Zariski patching;
- GEO-AFF (this lane);
- plus `RatFuncFinitaryAt` (from F.5) and H.b over F_p[s][X] for the descent.

**Not needed:**
- A3 / EXC (LSV §4 pro-groups): fix-bh-a can drop EXC and keep STAB as the fallback.
- Panin (GEO in general).
- Popescu.
- MK.

## 5. Lean status (updated 2026-09-19 ~12:10)

`AffineMonicFibreStatement` is restated in consumer form. The fibre condition reads
`IsCoprime` in `(R/M)[s₀]` after mapping coefficients along `fibreMap M φ : K[s₁..sₙ] → R/M`. Its
kernel is `𝔭 = φ(M) ∩ C`, so there is no need to prove that `𝔭` is maximal. `isCoprime_map`
then descends the condition to `k(𝔭)`, and Nakayama lifts it to `C_𝔭[s₀]` (the consumer's step).

The full Lean proof of GEO-AFF is written but not yet built:
`PaninAffine/{Algebra,Line,Main}.lean` gives `infiniteFieldAffineMonicFibre :
InfiniteFieldAffineMonicFibreStatement`. The proof follows §3 with two substitutions:
- Step 1's localization isomorphism is replaced by the blow-up chart `ψ : κ[s] → κ[A][t]`.
  - `ψ` is injective, and every element becomes an image after multiplying by a power of `t`.
  - A common factor of `ψf, ψf'` then pulls back to a factor of `s₀^N f, s₀^N f'`.
  - Removing the `s₀`-part leaves a common factor of `f, f'`.
  - The nonvanishing constant term `f'(x) ≠ 0` rules out powers of `t`.
- Step 1's Bézout-with-denominators is replaced by Mathlib's resultant.
  - Gauss (`IsPrimitive.dvd_of_fraction_map_dvd_fraction_map`) gives coprimality over `κ(A)`.
  - Then `resultant_eq_zero_iff` gives `Res ≠ 0`.
  - `resultant_map_map` and `exists_mul_add_mul_eq_C_resultant` specialize it at `a`.

The gcd under field extension (`isRelPrime_map_of_isRelPrime`) is proved with coefficient
functionals `ℓ : κ → K` and a `K`-basis of `κ`.

Sources: LSV arXiv:2110.11087 §2 (local copy in work/bh-pal-wire/lit); Panin arXiv:1707.01756
§§1–2.
