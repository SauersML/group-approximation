# sk-algebraic-putnam part 1: Laurent elements are suitable, and Laurent unimodular pairs are stable (2026-09-13)

Lane sk-algebraic-putnam. The target is an algebraic Putnam theorem: is `R = LC(X,F) ⋊_T Z`, for a minimal Cantor homeomorphism `T` and a field `F`, an exchange ring of stable rank one? This part proves the two statements below by residue maps. Both are ESTABLISHED here and unreviewed.

## 0. Statements
Let `(X,T)` be a minimal homeomorphism of the Cantor set, `F` a field and `R = LC(X,F) ⋊_T Z`, with `(fu^i)(f′u^j) = f(f′∘T^{−i})u^{i+j}`. Write `F[u^{±1}] ⊆ R` for the Laurent polynomials in `u`.

- **Lemma C (columnwise right ideals).** For every nonzero `q ∈ F[u^{±1}]` and every `z ∈ R`: `z ∈ qR` iff every column `zδ_t` of `z` in an orbit representation lies in `qV`.
- **Theorem S (suitability).** Every `p ∈ F[u^{±1}]` is suitable in `R`: there is an idempotent `e ∈ pR` with `1 − e ∈ (1−p)R`. The idempotent can be taken in a tower algebra `A_𝒫 ≅ ∏_a M_{h_a}(F)`.
- **Theorem L (Laurent pairs are stable).** Let `a ∈ R` and `0 ≠ q ∈ F[u^{±1}]` with `aR + qR = R`. Then `a + qc ∈ R^×` for some `c ∈ R`, and the unit can be taken in a tower algebra.
- **Corollary.** Every unimodular row `(p_1,…,p_n)` over `F[u^{±1}]` is stable in `R`: `p_1 + Σ_{i≥2} p_i c_i ∈ R^×` for some `c_i ∈ R`.

In `F[u^{±1}]` itself both statements fail (§5). So the towers of a minimal Cantor system repair the Laurent obstructions to the exchange property and to stable rank one.

## 1. Setting
- **Orbit representation.** Fix `x ∈ X` and put `V = F^{(Z)}` with basis `δ_t`. Put `fδ_t = f(T^tx)δ_t` and `uδ_t = δ_{t+1}`. Then `ufu^{−1}δ_t = f(T^{t−1}x)δ_t = (f∘T^{−1})δ_t`, as the multiplication requires.
  - For `a = Σ_j f_ju^j`, `aδ_n = Σ_j f_j(T^{n+j}x)δ_{n+j}`. So `a` acts by a banded matrix with entries `a(m,n) = f_{m−n}(T^mx)`.
  - The representation is faithful: every orbit is dense and the `f_j` are continuous.
- **Towers.** A Kakutani–Rokhlin partition `𝒫` has clopen bases `B_a` with heights `h_a` and levels `T^iB_a` (`0 ≤ i < h_a`) partitioning `X`. Heights can be made as large as wanted, and the base atoms can be refined so that they determine any given locally constant data along the whole tower.
  - `e_{T^{i′}B_a}u^{i′−i}` sends `δ_{b+i}` to `δ_{b+i′}` when `b` is a base position of type `a`, and kills all other `δ_n`.
  - So block-diagonal operators, whose block on each tower occurrence is a matrix `G_a ∈ M_{h_a}(F)` depending only on the type `a`, lie in `R`. They form `A_𝒫 ≅ ∏_a M_{h_a}(F)`.
- **Residues.** For `q ∈ F[u^{±1}]` write `q = u^αq_0` with `q_0 ∈ F[u]`, `q_0(0) ≠ 0`, `d = deg q_0`, and `A_q := F[u]/(q_0)`, of dimension `d`. The class `ū` is a unit of `A_q`. Identify `V ≅ F[u^{±1}]` by `δ_t ↦ u^t`, and let `ρ_q : V → A_q`, `δ_t ↦ ū^t`, be the quotient map. Its kernel is `q_0V = qV`.

## 2. Lemma C
*Only if.* `(qy)δ_t = q(yδ_t) ∈ qV`.

*If.* As `u^α` is a unit, `qR = q_0R` and `qV = q_0V`. Let `z = Σ_j ζ_ju^j` have propagation `w`, so `supp zδ_t ⊆ [t−w, t+w]`. Suppose every `zδ_t ∈ q_0V`.
1. **Support of quotients.** If `v ∈ q_0V` has support in `[m,M]`, then `v = u^mP` with `deg P ≤ M−m`. `q_0` divides `P` in `F[u]`, because `q_0(0) ≠ 0`. So the unique `v′` with `q_0v′ = v` is supported in `[m, M−d]`.
2. **The quotient operator.** Write `q_0 = Σ_{i=0}^d κ_iu^i` and `q_0^{−1} = Σ_{i≥0} λ_iu^i` in `F[[u]]`. Back-substitution from the lower end gives `(yδ_t)_m = Σ_{k=t−w}^{m} λ_{m−k} z(k,t)`. This is a finite sum, and the support bound of step 1 truncates it at `m ≤ t+w−d`.
3. **Membership in R.** `z(k,t) = ζ_{k−t}(T^kx)`, so `y(m,t) = η_{m−t}(T^tx)` with `η_i(ξ) = Σ_{j=−w}^{i} λ_{i−j} ζ_j(T^jξ)` for `−w ≤ i ≤ w−d`. These are locally constant. So `y = Σ_i (η_i∘T^{−i})u^i ∈ R`.
4. **Conclusion.** `q_0y = z` in the faithful representation, so `z ∈ q_0R`. ∎

## 3. Theorem S
Let `p ∈ F[u^{±1}]`. If `p = 0` or `1−p = 0`, take `e = 0` or `e = 1`. Otherwise write `p = u^αp_0` and `1 − p = u^βr_0` as in §1. The polynomials `p_0` and `r_0` are coprime: a common factor divides `p` and `1−p`, hence `1`. Put `D = deg p_0 + deg r_0`.
1. **Tower algebra.** Choose `𝒫` with all heights `h_a ≥ D`.
2. **One block.** On `F^h` (levels `0,…,h−1`) let `ρ^0 = (ρ_p, ρ_{1−p}) : F^h → A_p × A_{1−p}`, `δ_i ↦ (ū^i, ū^i)`. By the Chinese remainder theorem this is the quotient map `F^h → F[u]/(p_0r_0)`, and `h ≥ D` consecutive powers of `ū` span it. So `ρ^0` is onto. Let `K = ker ρ^0`, choose `C_p` and `C_{1−p}` mapping isomorphically onto `A_p × 0` and `0 × A_{1−p}`, and let `E_h` be the projection onto `C_{1−p}` along `K ⊕ C_p`. Then:
   - `ρ_p E_h = 0`, since `C_{1−p} ⊆ ker ρ_p`;
   - `ρ_{1−p}(1 − E_h) = 0`, since `K ⊕ C_p ⊆ ker ρ_{1−p}`.
3. **Glue.** `e = ⊕ E_{h_a}` over the tower occurrences is an idempotent of `A_𝒫 ⊆ R`. For `t = b+i` in an occurrence of height `h`, `ρ_p(eδ_t) = ū^b ρ_p(E_hδ_i) = 0`, and likewise `ρ_{1−p}((1−e)δ_t) = 0`. By Lemma C, `e ∈ pR` and `1 − e ∈ (1−p)R`. ∎

## 4. Theorem L
Let `ar + qs = 1` with `r, s ∈ R`, and normalize `q = u^αq_0` as in §1. Let `w_r` be the propagation of `r`.
1. **Residues of a.** Apply `ρ_q` columnwise. `ρ_q(qsδ_t) = 0`, so `ρ_q ∘ a ∘ r = ρ_q` as maps `V → A_q`. For `a = Σ_j f_ju^j`, `ρ_q(aδ_n) = ū^n τ(T^nx)` with `τ(ξ) = Σ_j f_j(T^jξ)ū^j ∈ A_q`. This is locally constant in `ξ`.
2. **Towers.** Choose `𝒫` with heights `h ≥ 2w_r + d + 2`, with base atoms refined so that the values `τ(T^iξ)`, `0 ≤ i < h`, are constant on each atom.
3. **One block.** For an occurrence `[b, b+h)` define `φ_0, ψ_0 : F^h → A_q` by `φ_0(δ_i) = ū^i` and `ψ_0(δ_i) = ū^iτ(T^{b+i}x)`. So `ψ_0` depends only on the atom of `T^bx`.
   - `φ_0` is onto because `h ≥ d`.
   - `ψ_0` is onto. For `m` at distance `> w_r` from both ends, `ū^m = ρ_q(δ_m) = Σ_{n} r(n,m)ρ_q(aδ_n)` with all `n` inside the occurrence. So `ū^{−b}ρ_q(δ_m) ∈ im ψ_0`, and there are at least `d` consecutive such `m`.
   - Two surjections `F^h → A_q` differ by an automorphism: map `ker ψ_0 → ker φ_0` by any isomorphism, and a complement `C_ψ → C_φ` by `(φ_0|_{C_φ})^{−1}∘ψ_0`. This gives `G ∈ GL_h(F)` with `φ_0∘G = ψ_0`, chosen per atom.
4. **The unit.** `g = ⊕ G` lies in `GL_1(A_𝒫) ⊆ R^×`. For `t = b+i`, `ρ_q(gδ_t) = ū^bφ_0(Gδ_i) = ū^bψ_0(δ_i) = ρ_q(aδ_t)`. So every column of `g − a` lies in `qV`. By Lemma C, `g − a = qc` with `c ∈ R`, and `a + qc = g`. ∎

**Corollary (rows).** Let `(p_1,…,p_n)` be unimodular over `F[u^{±1}]` and `q = gcd(p_2,…,p_n) = Σ_{i≥2} p_iλ_i`. Then `p_1` and `q` are coprime, so `p_1R + qR = R`. Theorem L gives `p_1 + qc ∈ R^×`, that is `p_1 + Σ_i p_i(λ_ic) ∈ R^×`. ∎

## 5. Model tests
- **F_2[u^{±1}] fails Theorem S.** `a = u + u²`: the only idempotents of the domain `F_2[u^{±1}]` are `0` and `1`, and neither `a` nor `1 − a = 1+u+u²` is a unit. This is sk-stable-rank-a §2.2's calibration, where a tower-to-base witness was found in `R` for this one element. Theorem S covers every Laurent element.
- **F_2[u^{±1}] fails Theorem L.** Take `q = Φ_5(u) = 1+u+u²+u³+u⁴`, irreducible over `F_2` since the order of 2 mod 5 is 4, so `A_q = F_16`. Take `p = 1+u`. The units of `F_2[u^{±1}]` are the powers `u^k`, and `ū` has order 5 in `F_16^×`, with powers `1, ū, ū², ū³, ū³+ū²+ū+1`. None of these is `1+ū`. So no `p + qc` with `c ∈ F_2[u^{±1}]` is a unit, while Theorem L gives one with `c ∈ R`.
- **Where the hypotheses enter.**
  - Minimality supplies dense orbits (faithfulness) and Kakutani–Rokhlin partitions with long heights. For the one-point system, `R = F[u^{±1}]`, and both theorems fail as above.
  - `q ≠ 0` and `q_0(0) ≠ 0` make `A_q` finite-dimensional with `ū` a unit.
  - Commutation with `u` makes `ρ_q` translation-covariant, so the block conditions depend only on local data. This is exactly what fails for a general `b ∈ R` (§6).
- **Sanity.** For `q` a unit, `A_q = 0` and any unit `g` works. For `q` coprime to `a = p` Laurent, the unit found is in `A_𝒫` and not in `F[u^{±1}]`, as it must be.

## 6. Scope and what remains open
- **Not proved:** the exchange property for general `a ∈ R`, and stable rank one for general pairs `(a,b)`. Both open nodes stay open.
- **Where the method dies.**
  - For general `b ∈ R`, `bR` is not characterized columnwise. Example: `b = e_W`, where `e_WR` is the set of elements with vanishing rows off `W`.
  - `V/bV` is typically infinite-dimensional or not translation-covariant.
  - The residue method needs `b` in a commutative subalgebra over which `V` is free of finite rank.
- **Extension, sketched only.** The same proofs apply to `q(w)` for twisted shifts `w = fu^{±1}` with `f ∈ LC(X,F^×)`. `V` is free of rank one over `F[w^{±1}]` with basis `δ_0`. The cocycle scalars along a block are locally determined, so the block conditions stay homogeneous. Not written as a node.
- **Next steps in this lane.**
  - pairs `(a, e_W)` with an idempotent second entry, since exchange rings reduce general pairs to that case;
  - the gluing technique of sk-free-6 Theorem D (end corrections with Fredholm index) for general `b`.

## 7. Credit and search bounds
- **Imports recalled, not checked at source:** the definitions of suitable elements and exchange rings (Nicholson 1977; Warfield 1972) and of stable range (Bass, Vaserstein). No numbered theorem is used.
- **Checked:** Camillo–Yu, Comm. Algebra 22 (1994) 4737–4749, quoted through arXiv:1402.4706: an exchange ring has stable range one iff every regular element is unit-regular. It is not used in the proofs above; it bears on the next step.
- **Nearest prior on main:** sk-stable-rank-a §2.2, the single element `u+u²` over `F_2`.
- **Search:** three web searches (Steinberg algebras and exchange or stable rank; Camillo–Yu; separative exchange rings) and a grep of main for Laurent, suitable and unimodular nodes. No algebraic exchange or stable-rank result for `LC(X,F) ⋊ Z` was found.
