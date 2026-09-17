---
rg: 2
id: profinitely-closed-linear-coefficients-rank-condition-proof
kind: route
title: Evaluate the symmetric algebra at linear functionals on coinvariants of a finite quotient, where the group acts exactly, and bound the zeros of the denominators by Schwartz-Zippel
target: profinitely-closed-linear-coefficients-rank-condition
requires:
  - finite-field-point-models-give-the-rank-condition
---

Notation is as in the target. Definitions (P1)–(P3) and part (A) are from
`finite-field-point-models-give-the-rank-condition`. Part (A) says that finite-field point models give the rank
condition, and that the rank condition passes to unital subrings.

## 1. The symmetric algebra

- `M` is free over `R` with some basis `B`, so `A = Sym_R(M) = R[B]` is a polynomial ring and a domain.
- `G` acts on `A` by `R`-algebra automorphisms extending its action on `M`, and hence on `K = Frac A`.
- If `W_0` is the `R`-span of a finite subset of `B`, then `W_0` is a direct summand of `M`. So `Sym_R(W_0)`
  is a polynomial ring in `t = rank W_0` variables, and `W_0/pW_0 -> M/pM` is injective.

## 2. Point models (Theorem 1)

Fix finite `E ⊆ K`, finite `W_G ⊆ G` containing `e`, and `ε > 0`.

1. **Denominators.**
   - Write `b = a_b / c_b` with `a_b, c_b ∈ A` and `c_b ≠ 0`, for `b ∈ E`.
   - Put `Δ = ∏_(h ∈ W_G, b ∈ E) σ_h(c_b) ∈ A`, which is nonzero because `A` is a domain and each `σ_h` is
     injective.
   - Let `W_0` be the span of the finitely many basis elements occurring in `Δ`, so
     `Δ ∈ Sym_R(W_0) = R[y_1..y_t]`.
2. **Prime.**
   - If `R = F_q`: let `p = char F_q`.
   - If `R = Z`: choose a prime `p` for which `M` is residually finite mod `p` and `p` does not divide all
     coefficients of `Δ`. Only finitely many `p` fail the second condition, so such `p` exists.
   - Let `Δ̄ ∈ F_p[y_1..y_t]` (resp. `F_q[y_1..y_t]`) be the reduction of `Δ`, which is nonzero, with total
     degree `D`.
3. **Quotient.** By the definition, choose a finitely generated `W ⊇ W_0` and `N ⊴ G` of finite index with
   `W/pW -> C = (M/pM)_N` injective.
   - The composite `W_0/pW_0 -> W/pW -> M/pM` is injective (Section 1), so its first map is injective.
   - Hence `ι: W_0/pW_0 -> C` is injective.
4. **Points.**
   - `C` is a finitely generated `F_p[G/N]`-module, hence finite-dimensional.
   - Let `F = F_Q` with `Q` a power of `p` (a power of `q` when `R = F_q`), and let `V = Hom_R(C, F_Q)`, a finite
     set.
   - Each `v ∈ V` composes with `M -> C` to give an `R`-linear map `M -> F_Q`, which extends uniquely to a ring
     homomorphism `ṽ: A -> F_Q`.
   - `ker ṽ` is prime. Put `O_v = A_(ker ṽ) ⊆ K` and `e_v(a/c) = ṽ(a)/ṽ(c)`.
5. **Exact action.**
   - Since `N` is normal, `g(nm - m) = (g n g^(-1))(gm) - gm`, so `G` acts on `C`.
   - For `h ∈ G` define `T_h v = v ∘ σ_h` on `C`. Then `T_(h') T_h v = v ∘ σ_h ∘ σ_(h') = T_(hh') v`.
   - Put `σ(h) = T_h^(-1) ∈ Sym(V)`. Then `σ(h')^(-1) σ(h)^(-1) = T_(hh') = σ(hh')^(-1)` and `σ(e) = id`.
   - So (P3) holds for every `v`.
   - `(T_h v)~` and `ṽ ∘ σ_h` are ring homomorphisms `A -> F_Q` that agree on `M`, so they are equal.
6. **(P1) and (P2).** Let `V_good = {v : ṽ(Δ) ≠ 0}`, and take `v ∈ V_good`, `h ∈ W_G`, `b ∈ E`.
   - Every factor of `Δ` is nonzero at `ṽ`. In particular `(T_h v)~(c_b) = ṽ(σ_h c_b) ≠ 0`, so
     `E ⊆ O_(T_h v) = O_(σ(h)^(-1) v)` (with `h = e`, also `E ⊆ O_v`).
   - Likewise `σ_h b = σ_h a_b / σ_h c_b ∈ O_v`.
   - `e_(σ(h)^(-1) v)(b) = (T_h v)~(a_b) / (T_h v)~(c_b) = ṽ(σ_h a_b) / ṽ(σ_h c_b) = e_v(σ_h b)`.
7. **Counting.**
   - `ṽ` restricted to `Sym_R(W_0)` factors through `W_0 -> W_0/pW_0 -> C -> F_Q`.
   - So `ṽ(Δ) = Δ̄(ρ(v))` with `ρ(v) = v ∘ ι ∈ Hom(W_0/pW_0, F_Q) ≅ F_Q^t`.
   - `ι` is an injective linear map of `F_p`-vector spaces (resp. `F_q`), so `ρ: V -> F_Q^t` is a surjective group
     homomorphism, and all its fibres have the same size.
   - By Schwartz–Zippel, `Δ̄` has at most `D Q^(t-1)` zeros in `F_Q^t`, so `|V \ V_good| <= (D/Q)|V|`.
   - Taking `Q >= D/ε` gives a point model.

## 3. Rank condition (Theorem 2)

1. **Point models.** By Section 2 and part (A), `K ⋊ G` has the rank condition.
2. **Subfields.** A `G`-stable subfield `F ⊆ K` gives a unital subring `F ⋊ G ⊆ K ⋊ G`.
   - For a submodule `M' ⊆ M`, the map `Sym_R(M') -> Sym_R(M)` is injective. Over `F_q`, `M'` is a direct summand as
     a vector space. Over `Z`, `M'` is free abelian and the map is injective after `⊗ Q` on a torsion-free source.
3. **Directed unions.** An identity `AB = I_d` involves finitely many coefficients, so it lies in one member of a
   directed union.

## 4. Closure criterion (Theorem 3)

1. **Coinvariants.** Let `P = F_q[G]^n` and `K_N = ker(P -> F_q[G/N]^n)`.
   - The span of `(n-1)x` for `n ∈ N`, `x ∈ P` is `K_N`. It lies in `K_N`, and conversely `g e_i - n g e_i` spans
     `K_N`.
   - For `M = P/J`, `M_N = P/(J + K_N)`.
   - So the kernel of a finite-dimensional `W ⊆ M` in `M_N` is `W ∩ (J + K_N)/J`.
2. **Directed family.** `K_(N ∩ N') ⊆ K_N ∩ K_(N')`, so these kernels form a downward directed family of subspaces
   of `W`, with intersection `W ∩ (∩_N (J + K_N))/J`.
3. **Criterion.** A downward directed family of subspaces of a finite-dimensional space contains its intersection.
   - If `J` is closed, some kernel is `0` for every `W`.
   - Conversely, `x ∈ ∩_N (J+K_N) \ J` spans a line `W` that never injects.

## 5. Examples

1. **Permutation modules.** Let `M = R[G/L]`.
   - The coinvariants `(M/pM)_N` form the permutation module on the `N`-orbits of `G/L`, which are the cosets of
     `NL`. So `(M/pM)_N = F_p[G/NL]` (resp. `F_q[G/NL]`).
   - A finite subset of `M` lies in `W = R{c_1..c_r}` for distinct cosets `c_i`, a span of basis elements.
   - If `L = ∩_N NL`, then for `i ≠ j` some `N_(ij)` has `c_i^(-1) c_j ∉ N_(ij) L`. With `N = ∩ N_(ij)`, the `c_i`
     stay distinct in `G/NL`, so `ι` is injective for every `p`.
2. **Primitive vectors.** For `G = SL_3(Z)`, `G` is transitive on primitive vectors, and `L = Stab(e_1)`.
   - `Γ(m)L` fixes `e_1` modulo `m`.
   - So `∩_m Γ(m)L ⊆ {g : g e_1 = e_1} = L`.
3. **Direct sums.** Coinvariants commute with direct sums, and `(M/pM)_(N') -> (M/pM)_N` is surjective for
   `N' ⊆ N`. So injectivity persists when `N` shrinks, and `N_1 ∩ N_2` serves both summands for a common `p`.
4. **Lattices.** For `M = Z^n`, `N = ker(G -> GL_n(F_p))` gives `(M/pM)_N = M/pM`.

## 6. Calibration

- For `LC(X,k) ⋊ F_2` with a paradoxical action, the coefficient ring consists of locally constant functions and
  has idempotents.
- A point homomorphism to `F_Q` sends each indicator to `0` or `1`. The fraction of points where a nonzero indicator
  vanishes is the measure of a clopen set, which does not shrink as `Q -> ∞`.
- Step 2.7 is the step that fails, and the argument certifies nothing there.
