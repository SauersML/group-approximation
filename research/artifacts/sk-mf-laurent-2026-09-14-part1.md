# sk-mf-laurent: is C*_r(G_X) MF? Unipotent spectra of the Laurent lattice (2026-09-14, part 1)

Lane sk-mf-laurent (wave 12). Everything here is unreviewed; the review requests are queued in `sk2/queue/verify.txt`.

## 0. Plan and verdict
**Question.** Is `C*_r(G_X)` MF? By `laurent-sl4-stability-makes-overgroups-reduced-non-mf` (sk-verify-7 PASS) it is
not MF if `Λ = SL_4(A)`, `A = F_q[t,t^{-1}]`, is point-norm matricially stable.

**Named target (done here).** The Laurent analogue of `sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full`.

**Results.**
1. **Theorem A (dichotomy).** For every unital representation of `SL_d(A)`, `d ≥ 3`, the joint spectrum of the column
   unipotent `A^{d-1}` is either all of `Â^{d-1}` or finite. In the finite case the representation factors through a
   congruence quotient `SL_d(A/J)`, `J ≠ 0`.
2. **Theorem B (norm four off the full spectrum).** A unital representation of `C*(Λ)` whose column unipotent spectrum
   is not full gives the block-`SL_2` Laplacian norm 4.
3. **Reduction.** The corona crux "every corona representation of `Λ` gives block-`SL_2` norm 4" is implied by stability
   and implies that `C*_r(G_X)` is not MF. By Theorem B it is equivalent to its full-spectrum case, which contains every
   MF embedding.

**Verdict on MF of `C*_r(G_X)`:** still open. The congruence mechanism is now pushed to every representation with
non-full spectrum, so the only remaining case is full (Haar) spectrum, exactly as for `SL_4(Z)`.

## 1. Setup
- `q` a prime power, `p` its characteristic, `A = F_q[t,t^{-1}]`, `m ≥ 2`.
- `Â` is the compact dual of the discrete group `(A,+)`; every character has order dividing `p`. Fix a nontrivial
  `ψ : F_q → μ_p`. Sequences `c ∈ F_q^{Z}` give characters `χ_c(Σ a_n t^n) = ψ(Σ a_n c_n)`, a homeomorphism
  `F_q^Z ≅ Â`.
- `A` acts on `Â` by `(a·χ)(b) = χ(ab)`; multiplication by `t` is the shift. For `χ ∈ Â`, `Ann(χ) = {a : a·χ = 1}` is an
  ideal of the PID `A`. Normalize a generator `h ∈ F_q[t]` with `h(0) ≠ 0`, and write `deg Ann(χ) = deg h`.
- **Windows.** `W_N = span{t^n : |n| ≤ N}`, of dimension `L = 2N+1`. Restriction `r_N : Â → Ŵ_N ≅ F_q^L` is continuous
  and open, and the cylinder sets `r_N^{-1}(π)` form a base of the topology.
- **The dual action.** For `g ∈ E_m(A)` acting on columns `v ∈ A^m`, a unital *-homomorphism `σ` with
  `σ(g)σ(u(v))σ(g)^{-1} = σ(u(gv))` has joint spectrum `K ⊆ Â^m` of `σ(u(v))` invariant under `χ ↦ χ∘g`. For
  `g = e_ij(a)`, `(χ∘e_ij(a))(v) = χ(v)·χ_i(a v_j)`. In additive notation on coordinates this is
  `χ_j ↦ χ_j + a·χ_i`, with the other coordinates unchanged.

## 2. Four elementary facts
- **(F1) Rich coordinates cover windows.** If `Ann(y) = 0`, or `deg Ann(y) ≥ L`, then `r_N(A·y) = Ŵ_N`.
  - Proof: `r_N(A·y) = r_N(closure(A·y))` since `Ŵ_N` is finite, and `closure(A·y)^⊥ = Ann(y)` in `A`.
  - The image of a closed subgroup `H` is all of `Ŵ_N` iff `W_N ∩ H^⊥ = 0`.
  - A nonzero multiple of `h` (with `h(0) ≠ 0`) has exponent span `≥ deg h ≥ L > 2N`, the span of `W_N`.
- **(F2) Few poor characters.** `|{z : Ann(z) ≠ 0, deg Ann(z) < L}| < q^{2L}`. There are fewer than `q^L` normalized
  `h` with `deg h < L`, and `{z : h·z = 1} = (A/(h))^` has `q^{deg h}` elements.
- **(F3) Fibres.** If `Ann(y) = (g)` with `deg g = D ≥ L`, every fibre of `r_N` on `A·y` has `q^{D-L}` elements, because
  `|A·y| = |A/(g)| = q^D` and `r_N|_{A·y}` is onto by (F1). If `Ann(y) = 0`, every fibre is infinite: the kernel of
  `A → Ŵ_N`, `b ↦ r_N(b·y)`, is infinite.
- **(F4) Unbounded annihilators.** Let `K ⊆ Â^m`, and suppose there is no nonzero ideal `J` with `J·χ_i = 1` for all
  `χ ∈ K` and all `i`. Then for every `M` some `χ ∈ K` has a coordinate `χ_i` with `Ann(χ_i) = 0` or `deg Ann(χ_i) > M`.
  - Otherwise all coordinate annihilators lie among the finitely many ideals `(h)`, `deg h ≤ M`, and their product is a
    nonzero uniform `J`.

## 3. Theorem A: finite or full
**Statement.** Let `m ≥ 2` and let `K ⊆ Â^m` be closed and invariant under the dual action of `E_m(A)`. Then either
- (a) `K ⊆ ((A/J)^m)^` for a nonzero ideal `J`, so `K` is finite; or
- (b) `K = Â^m`.

**Proof.** Assume (a) fails. Since `K` is closed it suffices to show that `K` is dense. Fix `N`, `L = 2N+1`, and
patterns `π_1, …, π_m ∈ Ŵ_N`.
1. By (F4), pick `χ ∈ K` and a coordinate, after renumbering `χ_1 = y`, with `Ann(y) = 0` or `deg Ann(y) > 3L`.
2. **Enrich coordinate 2.** By (F3) the set `{w ∈ A·y : r_N(χ_2 + w) = π_2}` has `≥ q^{2L}` elements, or infinitely many.
   By (F2) it contains `w = b·y` with `z = χ_2 + b·y` satisfying `Ann(z) = 0` or `deg Ann(z) ≥ L`. Apply `e_12(b)`:
   `(y, z, χ_3, …) ∈ K`, with `r_N(z) = π_2`.
3. **Coordinates `k ≥ 3`.** By (F1) choose `b_k` with `r_N(χ_k + b_k·y) = π_k` and apply `e_1k(b_k)`.
4. **Coordinate 1.** By (F1), since `z` is rich, choose `b` with `r_N(y + b·z) = π_1`, and apply `e_21(b)`. This changes
   only coordinate 1.

The resulting element of `K` has windows `π_1, …, π_m`. So `K` meets every basic open set and `K = Â^m`. ∎

**Model tests.**
- `m = 1`: no elementary operations, and the claim fails. The single orbit `{χ}` of a non-torsion `χ` is closed,
  infinite and proper.
- The trivial representation: `K = {1}`, case (a) with `J = A`.
- The regular representation: Haar spectrum, case (b).
- `K = (A/J)^m` dual for `J = (t−1)^k`: case (a).
- The union over all `k` of those sets is invariant but not closed, and its closure is full, consistent with the
  theorem.

**Corollary A′.** Let `d ≥ 3` and `σ : C*(SL_d(A)) → B` be unital. Let `K` be the joint spectrum of `σ(u(v))`,
`u(v) = I + Σ_{i<d} v_i e_{i,d}`. Either `K = Â^{d-1}`, or `σ` factors through `C*(SL_d(A/J))` for some nonzero `J`.
- `K` is closed (the Gelfand spectrum of `σ(C*(A^{d-1}))`) and invariant under the upper-left `E_{d-1}(A)`.
- In case (a), `σ(u(v)) = 1` for `v ∈ J^{d-1}`, since the Gelfand transform of `σ(u(v)) − 1` vanishes on `K`. So
  `e_{i,d}(J) ⊆ ker σ` for `i < d`.
- **Normal closure.** `[e_{i,d}(j), e_{d,k}(1)] = e_{i,k}(j)` for `k ≠ i, d`. Conjugating by signed permutations in
  `E_d(A)` then gives `e_{d,k}(J)`. So `E_d(A,J) ⊆ ker σ`.
- By Bass–Milnor–Serre Corollary 4.3 b) (`bms-congruence-kernel-trivial-not-totally-imaginary`),
  `SL_d(A,J) = E_d(A,J)`. So `σ` factors through `SL_d(A)/SL_d(A,J) ≅ SL_d(A/J)`; the reduction is onto because
  `A/J` is finite.

## 4. Theorem B: norm four off the full spectrum
**Statement.** Let `Λ = SL_4(A)` and `σ : C*(Λ) → B` be unital. Suppose the column unipotent spectrum is not all of
`Â^3`. Let `S, T ∈ SL_2(F_q[t])` generate a free group (Nagao; item 3 of
`ring-model-permutation-vectors-block-strong-convergence`), placed in the upper-left block, and let
`z = S+S^{-1}+T+T^{-1}`. Then `‖σ(z)‖ = 4`. If `B = B(H)`, the block `SL_2(A)` fixes a nonzero vector.

**Proof.**
1. By Corollary A′, `σ` factors through `C*(SL_4(A/J)) = ⊕_ρ M_{d_ρ}`, `J ≠ 0`.
2. `σ` is unital, so `σ(p_ρ) ≠ 0` for some central projection `p_ρ`. On the simple summand `σ` is isometric.
3. `A/J ≅ F_q[t]/(f)`, with `f` the normalized generator, is a finite principal ideal ring. By
   `sl4-over-finite-chain-rings-has-sl2-invariant-vectors` (sk-verify-5 PASS), `ρ` has a nonzero vector fixed by
   `SL_2(A/J)`, so `‖ρ(z)‖ = 4`.
4. `4 ≥ ‖σ(z)‖ ≥ ‖σ(z p_ρ)‖ = ‖z p_ρ‖ = ‖ρ(z)‖ = 4`. On `H`, the range of `σ(p_ρ)` is `ρ`-isotypic and contains
   `ρ`'s fixed vectors. ∎

**Model tests.**
- The regular representation has full spectrum and `‖λ(z)‖ = 2√3 < 4` (Kesten), so the hypothesis is needed.
- Genuine finite-dimensional representations have finite spectrum and norm 4, recovering
  `laurent-sl-n-representations-have-sl2-invariant-vectors`.

## 5. The corona crux and what it decides
**Crux.** Every unital `π : C*(Λ) → Q = ∏_n M_{k_n}/⊕_n M_{k_n}` has `‖π(z)‖ = 4`.
- **Stability ⇒ crux.** Lift `π(g)` to unitaries `φ_n(g)` (an asymptotic homomorphism), correct them to genuine
  `π_n`, and apply Theorem 1 of sk-matricial-stability in every coordinate with `k_n ≥ 1`. The corona norm is `limsup`.
- **Crux ⇒ `C*_r(G_X)` not MF.**
  - An injective `ι : C*_r(Γ) → Q` with `Λ ≤ Γ` restricts isometrically to `C*_r(Λ)`; make it unital by cornering.
  - The composite `C*(Λ) → C*_r(Λ) → Q` is unital, so `‖π(z)‖ = 4`.
  - Isometry gives `‖λ_Λ(z)‖ = 2√3`, a contradiction.
  - `Γ = G_X` contains `Λ` by `subshift-elementary-groups-contain-laurent-sl-n-lattices`.
- **Theorem B ⇒ the crux is equivalent to its full-spectrum case.** Every MF embedding of `C*_r(Λ)` has Haar spectrum on
  `A^3`, so the congruence mechanism reaches none of them.

## 6. Refinement of the rational-cohomology attempt (sketch, not established)
sk-matricial-stability's even-cohomology note says only `H^6(Λ;Q)` can carry Dadarlat's obstruction. The purity step can
be stated precisely:
- Harder identifies `H^6(Λ;Q)` with the multiplicity of `St_0 ⊗ St_∞`, unramified elsewhere, in the discrete spectrum.
- **Cuspidal part.** Lafforgue attaches a pure lisse ℓ-adic sheaf on `G_m` with local-global compatibility. Steinberg
  at `0` means a tame unipotent inertia action with `N ≠ 0`.
  - Pure lisse sheaves are geometrically semisimple (Deligne, Weil II, Thm 3.4.1(iii)).
  - Tame at `0` and `∞`, the geometric sheaf factors through the abelian tame `π_1(G_{m,F̄_q})`. A semisimple
    representation of an abelian group has semisimple image, so inertia at `0` is both semisimple and unipotent,
    hence trivial, and `N = 0`. Contradiction.
- **Residual part.** Mœglin–Waldspurger residual representations of `GL_4` are Speh-type, with non-generic local
  components, never Steinberg.
- So `H^6(Λ;Q) = 0` and `Λ` is `Q`-acyclic: Dadarlat's even-cohomology obstruction is void.
- Imports not read at source: Harder, Lafforgue, Deligne Weil II, Mœglin–Waldspurger.

## 7. Nodes landed with this artifact
- `laurent-unipotent-spectra-are-finite-or-full` (+ `-finite-or-full-proof`): Theorem A and Corollary A′.
- `laurent-sl4-block-sl2-norm-four-off-full-unipotent-spectrum` (+ `laurent-sl4-block-sl2-norm-four-off-full-spectrum-proof`): Theorem B.
- `laurent-sl4-corona-representations-have-block-sl2-norm-four` (OPEN crux), with routes
  `laurent-corona-norm-four-from-matricial-stability` and `subshift-el-reduced-not-mf-from-laurent-corona-norm-four`.
- Attempts merged onto `laurent-sl4-matricially-stable` and `subshift-elementary-group-reduced-cstar-is-not-mf`.

## 8. Sharpest next target
The full-spectrum case in positive characteristic. Given a corona representation with Haar spectrum on `A^3`, build
asymptotically invariant vectors for the block `SL_2(A)` from far-level spectral projections. Clopen cylinder
projections for finite subgroups `F ≤ A^3` exist in `σ(C*(A^3))`. The obstruction to rule out is weak containment in
`λ_{SL_2(A)}` at annihilator-zero characters. One lane at most; famous-hard, and it does not gate the paper.
