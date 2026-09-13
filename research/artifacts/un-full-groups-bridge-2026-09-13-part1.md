# Full groups and elementary groups from one finite model

Lane `un-full-groups-bridge` (UN swarm), 2026-09-13. Part 1: the measure side. Written proofs, UNREVIEWED.
Credits: Grigorchuk–Medynets (arXiv:1105.0719, LEF full groups of minimal Z-systems), Xin Ma (arXiv:2209.00580,
Thm C), Kerr–Nowak (residually finite actions), Matui and Nekrashevych (full groups), and lane `un-measure`
(Lemma S and Theorem A in `un-measure-residually-finite-lef-rings-2026-09-13-part1.md`, whose argument §2 adapts).

## 0. Summary

`Γ` is a countable group acting minimally and topologically freely on a Cantor space `X` by `α`, with a compatible
metric `d`. `k` is a field, `𝒢 = X ⋊ Γ` is the transformation groupoid, and `R = A_k(𝒢) = LC(X,k) ⋊ Γ`. The topological
full group `[[α]]` sits in `R^×` as the units `1_B` of full compact open bisections
(`full-group-units-embed-in-steinberg-algebras`).

**Theorem 1.** These are equivalent:
- (i) `α` is *locally residually finite* (LRF, Definition 1.1);
- (ii) `R` has a *combinatorial matricial model* (Definition 1.2) over some field;
- (ii') `R` has a combinatorial matricial model over every field.

They imply:
- (a) `[[α]]` embeds in an algebraic ultraproduct `∏_ω Sym(N_n)`, so `[[α]]` is LEF;
- (b) for `k = F_q`, every finitely generated subgroup of every `GL_m(R)` is LEF. If `R` is finitely generated and
  `n >= 3`, then `EL_n(R)` is a finitely generated LEF group with property (T).

So the same finite models that make the full group LEF make the Kazhdan elementary groups LEF. The following are one
statement, restricted to the permutation units `1_B` or to the elementary matrices of the same model:
- Grigorchuk–Medynets: `[[T]]` is LEF for minimal Z-systems;
- Ma's Theorem C: `[[α]]` is LEF for RF actions;
- the Pestov 9.1 ring and `un-measure`'s Theorem A: `EL_n` is LEF.

**Where the bridge stops (§3).** For aperiodic free minimal `Z^2`-SFTs (Labbé's `Ω_U`), LRF fails, so no combinatorial
model exists. Any matricial model must be genuinely *quantum*, i.e. not induced by partial permutations. Neither
Theorem 1 nor Ma's Theorem C then says anything about `[[α]]` or `EL_n(R)`.

## 1. Definitions

**Definition 1.1 (LRF).** `α` is *locally residually finite* if, for every finite `F ⊆ Γ` with `e ∈ F` and every
`ε > 0`, there are a finite nonempty `E ⊆ X` and a map `β : F -> Sym(E)` with
- `β(e) = id`;
- `β(g)β(h) = β(gh)` whenever `g, h, gh ∈ F`;
- `d(α(g)z, β(g)z) < ε` for all `z ∈ E` and `g ∈ F`.

Kerr–Nowak residual finiteness (as quoted in `extensions-of-aperiodic-sfts-are-not-residually-finite-actions`) asks
for a genuine `Γ`-action on an `ε`-dense `E`. Restricting it to `F` and forgetting density gives LRF. So RF ⇒ LRF.

**Definition 1.2 (combinatorial matricial model).** A *combinatorial matricial model* of `R` is an injective unital ring
homomorphism `Ψ = [ψ_n]_ω : R -> ∏_ω M_(N_n)(k)` (algebraic ultraproduct, non-principal `ω`) such that, for every
compact open bisection `B ⊆ 𝒢`, `Ψ(1_B)` has a representative sequence of partial permutation matrices. These are
`0/1` matrices with at most one `1` in each row and each column.

**Two facts about partial permutation matrices (ppm).**
- (P1) An idempotent ppm is diagonal. If `Pδ_z = δ_w` with `w ≠ z`, then `P^2 δ_z = Pδ_w`. Idempotence forces
  `Pδ_w = δ_w`, so row `w` has two `1`s, which is a contradiction.
- (P2) If ppms `P, Q` satisfy `PQ = I`, then `P` is a permutation matrix. `P` has full rank, so it has a `1` in every
  row and every column.

## 2. Proof of Theorem 1

**(i) ⇒ (ii') (adapting `un-measure` Theorem A).**
- **Setup.**
  - Fix symmetric finite sets `S_n ∋ e` increasing to `Γ`, let `F_n = S_n^3`, and fix `ε_n -> 0`.
  - Choose `(E_n, β_n)` for `(F_n, ε_n)`, and let `P_n(g)` be the permutation matrix `δ_z ↦ δ_(β_n(g)z)` (`g ∈ F_n`).
  - On normal forms `r = Σ_g f_g u_g` with `supp r ⊆ S_n`, put `ψ_n(r) = Σ_g D_n(f_g) P_n(g)`, where
    `D_n(f) = diag(f(z))_(z ∈ E_n)`. Outside that window, `ψ_n` is any additive extension.
- **Window `W_n`.** The `r` with `supp r ⊆ S_n` and all `f_g` constant on sets of diameter `< ε_n`. Every `r` lies in
  `W_n` for large `n`.
- **Multiplicativity on `W_n`.** For `f u_g, f' u_h ∈ W_n`, on `δ_z` with `w = β_n(gh)z`:
  - `ψ_n(f u_g)ψ_n(f' u_h)δ_z = f(w) f'(β_n(h)z) δ_w`, using `P_n(g)P_n(h) = P_n(gh)` (`g, h, gh ∈ F_n`);
  - `ψ_n(f(f'∘α(g)^(-1)) u_(gh))δ_z = f(w) f'(α(g^(-1))w) δ_w`.
  - Since `g^(-1), gh, h ∈ F_n` and `β_n` is multiplicative there, `β_n(g^(-1))w = β_n(h)z`. Also
    `d(α(g^(-1))w, β_n(g^(-1))w) < ε_n`, and `f'` is constant on `ε_n`-sets, so the coefficients agree. Additivity and
    `ψ_n(1) = I` (because `β_n(e) = id`) are clear.
- **Injectivity.** `R` is simple, since `𝒢` is minimal and effective (`steinberg-algebra-simple-iff-minimal-effective`).
  Lemma S (`simple-rings-with-local-matrix-models-are-matricial`) then makes `Ψ` injective.
- **Combinatorial.**
  - A basic bisection `{[g,x] : x ∈ U}` has `1_B = 1_(α(g)U) u_g`, with image `D_n(1_(α(g)U))P_n(g)`, a ppm.
  - A general compact open bisection is a finite disjoint union of basic ones `B_i = (g_i, U_i)`. The `r(B_i)` are
    pairwise disjoint, and so are the `s(B_i) = U_i`.
  - Row supports `E_n ∩ α(g_i)U_i` are disjoint. Column `z` of term `i` is nonzero iff `β_n(g_i)z ∈ α(g_i)U_i`.
  - For `ε_n` below a Lebesgue number of the partition generated by the `U_i`, and `g_i^(-1) ∈ F_n`, that happens iff
    `z ∈ U_i`, so column supports are disjoint too.
  - Hence the sum is a ppm for large `n`. This works over every field.

**(ii) ⇒ (i).**
- **Permutations.** Let `Ψ` be combinatorial and `F ∋ e` finite. Each `u_g = 1_(B_g)` with `B_g` a full bisection, and
  `u_g u_(g^(-1)) = 1`. By (P2), for `ω`-almost every `n`, `ψ_n(u_g)` is a permutation matrix `P_n(g)`, for all `g ∈ F`.
  Put `β_n(g)` = the permutation.
- **Partial homomorphism.** `u_g u_h = u_(gh)` gives `β_n(g)β_n(h) = β_n(gh)` for `g, h, gh ∈ F` (`ω`-a.e.), and
  `β_n(e) = id`.
- **Positions.**
  - Fix `ε`. Take a clopen partition `𝒫` of `X` into sets of diameter `< ε` that is fine enough that each `α(g)` (`g ∈ F`)
    maps every atom into a set of diameter `< ε`. Each `1_U` (`U ∈ 𝒫`) is a bisection unit and an idempotent, so
    `ψ_n(1_U) = diag(χ_(E_n(U)))` by (P1).
  - `ω`-a.e. the sets `E_n(U)` partition `{1..N_n}`, and `u_g 1_U u_g^(-1) = 1_(α(g)U)` gives
    `β_n(g)E_n(U) = E_n(α(g)U)`, where the right side is a union of atoms.
- **Transport.** Atoms are infinite (Cantor), so choose an injective `ζ : {1..N_n} -> X` with `ζ(E_n(U)) ⊆ U`, and
  transport `β_n` to `E = ζ({1..N_n})`. For `z ∈ E_n(U)`, both `α(g)ζ(z)` and `ζ(β_n(g)z)` lie in the set `α(g)U` of
  diameter `< ε`. This is LRF.
- **Field independence.** (ii) over one field gives (i), and (i) gives (ii') over every field.

**(a).** A full compact open bisection `B` gives a unit `1_B` with inverse `1_(B^(-1))`. By (P2), `Ψ(1_B)` is `ω`-a.e. a
permutation matrix. `Ψ` is injective and multiplicative, so `[[α]] -> ∏_ω Sym(N_n)` is an injective homomorphism. A
subgroup of an algebraic ultraproduct of finite groups is LEF.

**(b).** Same as `residually-finite-actions-give-matricial-crossed-products` item 3: `GL_m(R) ↪ ∏_ω GL_(mN_n)(F_q)`.
Property (T) comes from `elementary-groups-over-fg-rings-have-property-t`. ∎

**Model tests.**
- **`Γ = Z`, minimal subshift.** RF (Pimsner, Kerr–Nowak Prop 7.1 via Ma), so (a) is Grigorchuk–Medynets and (b) is
  the Pestov ring.
- **Cuntz groupoid.** It is not a group action, but its algebra has no matricial model at all
  (`matricial-steinberg-algebras-have-invariant-measures`: `μ(X) = 2μ(X)`). Consistently, no combinatorial model
  exists.
- **Non-minimal action with a fixed point.** Theorem 1 is not claimed. `R` is not simple and Lemma S fails, as it must.

## 3. Where the bridge stops: `Z^d` and quantum models

**Proposition 3.1.** For `Γ = Z^d`, LRF is equivalent to: for each `ε` and radius `r` there is a finite `E ⊆ X` with a
genuine `Z^d`-action `ε`-following `α` on the ball `B_r`.

*Proof.* Take `F = B_(3r)`. Then `β(e_i)β(e_j) = β(e_i+e_j) = β(e_j)β(e_i)` exactly, so the `β(e_i)` commute and
generate a genuine action. By induction inside `F`, `β(g)` agrees with it on `B_r`. The converse is clear. ∎

**Corollary 3.2.** A free minimal `Z^2`-subshift of an SFT without finite orbits is not LRF, so its crossed product has
no combinatorial matricial model.
- A genuine action on a finite set `ε`-following the shift on `B_r` yields periodic configurations. The coordinates
  read along the finite orbit agree, up to `ε`, with legal patterns of radius `r`.
- The SFT then has a periodic point, which contradicts `sfts-without-finite-orbits-are-not-residually-finite-actions`.
  That argument does not use density.
- In particular Labbé's `Ω_U` has no combinatorial model. By
  `matricial-z2-sft-crossed-products-give-quantum-tilings`, any matricial model is a noncommuting periodic quantum
  tiling, and neither Theorem 1 nor Ma's Theorem C applies.

**Open (recorded as a claim).** Does some minimal topologically free action have a matricial model but no
combinatorial one, and does that separate the approximation type of `[[α]]` from that of `EL_n(R)`? The Labbé ring is
the test case.
