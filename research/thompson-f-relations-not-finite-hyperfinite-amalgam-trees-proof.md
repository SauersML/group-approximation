---
rg: 2
id: thompson-f-relations-not-finite-hyperfinite-amalgam-trees-proof
kind: route
title: Chifan--Houdayer intertwining for amalgams over amenable subalgebras consumes one commuting non-amenable factor per level, while Thompson's F supplies infinitely many
target: thompson-f-relations-not-finite-hyperfinite-amalgam-trees
requires: []
---

**Imports (trust surface).**
- **(CH)** I. Chifan and C. Houdayer, *Bass--Serre rigidity results in von Neumann algebras*, Duke Math.
  J. 153 (2010), arXiv:0805.1566, the general intertwining theorem of §4 (label `kurosh` in the arXiv TeX source, checked there).
  - *Setting.* `N = N_1 *_B N_2` is a semifinite amalgamated free product with `B` amenable. `q ∈ N` is
    a nonzero projection of finite trace, and `Q ⊂ qNq` is a von Neumann subalgebra with no amenable
    direct summand.
  - *Conclusion.* `Q' ∩ qNq ≺_N N_i` for some `i ∈ {1,2}`.
  - The finite case is the one stated in the introduction (Theorem `subalgebra`).
  - *Robustness of the orientation.* Only `D ≺_N N_i` is used below, for `D ⊆ Q' ∩ qNq` with `Q`
    commuting with `D`. If the import is instead read in the dual form (non-amenable relative
    commutant forces intertwining of the algebra), apply it to `D`. `D' ∩ qNq ⊇ P_0`, and for a central
    projection `z` of `D' ∩ qNq`, `P_0 z` is a nonzero image of `P_0`, not amenable by Lemma 1. So
    `D' ∩ qNq` has no amenable direct summand by (Amen), and the same conclusion `D ≺_N N_i` follows.
- **(Po)** Popa's intertwining theorem.
  - Let `A ⊂ qNq` and `C ⊂ N` be finite. Then `A ≺_N C` if and only if no net `u_k ∈ U(A)` satisfies
    `‖E_C(x u_k y)‖_2 → 0` for all `x, y ∈ N`.
  - In that case there exist `n ≥ 1`, a nonzero projection `p ∈ M_n(C)`, a normal unital `*`-homomorphism
    `θ : A → pM_n(C)p`, and a nonzero partial isometry `v ∈ M_(1,n)(qN)p` with `a v = v θ(a)` for all
    `a ∈ A`.
- **(Amp)** `M_n(N_1 *_B N_2) = M_n(N_1) *_(M_n(B)) M_n(N_2)`, with the trace `Tr_n ⊗ τ`. This is
  standard. Freeness with amalgamation over `M_n(B)` is checked entrywise, since the conditional
  expectation is `id ⊗ E_B`.
- **(Amen)** Two facts about finite von Neumann algebras.
  - A von Neumann subalgebra of an amenable finite von Neumann algebra is amenable, because it is the
    image of a trace-preserving conditional expectation.
  - `M_n` of an amenable algebra is amenable. `L(Γ)` is amenable if and only if `Γ` is amenable
    (Connes). `L(R)` is amenable for hyperfinite `R`.
- **(CFP)** For disjoint dyadic intervals `I, J ⊂ (0,1)`, `F_I` and `F_J` commute, `F_I ≅ F`, and
  `F_(I_1) × ⋯ × F_(I_k) ≤ F` is ICC.

## Lemma 1 (surviving summands)

*Let `θ : P → pMp` be a normal `*`-homomorphism with `θ(1) = p ≠ 0`, where `P` has no amenable direct
summand. Then `θ(P)` has no amenable direct summand. If `P` is a factor, `θ` is injective.*

`ker θ` is a weak-`*` closed two-sided ideal, so `ker θ = P(1-z)` for a central projection `z ∈ Z(P)`.
Then `θ(P) ≅ Pz`, and `z ≠ 0` since `θ(z) = θ(1) ≠ 0`.
- A direct summand of `Pz` is a direct summand of `P`, so it is not amenable.
- If `P` is a factor, `z = 1`.

## Lemma 2 (intertwining passes to unital subalgebras)

*If `A ⊂ qNq`, `D ⊂ A` is a unital subalgebra and `A ≺_N C`, then `D ≺_N C`.*

`U(D) ⊆ U(A)`, so a net of unitaries in `D` witnessing `D ⊀ C` would witness `A ⊀ C` by (Po).

## Proof of Theorem item 1 (depth bound)

We show by induction on `d` that for `N ∈ 𝒜_d`, `κ(N) ≤ d`. By (Amp) and (Amen), `𝒜_d` is closed under
`M_n(·)`: induct through the amalgam.

**Base case, `d = 0`.** Every unital subalgebra of the amenable corner `qNq` is amenable by (Amen), so
`κ = 0`.

**Inductive step.**
- *Setup.* Let `N = N_1 *_B N_2 ∈ 𝒜_(d+1)`. Suppose `P_0, …, P_(d+1) ⊂ qNq` pairwise commute and have no
  amenable direct summand.
- *Intertwining.* Let `Q = P_0` and `D = P_1 ∨ ⋯ ∨ P_(d+1) ⊆ Q' ∩ qNq`, a unital subalgebra.
  - By (CH), `Q' ∩ qNq ≺_N N_i` for some `i`, and by Lemma 2, `D ≺_N N_i`.
  - By (Po) there is a normal unital `θ : D → pM_n(N_i)p` with `p ≠ 0`.
- *Surviving algebras.* The algebras `θ(P_1), …, θ(P_(d+1))` pairwise commute, and they are unital in
  `pM_n(N_i)p`, since `θ(1) = p`.
  - Each `θ|P_j` is normal with `θ(1_(P_j)) = θ(q) = p ≠ 0`. By Lemma 1, none of them has an amenable
    direct summand.
- *Contradiction.* `M_n(N_i) ∈ 𝒜_d`, so this is `d+1` commuting algebras in a corner of an `𝒜_d` algebra,
  contradicting the induction hypothesis. Hence `κ(N) ≤ d+1`. ∎

## Proof of item 2

- Suppose `F` is not amenable. Choose disjoint dyadic intervals `I_1, …, I_k`.
  - By (CFP) the factors `L(F_(I_j))` pairwise commute, and each is non-amenable by (Amen). They are
    factors because `F` is ICC.
  - So `κ(L(F)) ≥ k` for every `k`.
- If `L(F) ⊆ M` unitally, the same algebras witness `κ(M) = ∞`. So by item 1, `M ∉ 𝒜_d` for every `d`.

## Proof of item 3

**Lemma 3 (relation amalgams give algebra amalgams).** *If `R = R_1 *_(R_0) R_2`, then
`L(R) = L(R_1) *_(L(R_0)) L(R_2)`.*

We use Gaboriau's definition (Invent. Math. 139 (2000), §IV). `R_0 ⊆ R_1 ∩ R_2`, `R` is generated by
`R_1 ∪ R_2`, and for a.e. `x_0` the following holds. For every chain `x_0, …, x_n` (`n ≥ 1`) with
`(x_(k-1), x_k) ∈ R_(i_k) ∖ R_0` and `i_k ≠ i_(k+1)`, we have `(x_0, x_n) ∉ R_0`.

- **Generation.** `L(R_1)` and `L(R_2)` generate `L(R)`, because `[[R]]` is generated by
  `[[R_1]] ∪ [[R_2]]` under composition and countable disjoint gluing.
- **Conditional expectation.** The trace-preserving expectation onto `L(R_0)` restricts the matrix
  function to `R_0`. By Kaplansky density, `L(R_i) ⊖ L(R_0)` is the `‖·‖_2`-closure, within the operator
  norm ball, of finite sums `Σ f_φ u_φ` with `graph φ ⊆ R_(i) ∖ R_0`.
- **Freeness.** An alternating product of such elements is a sum of `f u_ψ` where `ψ` is a composite
  along such chains, so `graph ψ ∩ R_0 = ∅` by the freeness condition. Its expectation onto `L(R_0)` is
  therefore `0`.
  - The product is jointly `‖·‖_2`-continuous on norm-bounded sets, which passes this to the closure.
- **Conclusion.** The trace on the algebra generated by the pieces is thus determined by the traces on
  the pieces and freeness with amalgamation. That is the defining property of `L(R_1) *_(L(R_0)) L(R_2)`.

(For `R_0` the diagonal, this is Gaboriau's and Popa's identification of free products of relations.)

**Proof of item 3.**
- By Lemma 3 and (Amen), `R ∈ ℛ_d` implies `L(R) ∈ 𝒜_d`.
- A free pmp orbit relation of `F` has `L(R) = L^∞(X) ⋊ F ⊇ L(F)`.
  - If `F` is not amenable, item 2 gives `L(R) ∉ ∪_d 𝒜_d`, so `R ∉ ∪_d ℛ_d`.
  - If `F` is amenable, `R` is hyperfinite (Ornstein--Weiss, Connes--Feldman--Weiss), so `R ∈ ℛ_0`.
- **Treeable case.** A treeing by finitely many partial isomorphisms `φ_1, …, φ_m` exhibits `R` as
  `R_(φ_1) * ⋯ * R_(φ_m)`, amalgamated over the diagonal. Each `R_(φ_j)` is generated by one partial
  isomorphism and is hyperfinite, so `R ∈ ℛ_(m-1)`.

## Proof of item 4

- *Setup.* Let `R_F = R_1 *_(R_0) R_2` with `R_0` hyperfinite, and `M = L(R_F) = L(R_1) *_(L(R_0)) L(R_2)`
  by Lemma 3.
- *Intertwining.* Take disjoint dyadic intervals `I_0, I_1, …, I_k`, `Q = L(F_(I_0))` (a non-amenable
  factor), and `D = L(F_(I_1) × ⋯ × F_(I_k)) ⊆ Q' ∩ M`.
  - (CH) and Lemma 2 give `D ≺_M L(R_i)`.
  - (Po) gives a normal unital `θ : D → pM_n(L(R_i))p` with `a v = v θ(a)`.
- *Injectivity.* `D ≅ L(F^k)` is a factor by (CFP), so `θ` is injective by Lemma 1.
- *Choice of piece.* The index `i` may depend on `k`. `L(F^k)` embeds unitally in `L(F^(k+1))`, so a
  piece that works for infinitely many `k` works for all `k`. ∎

## Calibration and where it stops

- **Solid-type examples.**
  - `L(F_2 × Z) ∈ 𝒜_1`, and its commuting depth is `1`. `L(F_2) ⊗ L(Z)` has one non-amenable tensor
    factor.
  - For `L(F_2) ⊗ L(F_2)`, item 1 excludes `𝒜_1` and says nothing about `𝒜_2`. The theorem never
    asserts more than the counting allows.
- **Unions.** The proof uses a *finite* induction. For an increasing union `R = ∪_k R^(k)` with
  `R^(k) ∈ ℛ_(d_k)` and `d_k → ∞`, nothing is excluded. Intertwining into `L(R^(k))` is not implied by
  containment in the union. This is the measured analogue of the metric step where
  `thompson-f-lies-in-algebraic-lea-closure-only-if-amenable` stops.
- **Products.** `R_1 × R_2` gives `L(R_1) ⊗ L(R_2)`. `L(F)` is McDuff (Jolissaint), so no tensor
  primality obstructs product decompositions.
- **Not a soficity obstruction.** `⊕_N F_2` is sofic and has `κ = ∞`. Item 1 is about the depth of the
  mechanism only.
