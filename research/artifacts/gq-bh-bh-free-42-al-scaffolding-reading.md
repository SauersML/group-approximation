# Amir–Lazarovich scaffolding data, and Radu's normal-closure device: reading record (09-18)

Lane bh-free-42. Companion to `research/artifacts/gq-bh-bh-free-extensions-cd3-sources.md`, which
records AL's Theorem A, Prop. "the lattice Lambda" and the Discussion. This file records the
interlacing data those nodes do not quote. It also records one misprint in AL's explicit scaffolding
and Radu's device for computing finite residuals.

- **Sources.** AL = M. Amir, N. Lazarovich, arXiv:2605.09493. Radu = N. Radu, "New simple lattices in
  products of trees and their projections" (appendix by P.-E. Caprace), arXiv:1712.01091v1.
- **Where the files are.** Both are arXiv e-prints on MSI:
  - AL: `/projects/standard/hsiehph/sauer354/gqsrc/bh-free-42/al/main.tex`. Its md5 equals that of
    `/scratch.global/sauer354/bhfe/al/main.tex`, so line numbers agree with the companion artifact.
  - Radu: `/projects/standard/hsiehph/sauer354/gqsrc/bh-free-42/radu/Lattices3ALL.tex`.
- Statements are paraphrased, with short phrases quoted.

## A. AL's interlacing pair built from an involutive BMW group (AL §5.3, l.1988–2285)

- **Input.** An involutive BMW group `Γ = ⟨x_1..x_m, a_1..a_n | R⟩` with alternating local actions.
  Also an n-scaffolding (l.1996–2010) with the following data:
  - **(E1)** `k, d` with `max{n+1, 6} <= d`;
  - **(E2)** a vertex `A'` of `O_d` and `n+1` of its neighbours `𝒜' = {A_1, …, A_n, B}`;
  - **(E3), l.2006.** Even involutions `υ_1, …, υ_k` that generate `Alt_{2d−1}`, with
    `supp(υ_1) ⊆ B`.
  - **(E4), l.2007.** A set `𝒞 = {C_1, …, C_k}` such that `𝒜' ∪ 𝒞` is independent in `O_d`, and
    `supp(υ_i) ∪ … ∪ supp(υ_{i+3}) ⊆ C_i` (indices mod k).
- **Index sets.** `Z = 𝒳 ⊔ 𝒴`, with `𝒳 = {x_1..x_m}` and `𝒴 = {y_1..y_k}`, so `c = m + k`.
- **The pair (l.2101).**
  - `ζ_{x_i} = ξ_i` is the local action of `x_i` on `[n]`, transported to `[2d−1]` by `j ↦ j̄`,
    the odd-one-out of the edge `{A', A_j}`. `ζ_{y_i} = υ_i`.
  - `δ_{A_j} = α_j` is the local action of `a_j` on `𝒳`, "extended by the identity on `𝒴`" (l.2160).
  - `δ_B = β = (x_1 y_1)(x_2 x_3)` (l.2165).
  - `δ_{C_i} = γ_i = (y_i y_{i+1})(y_{i+2} y_{i+3})`, indices mod k (l.2169).
  - `δ_D = id` for every other D.
  - **Consequence used in `amir-lazarovich-simple-lattice-has-torsion-iff-index-four`.** `δ_D` moves an
    element of `𝒴` only in two cases: `D = B`, where it moves only `y_1`; and `D = C_i`, where it moves
    only `y_i, …, y_{i+3}`.
- **Proof of (D4) for `D = C_i` (l.2232–2235).** It cites (E4) for `supp(ζ_{y_j}) ⊆ C_i`,
  `i <= j <= i+3`.
- **Claim "the local actions of Λ" (l.2295).** `⟨δ_D⟩ = Alt(Z)` and `⟨ζ_z⟩ = Alt_{2d−1}`.

## B. The explicit scaffolding violates (E4) when d <= 8

- **AL's explicit choice (Lemma "existence of scaffoldings", l.2011–2032).**
  - `d = max{n+1, 6}` and `k = 2d−1` (l.2017).
  - `υ_i = (i, i+1)(i+2, i+3)` mod `2d−1` (l.2023).
  - `C_i = C_i' ∪ {1 or d}`, where `C_i' = {i, …, i+d−3}` has `d−2` elements (l.2024).
- **Where it fails.** `supp(υ_i) ∪ … ∪ supp(υ_{i+3}) = {i, …, i+6}` has 7 elements. `C_i` is a
  window of `d−2` consecutive points plus one point.
  - So (E4) forces `d − 2 >= 7`, or `d − 2 = 6` with the added point equal to `i+6`.
  - The added point is 1 or d, so for `d <= 8` (E4) fails for most i.
- **(E4) is really needed.** (D4) at `D = C_i`, `z = y_i`, `z' = γ_i(y_i) = y_{i+1}` asks `υ_i` and
  `υ_{i+1}` to agree off `C_i`. They disagree exactly on `{i, …, i+4}`, and the pair
  `(y_{i+2}, y_{i+3})` gives `{i+2, …, i+6}`. So any interlacing pair with these `υ`'s and `γ`'s needs
  `C_i ⊇ {i, …, i+6}`.
- **Effect.** For `n <= 7` (so `d <= 8`) the lemma "from involutive to interlacing" does not apply to
  the printed data.
  - Theorem A ("for infinitely many c, d") is unaffected: take `n >= 8`, or replace 6 by 9 in the
    choice of d. Then `C_i'` has `>= 7` consecutive points, and `1 ∈ C_i` for every i keeps `𝒞`
    pairwise intersecting.
  - I did not recheck the remaining independence conditions for `d >= 9`.
- **Smallest instance.** Any AL instance with these `υ`'s has `d >= 9`, so
  `|V(O_d)| >= C(17, 8) = 24310`. This bears on the finite-quotient search proposed by
  bh-free-extensions for `d = 7`.

## C. Radu's normal-closure device (Radu §5.1, l.2218 and l.2276)

- **Commutator lemma (l.2218).** Radu cites Caprace's note for the fact that
  `[C_G(H), cl(H)] ⊆ G^(∞)` for every subgroup H. Here `cl(H)` is the profinite closure.
  - He uses it to find an explicit element `r ≠ 1` of `Γ_{4,4}^(∞)`.
- **Computing the index (l.2276).** Radu uses `r` to compute `[Γ : Γ^(∞)]`.
  - Radu: "the kernel of the projection `Γ_{6,6,k} → Q` is the smallest normal subgroup … containing"
    `r`, where Q is `Γ_{6,6,k}` with `r` added as a relator. So `Q = Γ/Γ^(∞)`, and a coset
    enumeration gives `|Q|`.
  - The reason: `Γ` is just-infinite and `r ∈ Γ^(∞)`.
- **Outcome for his 160 (6,6)-groups (l.252, l.2276, l.2292).**
  - 158 have `|Q| = 4`, so the simple subgroup is `Γ^+`, of index 4.
  - Two have `Q ≅ (Z/2)^2 × Z/3`, so the simple subgroup has index 3 in `Γ^+`.
  - His (4,5)-groups: 48 have index 4 and 12 have index 8.
- **These are not AL inputs.** They contain the torsion-free `Γ_{4,4}`, so they are not involutive.
  They are the only published data on how often the index is exactly 4.
