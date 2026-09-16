---
rg: 2
id: thompson-v-amenable-actions-free-off-fixed-points-proof
kind: route
title: Elek–Szabó plus simplicity give the reduction, character rigidity makes the stabilizer IRS trivial, and the halving obstruction absorbs every stabilizer that fixes a measure or a rigid cover
target: thompson-v-amenable-actions-are-free-off-fixed-points
requires:
  - thompson-v-finitely-presented-infinite-simple
  - thompson-v-character-simplex
  - elek-szabo-essentially-free-amenable-actions
artifacts:
  - research/artifacts/thompson-v-amenable-actions-2026-09-16.md
  - research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md
---

Notation as in the claim. The full proofs are in
`research/artifacts/thompson-v-amenable-actions-2026-09-16.md`, Sections 1–6. Below are the key steps.

**Halving (H).** There is no `V`-invariant finitely additive probability `µ` on clopen sets.
- The tables `{0,10,11} → {00,01,1}` and `{0,10,11} → {01,00,1}` map `[0]` onto `[00]` and onto `[01]`.
  So `µ[0] = 2µ[0]`, hence `µ[0] = 0`.
- The swap of `[0]` and `[1]` gives `µ[1] = 0`, so `µ(C) = 0`, a contradiction.

**Transitivity (Tr).** `V` is transitive on proper nonempty clopen sets. Split cones until the two sets
and their complements have matching cone counts, then match the prefix codes.

**Item 1** (artifact §1).
- **(a ⇒ d).** `m(Ω \ Fix V) ≤ Σ_s m(Ω \ Fix s)`, so some `s ∉ N_(V,Ω,m) ⊇ N_V`.
- **(d ⇒ b).** `N_V` is normal and `V` is simple, so `N_V = 1`. Apply Proposition 5.1(2).
- **(b ⇒ a).** `Fix V ⊆ Fix s` is null, so restrict to its complement.
- **(b ⇒ c).** Take Theorem 3 (1 ⇒ 3) of Elek–Szabó with `K = S` and `ε < 1/2`. Remove `Fix V` from the
  Følner set, which costs at most an `ε` fraction because `Fix V ⊆ Fix s`. Then pick the best `V`-orbit:
  it is `V/H` with `H` proper and ratio `< 2|S|ε`.
- **(c ⇒ a).** Take a weak*-limit of uniform averages on almost-invariant `P_n ⊆ V/H_n`, placed in
  `⊔_n V/H_n`.
- **Soficity.** `N_V = 1`, so Proposition 5.1(3) gives that `V = V/N_V` is sofic.

**Item 2** (artifact §2).

*IRS rigidity.* `V` has no proper finite-index subgroup, since its normal core would be a proper normal
subgroup of finite index. By `thompson-v-character-simplex`, every IRS `ν` of `V` has
`ν{K : g ∈ K} = b` for `g ≠ e`. This is because `g ↦ ν{K ∋ g}` is a normalized positive-definite class
function, and so equals `b·1 + (1-b)δ_e`.
- Take a symmetric lazy full-support probability `µ` on `V`. For each `K`, `µ^(*n)(K) → 1/[V:K]`, which
  is `1_(K = V)`.
- Averaging over `ν` gives `µ^(*n)(e) + b(1 - µ^(*n)(e)) → b`. Dominated convergence then gives
  `ν{V} = b`.
- Countable additivity over `g ≠ e` gives `ν = (1-b)δ_({e}) + bδ_V`.

This is §§1–3 of `research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md`.

*The mean.*
- `ν_0(E) = m{x : Stab(x) ∈ E}` is a finitely additive probability on the clopen algebra of `Sub(V)`,
  since each clopen set is a finite Boolean combination of the sets `U_g = {K ∋ g}`.
- It is countably additive on that algebra by compactness, so Carathéodory extends it to a conjugation-invariant Borel probability. That is an IRS.
- `{V} = ⋂_(s ∈ S) U_s` is clopen and has mass `m(Fix V)`. So for `g ≠ e`,
  `m(Fix g) = ν_0(U_g) = m(Fix V)`.

**Item 3.** `{x ∉ Fix V : Stab(x) ∩ P ≠ ∅} ⊆ ⋃_(p ∈ P) (Fix p \ Fix V)`, a finite union of null sets. On
`V/H` with `H` proper and confined by `P`, this set is everything.

**Item 4** (artifact §3).
- Let `Ω_0` be the set of `x` whose stabilizer fixes a finitely additive probability `λ` on `𝒜`. It is
  invariant.
- Choose `λ_x` on each orbit by transport from one representative. This is well defined because
  stabilizers fix it, and it satisfies `λ_(gx) = g_*λ_x`.
- If `t = m(Ω_0) > 0`, then `E ↦ t^-1 m(1_(Ω_0)(x) λ_x(E))` is an invariant finitely additive probability
  on `𝒜`, which cannot exist.
- For `𝓜`, take `Y = C` with the clopen algebra and apply (H).

**Item 5** (artifact §4).
- **Setup.** For `x ∉ Fix V` with `O(x) = C`, let `P(x)` be the maximal cones `W` with `V_W ≤ Stab(x)`.
  They form a finite partition of `C` (Lemma 4.1).
- **Shallow cones are null.** Let `S_n` be the set of `x` such that `V_[w] ≤ Stab(x)` for some word `w`
  of length `≤ n`. Then `S_n \ Fix V ⊆ ⋃_(|w| ≤ n) Fix(h_w)`, where `h_w` swaps `[w0]` and `[w1]`. So it is null
  by item 2.
- **Equivariance.** Let `g` have depth `≤ d`, so that it maps cones of length `≥ d` to cones of length
  at most `d` more. Then for `x ∉ S_(2d)`, `gx ∉ S_d` and `P(gx) = gP(x)` (Lemmas 4.2–4.4).
- **Conclusion.** Let `t = m(Ω_𝒞)` and suppose `t > 0`. Then
  `λ(E) = t^-1 m(1_(Ω_𝒞)(x) #{W ∈ P(x) : W ⊆ E}/|P(x)|)` is:
  - finitely additive on unions of length-`n` cones, up to the null `S_n`;
  - invariant up to the null `S_(2d)`.

  This contradicts (H).

**Item 6** (artifact §5). Suppose proper `H_n ≤ K_n` have `φ_S(V/H_n) → 0`, with `K_n` in one family.
- As in (c ⇒ a), `⊔_n V/H_n` carries an invariant mean.
- Push it along `gH_n ↦ gK_n`. All stabilizers of `⊔_n V/K_n` lie in the conjugation-invariant family,
  and none is `V`.
- Items 3–5 make this whole `V`-set null, a contradiction.

**Item 7** (artifact §6).
- `f(U) = m{x : ∅ ≠ K(x) ⊆ U}` is `V`-invariant, so by (Tr) it is a constant `c` on proper nonempty
  clopen sets.
- `{∅ ≠ K ⊆ [00]}` and `{∅ ≠ K ⊆ [01]}` are disjoint inside `{∅ ≠ K ⊆ [0]}`, so `2c ≤ c` and `c = 0`.
- **First consequence.** Apply this to `K(x) = C \ O(x)`. The case `K(x) = ∅` is item 5.
- **Second consequence.** The atoms of the invariant clopen algebra define an equivariant map into
  finite clopen partitions with at least two pieces. The stabilizers of that `V`-set lie in `𝓒`, so
  item 5 makes it null.

**The T remarks.**
- **Not in 𝓜.** A `T`-invariant probability on `C` pushes forward to the circle. There `F` has an
  element `f` with `f(u) > u` on `(0,1)`, which confines any invariant probability to `{0}`, and dyadic
  rotations move `0`.
- **No V_U.** Swapping two adjacent arcs `[w00]` and `[w01]` reverses cyclic order, so it is not in `T`.
- **No finite clopen partition.** Simplicity and minimality would force `T` to fix every piece.
