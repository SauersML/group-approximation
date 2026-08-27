---
rg: 2
id: atlas-steinberg-spare-index-independence
kind: claim
title: Spare-index independence holds at every monomial length — the presented group is Steinberg
distinct_from:
  atlas-steinberg-transfer-identity: that is the bare group identity the induction consumes, its hypotheses supplied one length down; this is the theorem about the presented group G₀ — all chains agree, splits agree, the derived commutations hold — proved by a joint induction whose acyclicity was the entire difficulty.
  atlas-steinberg-rank-five-translation: that is the usable-list program; this is the lemma it blocked on, now proved, together with the involutivity finding that completes the additive side.
artifacts:
  - research/artifacts/steinberg-spare-index-2026-08-15.md
  - research/artifacts/atlas-completeness-derivation-2026-08-15.md
---

Let `G₀` be the group presented by generators `X_ij(a)`, `a ∈ A =
{1, e, f, e^*, f^*}`, `1 ≤ i ≠ j ≤ 5`, subject to the full (St2)/(St3)
instantiation on `A` (all 25 coefficient pairs, all root pairs under the
genuine side condition, all three intermediate indices equated to one
canonical right-hand side), the abelian-root relations, and the five
context-free Cuntz–Krieger relations.

**Theorem.**  For every monomial `w` in `A` and every root `(i,j)`, all
legal spare-index chains defining `Ê_ij(w)` agree ("(P)"), every split
satisfies `Ê_ij(uv) = [Ê_im(u), Ê_mj(v)]` for every `m ∉ {i,j}` ("(R)"),
and the (St2)-pattern commutations hold for the derived objects
(`[Ê_ij(w), Ê_kl(w')] = 1` whenever `j ≠ k, l ≠ i` — "(Q′)").  In
particular Lemma X — the spare-`l` object commutes with its own factors
— holds at every length.

**Consequently**, adding the involutivity relators `X_ij(a)² = 1`
(which the abstract family provably does not force — see the involutivity
finding below — but which hold in every evaluation over an
`F₂`-algebra), the assignment `Ê` extends additively to all of `L`, is
well defined by context absorption plus involutivity, satisfies
(St1)–(St3), and inverts the evident map: **`G₀ ≅ St₅(L)`**.

**Proof shape** (complete proof in the artifacts; adversarially verified
with every critical step re-derived by hand): a joint induction on
length carrying `(P_t) < (R_t) < (Q_t) < (Q′_t)` in that order within
each stage.  `(P_t)` uses the corrected transfer identity
(`atlas-steinberg-transfer-identity`) whose five hypothesis instances
sit at lengths `≤ t−1` — verified edge by edge, so the dependency graph
is acyclic and the old stall (an artifact of the identity's earlier
over-strong hypotheses) never arises.  The three-index shuffle in
`(P_t)` — `Ê^{(k)} = V_m` for every spare `m ≠ k`, forcing all three
chains equal — is one of FOUR places consuming the third spare index,
so this is an `n ≥ 5` proof; it does not reprove [KrM, Theorem 3] at
rank four.

**The involutivity finding.**  Additivity needs `Ê_ij(w)² = 1`, and the
abstract emitted family cannot derive it: over the Leavitt path algebra
`L_ℤ(1,2)` of the rose with two petals over `ℤ` (free as a ℤ-module by
Tomforde, so `2·1 ≠ 0`), every emitted relation holds — including the
five lifted Cuntz–Krieger relators, all emitted with explicit inverses
and hence sign-correct over `ℤ`, a check the verification supplied —
while `X_ij(1)² ↦ E_ij(2) ≠ 1`.  Scope: this shows non-DERIVABILITY
from the abstract family; whether the squares happen to lie in the atlas
quotient's normal closure is not decided and not needed — the repair is
to emit, not adjudicate.  The 100 squares reduce to 24 genuinely new
relators in the atlas realisation (12 are freely trivial — chart
transvections are involutions — and 64 coincide with emitted cross-root
words, an atlas-realisation phenomenon distinct from the abstract
independence; this breakdown is the emission engineer's exact
computation, block-matched against rebuilt reduced words, and postdates
the adversarial pass on the proof), all verified in `R̄`; and the
length-one relators
propagate to all lengths: `(Q′)` makes `δ = Ê_ij(uv)` central in
`⟨Ê_im(u), Ê_mj(v)⟩`, and `[Ê_im(u)², Ê_mj(v)] = δ²` closes the
induction.
