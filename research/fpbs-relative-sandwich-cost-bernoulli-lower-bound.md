---
rg: 2
id: fpbs-relative-sandwich-cost-bernoulli-lower-bound
kind: claim
title: For finitely generated groups the Bernoulli shift minimizes every relative sandwich cost among free actions
distinct_from:
  fpbs-free-action-cost-at-least-bernoulli-cost: that is the case where F generates Delta, so the sandwich cost is the cost C(a) and the statement is fixed price for finitely generated groups; this asks the same inequality for every finite F, including F generating a proper subgroup, and so implies that one.
  fpbs-countable-groups-have-fixed-pseudocost: that is fixed pseudocost for all countable groups; this is a statement about finitely generated groups only, and implies that one through fpbs-fixed-pseudocost-from-relative-sandwich-bound.
artifacts:
  - research/artifacts/fpbs-sandwich-cost-quantifier-shift-2026-09-17.md
---

**OPEN.** For a countable group `Δ`, a p.m.p. action `a` of `Δ` and a finite
`F ⊆ Δ`, let

    p^Δ_F(a) = inf { C(E) : E_{a|⟨F⟩} ⊆ E ⊆ E_a }.

Let `s_Δ` be the Bernoulli shift `[0,1]^Δ`. Prove: for every finitely
generated group `Δ`, every finite `F ⊆ Δ` and every free p.m.p. action `a` of
`Δ`,

    p^Δ_F(s_Δ) ≤ p^Δ_F(a).

**Why it matters.**
- **Case `F` generates `Δ`.** Then `p^Δ_F = C`, and the statement is
  `fpbs-free-action-cost-at-least-bernoulli-cost`. With Abért–Weiss
  maximality, that is fixed price for finitely generated groups.
- **All `F`.** The statement gives fixed pseudocost for every countably
  infinite group (`fpbs-fixed-pseudocost-from-relative-sandwich-bound`). That
  excludes shape (A) of Theorem G of the passage artifact everywhere, using
  only finitely generated groups.

**Reverse inequality.** For infinite `Δ`, the reverse inequality
`p^Δ_F(a) ≤ p^Δ_F(s_Δ)` follows from Abért–Weiss and Tucker-Drob's openness
theorem (artifact Proposition 2.5, not a graph node). So the statement is
equivalent to: `p^Δ_F` is constant on free actions of `Δ`.

**Known cases** (artifact §3, remarks):
- finite `Δ`;
- amenable `Δ`, where the infimum is attained at `E_{a|⟨F⟩}` and depends only
  on `|⟨F⟩|`.

**First test.** `Δ = F_2`, with `F` generating a free subgroup of infinite
index and rank at least 2. All sandwich relations are treeable.

**Open question.** Does fixed price for all countable groups imply this
statement?

## Attempts

**Openness plus weak containment (September 17, 2026, b-t-nonamgen).**
- Tried: use that `A_{F,r}` is open in the weak topology at free actions
  (`tucker-drob-sandwich-sets-open-at-free-actions`) and that `s_Δ` is weakly
  contained in every free `a` (Abért–Weiss).
- Where it dies: openness of `{p_F < r}` makes `p_F` upper semicontinuous.
  Every free `a` has `s_Δ` in the closure of its conjugacy class, so the argument
  moves small sandwich cost from `s_Δ` to `a`. That gives only the reverse
  inequality `p^Δ_F(a) ≤ p^Δ_F(s_Δ)`. No lower semicontinuity of `p_F` is known,
  and at `F` generating `Δ` it would be fixed price for `Δ`.
- Deferred: the `F_2` test above. There every sandwich relation is treeable,
  but a treeable `E` with `E_{a|⟨F⟩} ⊆ E ⊆ E_a` has no generating free action
  to which Gaboriau's fixed price applies. So the test needs a direct cost
  computation for intermediate treeable relations, which was not attempted.

**Fiber trick / virtual rank drop (September 17, 2026, w11-fp-break,
census-computation).**
- Tried: build free actions of `F_2` with small sandwich cost as products
  `b × F_2/N`, with `KN = F_2`, and look for a drop in the least rank of
  subgroups between `K∩N` and `N`.
- Proved (`fpbs-sandwich-cost-fiber-formula`): an exact fiber formula,
  `p_K(b × Δ/N) = 1 + (p^N_{K∩N}(b|N) − 1)/d`. So RBL predicts
  finite-index multiplicativity of Bernoulli sandwich cost minus one, given
  the reverse inequality.
- Where it dies: Theorem 4(iii) of the artifact. `K ∩ M' = K ∩ N` for every
  `K∩N ≤ M' ≤ N`. So by strong inertness, the trivial double coset alone
  forces `rk M' ≥ 1 + d`. Every virtually group-generated sandwich
  therefore costs `≥ 2`, which equals `C(E_a)`, in every free action.
  Invariant: reduced rank. A census found no drop in `F_2` (confirming the
  theorem) or in `F_3` with `rmin(K) = 3`.
- Reduction: the `F_2` slice of RBL follows from
  `fpbs-free-group-sandwich-cost-is-two` (every sandwich costs `≥ 2`). That
  is a measured Hanna Neumann statement. Its naive measured form is false
  (artifact §5 example). Equivariant copies inside `E_a` are identities
  (artifact Lemma 5). So a counterexample needs a twisted, non-group
  sandwich.

**All finitely generated free groups: exact value via the L2-closure rank
(September 19, 2026, swarm-0917-w18-w18-fp-break, group-rings).**
- Proved (`fpbs-free-group-sandwich-cost-is-minimal-overgroup-rank`,
  ESTABLISHED): for free `Δ` of finite rank, every finite `F` and every free
  `a`, `p^Δ_F(a) = π̄(⟨F⟩ ≤ Δ) = min{rk L : ⟨F⟩ ≤ L ≤ Δ}`. The minimum is
  attained by `E_{a|L}`. So RBL holds for every finitely generated free
  group, including non-compressed `⟨F⟩`, for example the index-2 subgroup
  `⟨x, yxy^{-1}, y^2⟩` of `⟨x, y⟩ ≤ F_3`, with value `2 < 3 = rk`.
- Input: the Fox-rank bound `C(E) ≥ rk(A)` of
  `fpbs-sandwich-cost-fox-rank-lower-bound`, together with Jaikin-Zapirain's
  Theorem 3.12 (arXiv:2403.09515v2), imported as
  `free-group-minimal-overgroup-rank-is-fox-rank`. That theorem gives
  `rk(A) = π̄` for every finitely generated `H`, not only compressed `H`.
- Where it stops (the invariant): the Fox cocycle needs a derivation
  `δ: Δ → (ZΔ)^q` with `δ(f_k) = e_k`. Such a `δ` makes `I_Δ` free on the
  `f_k − 1`, so `Δ` is free. Every non-free `Δ` is outside this method. The
  remaining RBL is for non-free `Δ`, where no action-independent formula for
  `p_F` is known. A natural next case is surface groups. There an L2
  analogue of compressed-implies-independent is known from Antolín and
  Jaikin-Zapirain (not imported, not checked here), but the Fox cocycle on
  `[[E_a]]` has no analogue.

**Free-group slice closed; complementary split (September 19, 2026,
w18c-fp-alt, group-rings).**
- **Proved** (`fpbs-free-group-sandwich-cost-is-minimal-overgroup-rank`).
  For `Δ = F_q` of finite rank, every finite `F` and every free action `a`:
  `p^Δ_F(a) = min{rk L : ⟨F⟩ ≤ L ≤ Δ}`.
  - The lower bound is the Fox rank bound `C(E) ≥ rk_{N(F)}(A)`.
  - The rank `rk_{N(F)}(A)` is identified with the least overgroup rank for
    every `H`, compressed or not. This uses Jaikin-Zapirain's Theorem `pibar`
    (`jaikin-zapirain-minimal-overgroup-rank-formula`, arXiv:2403.09515,
    quoted verbatim), which gives
    `π̄(H ≤ F) = rk F − β_0^{Q[F]}(I_{Q[F]}/^F I_{Q[H]})`.
  - The upper bound is the subgroup treeing of a minimal-rank overgroup.
  - So the "First test" above, and the whole free ambient slice, hold with
    an action-independent value.
- **New decomposition** (route
  `fpbs-rsb-from-bernoulli-cost-and-subgroup-attainment`).
  RSB follows from three inputs:
  - `fpbs-free-action-cost-at-least-bernoulli-cost` (the H core);
  - Abért–Weiss (`fpbs-bernoulli-maximal-cost`);
  - a new OPEN claim `fpbs-sandwich-cost-attained-by-subgroup-relations`
    (SAS): `p^Δ_F(a) ≥ inf{C(a|Δ') : Δ' fg, ⟨F⟩ ≤ Δ' ≤ Δ}` in each single
    action.

  SAS is vacuous at `⟨F⟩ = Δ`, and H is exactly that case. So the two open
  inputs are complementary. SAS makes no comparison between actions. SAS
  alone gives `PC = σ` (passage artifact, Proposition A) for all free
  actions of all countable groups.
- **Partial answer to the open question above.** Fixed price for all
  finitely generated groups implies RSB modulo SAS. It is still unknown
  whether it implies SAS.
- **Where it stops.** SAS beyond free groups. The first open test is a
  surface group with `F` generating a rank-2 free subgroup of infinite index,
  where `q = 2`. The free-group argument needs two ingredients there:
  - a Fox-type `L²` bound for sandwiches inside a one-relator group;
  - `L²`-subgroup rigidity of surface groups. Jaikin-Zapirain conjectures
    this for all locally indicable groups.
