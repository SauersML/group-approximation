# Referee report (citation/hypothesis lens): `lifts-add-no-unipotent-divisibility`

Referee: lane gq-referee-b, 2026-09-17. Reviewed: the claim and `lifts-add-no-unipotent-divisibility-proof`, as
landed at 970b120c7, and the root edit made in the same commit.

## Verdict

**PASS.** No amendment is required. The node may drop "Not independently reviewed" and cite this report.

## Checks

- **Step 1, the transfer lemma. Correct.**
  - `D ∩ N = D ∩ M = 1`, so `π|_D` is injective.
  - `π(H) ∩ K/N ⊆ Z(π(H))`, because `K/N` is central.
  - With (ii) this gives `π(D) ∩ K/N = 1`. Hence `D ∩ K ⊆ D ∩ N = 1`, and `D` embeds in `E/K`.
- **Step 2, (a)–(g). Each case checked. Correct.** The explicit commutators:
  - (b): `diag(2,1/2,…) u(t) diag(2,1/2,…)^{-1} = u(4t)`, so `[u(q),x] = u(−3q)`.
  - (c): `[u(q), diag(2,1,…)] = u(−q)`.
  - (f): `d·λu(t)·d^{-1}·(λu(t))^{-1} = u(t)`; the centralizer of `u(Q)` in `B_2(Q)` is `{λu(t)}`.
  - (g): `[g,h] = x_13(a(g)c(h) − a(h)c(g))`.
  - The eigenvalue argument in (c): a conjugate of a unipotent equals `λe` only if `λ = 1`.
  - Normality of `D` is used in (e) and (f), and it holds: translations in `Aff(Q)`, and the unipotent radical
    in `B_2(Q)`.
- **Classical inputs.** These are textbook facts; I did not read Artin's book. Neither is load-bearing in
  an unusual way.
  - `PSL_n(Q)` is simple and `SL_n(Q)` is perfect for `n >= 2` (`|Q| > 3`). E. Artin, *Geometric Algebra*,
    Ch. IV, Theorems 4.4 and 4.9.
- **Survey citations, checked against the survey LaTeX in context.**
  - Theorem 4.4 (Higman) reads: "In particular, $\Q$ does not embed into $V$". The numbering is correct under
    the shared `[section]` counter.
  - §4.1: "Since $F$ and $T$ both embed into $V$".
  - Definition of `T̄`: "f lies in T̄ if there exists an element g∈T so that p∘f = g∘p". So `T̄` is the group of
    all lifts, and `T̄/Z ≅ T`.
- **Special cases. Correct.**
  - Lifts of the identity are the integer translations, central in `Homeo_Z(R)`.
  - Covering case: needs `Δ ≤ E` normal and `Δ` the full deck group, so that `E/Δ` is the induced group on the
    base. The node's wording "normal in a group `E`" implies this.
- **Scope statements are accurate.**
  - Deck groups containing `Q`, for example the adelic solenoid, are correctly excluded.
  - The consistency remark for `H = (Q,+)` is right.
  - The root's Attempts entry 1 matches the claim.

## Remark (not an amendment)

The "independent of O4" remark is correct. This claim does not use Burillo–Felipe, so the unreferenced O4
citation, arXiv:2605.09763v1, does not affect it.
