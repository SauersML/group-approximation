# Referee report (gq-referee-b, citation/hypothesis lens): the Euler ring's rational symbols are infinitely generated

**Reviewed.** `euler-ring-rational-symbols-are-infinitely-generated` and its `-proof` (lane gq-k2-q, 29881297a), read on
origin/main.

**Verdict: PASS.** Every import is used inside its hypotheses, the `D` here is the `D` of the two cited nodes, and I
checked each step. The node correctly refutes `euler-triangular-ring-has-fg-central-unstable-k2`, for every `l` and
every `N ≥ 3`.

Two items are recorded below it:
- the `(T2)` diagnosis;
- a correction to my own report 76fc7667e.

## Imports

- **`abc-twisted-laurent-k-theory-fibration`** (ABC Theorem 3.6 and Lemma 7.2, read at source there). Its hypotheses
  hold:
  - `A = Z[u][π_k^(-1)]` is regular Noetherian of Krull dimension 2, so every `A[t_1..t_p]` is Noetherian of finite
    global dimension, hence regular coherent. That makes `A` regular supercoherent.
  - `σ` is a unital automorphism, since it permutes the `π_k`.
  - The exact segment `K_2A →(1-σ) K_2A → K_2D` then makes `coker(1-σ_*)` inject into `K_2(D)`.
  - The `σ` versus `σ^(-1)` convention is immaterial: `1 - σ^(-1) = -σ^(-1)(1 - σ)`.
- **Dennis–Stein §10(a)(i), p. 252.** Read at source in `gq/src/k2/ds-survey.pdf`, PDF page 12: "(i) The Steinberg
  symbols generate K_2(n,R) for n ≥ 3 if R is a commutative semi-local ring [90, Theorem 2.7]." **Match.**
  - Passing to the limit gives the stable statement for the DVR `Z[u]_𝔭`, which is what the route uses.
- **`infinitely-generated-symbols-block-fp-elementary-groups`.** I refereed it PASS earlier. Its hypotheses are a unital
  ring, `N ≥ 3`, and `Sym(R)` not finitely generated.
  - `Sym(D)` contains a free abelian group of infinite rank, and subgroups of finitely generated abelian groups are
    finitely generated. So `Sym(D)` is not finitely generated.
  - The same holds for `T_l` and `R_l`, through the retractions.
- **Textbook inputs, checked directly rather than at source.**
  - *(TS)* Milnor §11: `∂_v{a,b} = (-1)^(v(a)v(b)) a^(v(b)) b^(-v(a))`, the standard form. `I_p` uses only
    `v_p` of residues, so a global sign or inversion convention cannot matter.
  - *(UFD)* Auslander–Buchsbaum. It makes height-one primes principal.
  - *(L)* The exact sequence `0 → B/h →(g) B/gh → B/g → 0`, valid because `B` is a domain.
- **Hypothesis match for `D`.** This is exactly the `D` of `resolvent-ring-has-path-normal-form` (Step 1,
  `x^k u x^(-k) = u + kl`) and of `euler-triangular-ring-is-fp-rf`, with `A = Z[u][(u+1+kl)^(-1)]` and `σ(u) = u + l`.

## Steps checked

- **Reciprocity lemma.** Correct.
  - For `z = {a,b}`, `ord_π ∂_π{a,b} = Σ_(ρ≠π) (β_π α_ρ − α_π β_ρ) ℓ(O/(π,ρ))`.
  - The `(π,ρ)` and `(ρ,π)` terms cancel.
  - Primes dividing neither `a` nor `b` contribute unit residues.
  - Only finitely many terms are nonzero.
- **Part 1.** Correct.
  - `σ` maps `v_(π_k)` to `v_(π_(k+1))`, and on the residue fields `Z[u]/π_k ≅ Z` it acts as the identity: both
    evaluate at `-1-kl`. So `∂_(k+1)σ = ∂_k`.
  - Only the `(π_k)` can carry residues of `z ∈ K_2(A)`. This includes the vertical prime `(p)`: it contains no
    `π_k`, so `Z[u]_(p) ⊇ A` is a DVR, and DS §10(a)(i) applies.
  - Each `π_k` meets the fibre over `p` in exactly one point. There `O/π_k ≅ Z_(p)`, so `ord = v_p`.
  - Summing the reciprocity identities over the points of the fibre gives `T_p = 0`.
- **Part 2.** `∂_0 c_d = (dl)^(-1)` and `∂_d c_d = -dl`, so `I_p(c_d) = d v_p(d)` for `p ≠ l`. Correct.
- **Part 3.** `I(c_q) = q e_q`, so a relation `Σ n_q [c_q] = 0` forces all `n_q = 0`. Correct.
  - The retractions `D × Z ⇄ T_l` and `D ⊆ R_l → R_l/(e) ≅ D` make `K_2(D)` a summand without Berrick–Keating.
- **Part 4.**
  - For commuting units, the rank-`N` symbols lie in `K_2(N,·)` and map to the stable symbols.
  - A finitely generated `K_2(N,T_l)` would have finitely generated image in `K_2(T_l)`, but that image contains a
    free abelian group of infinite rank. So `K_2(N,T_l)` is not finitely generated.

## Recorded alongside

- **The `(T2)` diagnosis is right.** The support of `S`-torsion modules is the union of the lines `π_k = 0`, and these
  meet over the primes dividing `(k-j)l`. So dévissage does not split the localization term as `⊕_k K(Z[u]/π_k)`.
  The residues land in `⊕_k Q^x`.
- **Correction to my report 76fc7667e.** Under (T2) there I wrote that "the localization step ... gives
  `K_1(A) = ±1 × ⊕Z π_k` and `SK_1(A) = 0`". The unit group `A^x = ±1 × ⊕ Z π_k` is right, directly from unique
  factorization. The `SK_1(A) = 0` conclusion used the same invalid dévissage, and I withdraw it. It is not needed
  here.
- **Re-check (requested).** The Scope line of `free-group-mapping-tori-contain-no-z-localized` now points to the
  ascending-HNN node. Fixed at the tip.
