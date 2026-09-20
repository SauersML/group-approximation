---
rg: 2
id: fp-rf-nonexact-and-odd-q-lin-review
kind: claim
title: Referee review of 40a67c7c4b (bh-ra-t2) — the OPEN node "some finitely presented residually finite group is not exact" is correctly phrased and its citations check at source, with no printed statement found; the odd-characteristic Q_lin node's Steps 0–6 are correct given its inputs, but input (SA) as stated is not Pink's theorem and fails for subgroups with a smaller trace field (repair: work over the minimal quasi-model), the Pink citation is to Comment. Math. Helv., and (HJI) and (S) could not be checked at source
distinct_from:
  residually-finite-finitely-presented-non-exact-group: lane node under review here (OPEN question).
  congruence-closed-odd-linear-automaton-quotients-are-exact: lane node under review here (CONDITIONAL result).
---

**ESTABLISHED (referee bh-ref-d, 2026-09-19; review of two nodes in 40a67c7c4b by bh-ra-t2).** No
priority claimed.

## 1. `residually-finite-finitely-presented-non-exact-group` (OPEN): PASS

- **Phrasing.** Correct. For discrete groups, exactness, property A and exactness of `C*_r` are
  equivalent (Ozawa; Higson–Roe; Guentner–Kaminker; recalled).
- **Citations**, checked at source (arXiv abstracts; Osajda via the ar5iv HTML):
  - **Osajda, arXiv:1703.03791.** The paper constructs "finitely generated residually finite non-exact
    groups defined by infinite graphical small cancellation presentations". It says: "This answers one of
    few questions from the Open Problems chapter of the Brown-Ozawa book [2, Problem 10.4.6]." So the
    problem number is confirmed. The paper does **not** ask about finitely presented examples.
  - **Sapir, arXiv:1103.3873.** Every finitely generated group with a recursive aspherical presentation
    embeds in a finitely presented aspherical one. There is a closed aspherical 4-manifold whose
    fundamental group coarsely contains an expander, which gives finitely presented non-exact groups.
    Residual finiteness is not addressed.
  - **Kharlampovich–Myasnikov–Sapir, arXiv:1204.6506.** The abstract reads: "The groups are solvable of
    class 3." So they are amenable, hence exact, as the node says.
- **In print?** I did not find the question printed. Osajda's paper and a web search turned up nothing
  beyond what the node lists. The node's wording, "a statement about our search", is right.
- **Minor.** Guentner–Higson–Weinberger prove exactness for linear groups over **fields**. Groups over
  commutative rings follow by the nilradical argument (nilpotent-by-linear). Say so, or cite it as
  "GHW plus nilradical reduction".

## 2. `congruence-closed-odd-linear-automaton-quotients-are-exact` (CONDITIONAL): Steps check; (SA) must be restated

**The argument, given (SA), (HJI) and (S): correct.**
- **Step 0.** `F ∩ N̄ = N` because `N` is congruence-closed.
- **Step 1.** `[x, y_v]` is supported at `v`, and it lies in `U_v` once `U_v` is replaced by its normal
  core. Distinct coordinates commute, so `N̄` contains the full product `∏ K_v`.
- **Step 2.** The claim `ker ψ ≤ N̄` checks, and `F/N ↪ H/M` follows.
- **Steps 3–4.** `L_v` is normal in `H_v`, and `[m, h] ∈ L_v`. `(M ∩ H_0L)/L` is centralized by `M/L`
  and has finite index in it, so `M/L` is abelian-by-finite.
- **Step 5.** `H ∩ ∏L_v = L`. The adjoint map to `GL_4(∏B_v)` has scalar (abelian) kernel. The
  finitely generated image lies over a Noetherian ring with nilpotent nilradical, whose reduced quotient
  embeds in a finite product of fields. So the image is nilpotent-by-linear, hence exact.
- **Step 6.** For amenable `A ⊴ Δ`, `λ_(Δ/A)` is weakly contained in `λ_Δ`, and quotients of exact
  C*-algebras are exact (Kirchberg).
- **Item 2 (periodic = congruence).** Correct: every `f` with `f(0) ≠ 0` divides some `t^ℓ − 1`.
- **Item 3 (GL_2 reduction).** Correct. One addition: if `F` is virtually solvable, `F/N` is amenable,
  so the "free subgroup of `[F, F]`" step is only needed otherwise.

**(SA) as stated is not what Pink proves.**
- **Citation.** Pink, "Strong approximation for Zariski dense subgroups over arbitrary global fields",
  *Comment. Math. Helv.* **75** (2000), no. 4, 608–643 (from Pink's publication list). The node says
  "Ann. of Math. 2000"; fix it.
- **The theorem.** Pink states his result relative to a **minimal quasi-model**, i.e. the trace field
  and a form of the group over it (from the published summary). I could not read the theorem's text,
  since fetching the PDF fails.
- **Why the stated form fails.** Let `F` be Zariski dense in `SL_2` but contained in
  `SL_2(F_q[s^(±1)])` with `s = t^2`. Then its closure in `∏_v SL_2(O_v)`, over the places of `F_q(t)`,
  lies in the image of the completions of `F_q(s)`. That image is not open at the places of `F_q(t)`
  over inert or split places of `F_q(s)`. So "the closure contains an open `∏_v U_v`" can fail for
  Zariski-dense `F`. Item 3's enlargement by a free subgroup of `[F, F]` does not raise the trace field.
- **Repair.**
  - Run Steps 0–6 over the trace ring `A_0` and the places of its fraction field, with Pink's quasi-model
    form. Non-split local forms occur at finitely many places, which go into `T`.
  - The congruence topology from `A` agrees with the one from `A_0`. `A` is finite and locally free, hence
    faithfully flat, over `A_0`, so `J′A ∩ A_0 = J′`. So item 2 and the consequence survive.
  - The residue fields at the places of `A_0` can be smaller than `F_q`. Places with a residue field of 3
    elements are finitely many and can be put into `T`, where only finiteness of `H_v` is used. So if
    (HJI) holds in residue characteristic 3, the `q ≥ 5` restriction may be removable. That is a
    suggestion, not checked.

**(HJI) and (S): not verified at source.**
- **(S).** Klingenberg, *Amer. J. Math.* 83 (1961), classifies normal subgroups of linear groups over
  local rings by congruence levels. The introduction of Lacroix, *Canad. J. Math.* (1969), states that
  classification. A secondary summary I found gives it for `n = 2` under conditions on 2 and the residue
  field. The node's form, `SL_2(O/m^k, m^j/m^k)·Z_0` for odd `q ≥ 5`, is consistent with it. The primary
  text is paywalled and I did not read it.
- **(HJI).** A secondary source states that `SL_n^1(F_p[[T]])` is just-infinite for `p > 2`. The node
  needs the stronger statement that every open subgroup of `SL_2(O_v)` is just-infinite modulo `{±1}`, for
  all odd `q`. No primary statement was located.
- **Tooling.** The fetch tool here cannot parse PDFs, and the lane rules bar reading PDFs locally. To
  check these two, and Pink's exact theorem, at source needs either a text extraction on acn112 or a
  coordinator exception.

## Verdicts

| node | verdict |
|---|---|
| `residually-finite-finitely-presented-non-exact-group` | PASS (OPEN record correct; one citation precision) |
| `congruence-closed-odd-linear-automaton-quotients-are-exact` | CONDITIONAL status stands; Steps 0–6 PASS given the inputs; (SA) must be restated over the minimal quasi-model; Pink citation corrected; (HJI) and (S) unverified at source |
