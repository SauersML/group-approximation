# Referee report (gq-referee-b, citation/scope lens): unit symmetries of a core are graded or inessential

**Reviewed.** Both from lane gq-infinite-primes, 69c0569db, read on origin/main:
- `unit-symmetries-of-a-core-are-graded-or-inessential` and its `-proof`;
- Attempt 11 of `fp-simple-resolvent-ring-with-divisible-unit-class`.

**Verdict: PASS.**
- Items 1–4 are correct, and the proof is self-contained.
- The Jordan attribution is fair only once his criterion is stated precisely, including a second condition (below).
  The node's own item 1 produces exactly that condition.
- There are two scope fixes, W1 and W2.

## Jordan's criterion (secondary source, read)

- **Source.** P. Bäck and J. Richter, *Simplicity of non-associative skew Laurent polynomial rings*,
  arXiv:2207.07994v9 (Proc. Edinb. Math. Soc. 68 (2025)). I read p. 4.
- **Theorem 3**, "([5, Theorem O])", verbatim: "Let R be an associative ring with a ring automorphism σ. Then R[X^±; σ]
  is simple if and only if R is σ-simple and there do not exist u ∈ R^× and a non-zero n ∈ Z, such that for all r ∈ R,
  the following equalities hold: (i) σ^n(r) = u^(-1) r u; (ii) σ(u) = u."
- **The reference.** Their [5] is D. A. Jordan, *Simple skew Laurent polynomial rings*, Comm. Algebra 12 (1984),
  135–137. The page range is from a search result; I did not read the primary paper.
- **The lane's paraphrase needs a qualifier.** "Simple iff σ-simple and no `σ^m` inner" drops condition (ii). The
  correct statement is: no `σ^m` that is inner *by a `σ`-fixed unit*.
  - "No power inner" is sufficient for simplicity but not necessary.
- **Item 1 matches the correct form exactly.** It produces `u = g_m`, with `σ(g_m) = g_m` and
  `σ^m(b) = g_m^(-1) b g_m`.
- **Recommendation.** Cite Jordan's Theorem O with conditions (i) and (ii), via Bäck–Richter Theorem 3 if the primary
  is not read.

## Steps checked

- **Item 1.**
  - `I_0` is an ideal: it is additive, and `(bg)_0 = b g_0`, `(gb)_0 = g_0 b`.
  - `I_0` is `σ`-invariant: conjugation by `x^(±1)` preserves support.
  - So `I_0 = A`. Minimality gives `g_m ≠ 0`, and `m ≥ 1` since `R ≠ 0`.
  - *Commutation.* `bg − gb` and `xgx^(-1) − g` lie in `J`, vanish in degree `0`, and have width `< m`, so they are
    zero.
  - *`g_m` is a unit.* `Ag_m = g_mA` is a nonzero `σ`-invariant ideal.
  - *Division by the central `g`.* The top step uses `c = h_n g_m^(-1)`; the bottom step works because `g_0 = 1`.
    Uniqueness in width `< m` then gives `J = Tg`.
- **Item 2.** The hypotheses of the graded node hold: a unital map `Q → R`, and the unit `x` of degree `1` in
  `A[x^(±1);σ]`.
- **Item 3.**
  - *(a)* The basis `x^k`, `k < m`, holds on both sides.
  - *(b)* `A''` is `σ^(±1)`-stable: `σ^m(F) = g_m^(-1) F g_m` and `σ^(-1)(F) = g_m σ^(m−1)(F) g_m^(-1)`. Division stays
    inside `A''`. Uniqueness of the normal form gives `A = A''`.
  - *(c)* Inner automorphisms act trivially on `K_n`.
  - *(d)* Restriction gives `[1_R] ↦ m[1_A]`. Induction gives `Σ σ^k_*`; the direction convention is immaterial,
    since `σ^m_* = id`. `Q ⊆ A` because `n` acts coefficientwise and bijectively on `⊕ A x^k`.
- **Item 4.**
  - Divisibility passes through restriction.
  - `ind(m[1_A]) = m[1_R]` gives infinite order.
  - `K_1` detection passes to `A` because the kernels are nested.

## Scope

- **W1 (item 4, last sentence).** "So a unit symmetry can make an infinite-rank base finitely *presented* only in the
  graded case." Item 3(b) proves finite *generation* of `A` in the inhomogeneous case; finite presentation of `A` is
  not addressed.
  - The design logic, as gate Attempt 11 puts it, is "the base is then not finitely generated, so finite presentation
    needs a mechanism that generates it". That needs only generation.
  - Say "finitely generated".
- **W2 ("What is closed" / gate "What remains").** Item 1 assumes `A` is `σ`-simple.
  - The node's Scope records this under "Hypothesis".
  - But gate Attempt 11's "What remains" lists only non-invertible shifts. Unit symmetries of cores with a nonzero
    proper `σ`-invariant ideal are not closed.
  - Simplicity of `R` does not obviously exclude them in the inhomogeneous case: an invariant ideal `I` of `A` gives
    `R = π(⊕ I x^k)`, which is no contradiction.
  - Add "or unit symmetries of non-`σ`-simple cores" to "What remains". Alternatively, prove `σ`-simplicity from
    simplicity of `R` in the gate's setting.
- **Gate Attempt 11, otherwise.** It is accurate.
  - The constraint paragraph is conditional on (P), with the finite-rank case sent to Attempt 10.
  - The inhomogeneous summary matches item 3.
  - The register squeeze and its open cases are cited, not re-proved.
