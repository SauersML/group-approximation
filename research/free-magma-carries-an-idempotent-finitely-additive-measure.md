---
rg: 2
id: free-magma-carries-an-idempotent-finitely-additive-measure
kind: claim
title: The free magma on one generator carries a finitely additive probability measure ν with ν^ν = ν (Moore's nonassociative Ellis lemma)
distinct_from:
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that uses idempotent state measures of finite tree automata to kill expansion certificates; this asks for an idempotent measure on the infinite free magma itself, which would give an invariant mean.
  moore-ramsey-criterion-for-amenability: that is the published Ramsey criterion; this is the existence statement of Moore's withdrawn arXiv:1209.2063.
  thompson-f-is-amenable: that is the root; this claim implies it through Moore's Theorem 3.3, and it may be strictly stronger.
---

**OPEN.** Let `T` be the free magma on one generator `1` (finite binary trees), with operation `^`. Let `Pr(T)` be the
finitely additive probability measures on `T`, with `μ^ν(Z) = ∫∫ χ_Z(x^y) dν(y) dμ(x)`. The claim is that some
`ν ∈ Pr(T)` satisfies `ν^ν = ν`.

**Source.** J. T. Moore, *Nonassociative Ramsey theory and the amenability of Thompson's group*, arXiv:1209.2063v1
(10 Sep 2012). The v1 PDF and the arXiv abstract page were read on 2026-09-17. Verbatim:

> Theorem 1.2. There is a ν in Pr(T) such that νˆν = ν.

> Theorem 3.3. If ν ∈ Pr(T) is an idempotent measure, then ν is F-invariant.

Here "F-invariant" means amenability of the partial action by re-association:
`ν({t : x_1·t and x_2·t are defined}) = 1` and `ν(x_1·Z) = ν(x_2·Z) = ν(Z)`. Moore writes, verbatim:
"It is well known that F is amenable if and only if this partial action is amenable".

Withdrawal comment on arXiv, verbatim:

> Over the weekend of September 29-30, 2012, Azer Akhmedov pointed out a serious error in Lemma 4.13. This error
> appears to be both serious and irreparable. I therefore withdraw my claim of a proof that F is amenable

**Why it matters.** This is a reduction of the root with a prerequisite that can fail on its own.
- *If true.* Theorem 3.3 and the quoted equivalence give `F` amenable.
- *If false.* Nothing follows for the root. The reduction runs one way only, and there is no known argument that
  amenability of `F` produces an idempotent measure.

**The sound half (Theorem 3.3), re-checked.**
- The proof in v1 §3 is complete given associativity of `⊗` for finitely additive measures (Moore's Proposition 3.2,
  proved there by weak* density of finitely supported measures).
- It uses `ν({1}) = 0`, the fact that `ν` gives full measure to trees whose left child is not a leaf, and
  `ν = (ν^ν)^ν = ν^(ν^ν)` with `x_1·((a^b)^c) = a^(b^c)`.
- The v1 text writes the null set as `{a^1}`. In the convention `x_1 : (a^b)^c ↦ a^(b^c)`, the complement of the domain
  is `{1} ∪ {1^c}`. That set is also null, because `ν^ν({1^c : c}) = ν({1})·ν(T) = 0`. So the typo is harmless.

## Attempts

- **2026-09-17 (swarm-0917-w6b-w6b-f-break, logic-computability).** Read into the graph. Three classes are dead.
  - *Moore's existence proof.* It dies at Lemma 4.13 (called Theorem 4.13 in v1): "The set IV coincides with the set of
    ν ∈ AV such that νˆν = ν". The author judged this error irreparable, as quoted above.
  - *Ultrafilters.* Define `f(1) = 0` and `f(a^b) = 1 − f(b)`, a magma homomorphism onto `({0,1}, (x,y) ↦ 1−y)`. Moore (v1
    §1) shows that `V^V ≠ V` for every `V ∈ βT`. The same homomorphism forces an idempotent measure to give
    `{f = 0}` measure exactly 1/2. Measures escape because they can take that value.
  - *Obstructions through finite quotients (class kill).* Let `h : T → M` be any magma homomorphism onto a finite magma.
    - For finitely additive `μ, ν`, the set `{(a,b) : h(a)*h(b) = z}` is a finite union of rectangles. So
      `h_*(μ^ν) = h_*μ * h_*ν`, with `*` extended bilinearly to the simplex `Δ(M)`.
    - The map `p ↦ p*p` is a continuous self-map of the simplex, so it has a fixed point by Brouwer.
    - Every `p ∈ Δ(M)` equals `h_*ν` for some finitely supported `ν`.
    - So no finite magma quotient, and no finite automaton coloring of `T` that is a congruence, can show that
      idempotent measures do not exist. The invariant is the push-forward to a finite quotient, and every member of
      the class dies at Brouwer's fixed point.
    - Compactness gives idempotent Borel measures on the profinite completion of `T`. But re-association does not
      preserve finite congruences in general, so these give nothing for `F`.
  - *Dies at / survives.* A refutation must use infinitely many nested congruences, or non-congruence sets. An existence
    proof must control the right-topological semigroup `(Pr(T), ^)` without associativity, which is exactly where Lemma
    4.13 failed.
