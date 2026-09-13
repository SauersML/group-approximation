# Nontrivial R-fibre W*-bundle: open-status and priority pass (2026-09-13)

Lane `ex-novelty`, 01:00–01:40 CDT, at the coordinator's request.

**Claim checked.** Lane ex2-tw-unsplittable-tails, 4934442568, unreviewed; route
`nontrivial-w-star-bundle-via-pauli-tower` into `nontrivial-w-star-bundle-with-r-fibres-exists`.
- The witness is the uniform tracial completion `M` of `lim_m C(Π_{k≤m} Y_k, ⊠_{k≤m} B_k)`.
  - `Y_k = RP^{4^{k−1}} × RP^{2·4^{k−1}}`.
  - `B_k` are flat `M_2`-bundles with Pauli holonomy.
- `M` is a strictly separable continuous W*-bundle over `X̂ = Π_k Y_k`, with every fibre `R`.
- Nontriviality comes from the scalar point property: every self-adjoint element is scalar somewhere. This is
  certified by the top Stiefel–Whitney class of the traceless part, which is the Moore determinant.

**Method.**
- arXiv LaTeX sources fetched on MSI:
  - BBSTWW 1506.03974;
  - Ozawa 1304.3523;
  - Evington–Pennig 1601.05964;
  - Mommaerts 2606.12134.
- In each source I extracted every theorem-like environment that mentions bundles, and every question environment.
- Printed numbers were checked by counting the section-numbered theorem counters in the source.
- arXiv abstract pages were fetched, and the arXiv search UI was queried for "W*-bundle" (abstracts).

**Limits.** OpenAlex citing-work lists returned HTTP 429 on every retry and are not included. Web search is exhausted.

**Tags.**
- S: source read;
- A: abstract or listing;
- C: Cairn text on main.

## (a) BBSTWW Question 3.14

Bosa–Brown–Sato–Tikuisis–White–Winter, *Covering dimension of C*-algebras and 2-coloured classification*,
arXiv:1506.03974v3 (24 May 2016); Mem. Amer. Math. Soc. 257 (1233), 2019 (A).

In Section 3, "Ultrapowers of trivial W*-bundles", `main.tex` line 1233 (S):

> **Question 3.14.** Does there exist a nontrivial strictly-separable bundle `M` over a compact metrizable space `K`
> all of whose fibres are copies of `R`?

- **Numbering.** `\newtheorem{question}[theorem]{Question}` shares a counter with every other theorem-like environment,
  and `\numberwithin{theorem}{section}` numbers it within sections. Counting the environments in Section 3 up to this
  one gives 3.14.
- **Context that follows it** (S): "There are two key conditions where triviality is known to hold: when `K` has finite
  covering dimension (this is due to Ozawa, [Corollary 12]{O:JMSUT}), and when `M = B̄^st` for a separable, unital,
  nuclear `Z`-stable C*-algebra `B` such that `T(B)` is a Bauer simplex."
- The next theorem (label `OzawaBundles`) states both cases.
- "Corollary 12" is the numbering of Ozawa's journal version. The same statement is Corollary 16 in arXiv:1304.3523.
- The node statement matches the source.

## (b) Mommaerts Remark 4.7

Mommaerts, *A non-locally trivial W*-bundle with fixed factorial fibres*, arXiv:2606.12134v1 (10 Jun 2026) (A).

`main.tex` line 613 (S), in Section 4, "Uniform w-spectral gap for subtrivial bundles":

> **Remark 4.7.** "Since the hyperfinite II_1 factor R also satisfies M_2(R)≅R, one could naively mimic the construction
> of [Example 4.6] with R instead of L𝔽_∞ and hope to obtain a W*-bundle that is not locally trivial. However, the bundle
> obtained in that way will(!) be trivial. Indeed by Ozawa's triviality result [OzawaWbundle], if there exists a
> non-trivial W*-bundle with all fibres isomorphic to R, then the base space must have infinite covering dimension. The
> (non)-existence of such a bundle is not known."

- **Numbering.** The remark environment shares the section-numbered `theorem` counter. Counting in Section 4 gives 4.7,
  which agrees with the arXiv HTML rendering.
- **Remark 4.8** (S): "It would be interesting to see whether there are non-locally trivial W*-bundles with all fibres
  isomorphic to some fixed factor that do have uniform w-spectral gap. However, as of now, we know of no other
  obstruction for such bundles being locally trivial than the negation of the uniform w-spectral gap property."
- **Main result** (S, introduction): "Evington and Pennig leave open the question of whether or not every W*-bundle with
  all fibres isomorphic to some fixed factor M is necessarily locally trivial. In this paper we resolve this question
  to the negative with the following counterexample over a space of covering dimension equal to zero."
  - The fibres there are full factors (`L𝔽_∞`), not `R`.
- The lane read Remark 4.7 correctly: as of June 2026, existence is recorded as not known.

## (c) Were nontrivial R-fibre W*-bundles already known?

Within this bound, no.

- **Ozawa,** *Dixmier approximation and symmetric amenability for C*-algebras*, arXiv:1304.3523 (J. Math. Sci. Univ.
  Tokyo 20 (2013)) (S).
  - Theorem 15: a strictly separable continuous W*-bundle with every fibre `R` is trivial iff it has approximately
    central approximate projections with `E(p_n) → 1/2`, iff for every `k` there is an approximately central
    approximately multiplicative embedding of `M_k`.
  - Immediately before Corollary 16: "It is unclear whether the finite-dimensionality assumption is essential."
  - Corollary 16: finite covering dimension implies triviality.
  - No example is given.
- **Evington–Pennig,** *Locally trivial W*-bundles*, arXiv:1601.05964 (Internat. J. Math. 2016) (S).
  - Theorem 4.10 (label `thm:hyperfinite_trivial`): "A locally trivial W*-bundle with all fibres isomorphic to the
    hyperfinite II_1 factor R is trivial." The abstract adds: "There is no restriction on the covering dimension of X."
  - Their nontrivial locally trivial examples, in the section "Non-trivial, locally trivial bundles", have a II_1
    factor fibre `M` with a finite group inside `Out(M)`. That fibre is not `R`.
- **Mommaerts 2026** (S): the first non-locally-trivial bundles with fixed factor fibres. They use full factors, and
  Remark 4.7 says the `R` case is unknown.
  - Mommaerts cites Evington's thesis (Proposition 3.1.10 of `Evington_thesis`). That is indirect evidence the thesis
    contains no example.
  - The thesis itself was not read.
- **arXiv abstract search "W*-bundle"** (A): Mommaerts 2606.12134, Vaccaro 2303.01942 (ultraproducts of factorial
  W*-bundles), Evington–Pennig 1601.05964. None constructs a nontrivial `R`-fibre bundle. Papers that write the term in
  TeX may be missed.
- **Not checked:**
  - papers citing BBSTWW, Ozawa or Evington–Pennig (the OpenAlex lists were rate-limited);
  - Evington's thesis;
  - MathSciNet.

## (d) What is known, by base

- **Finite covering dimension ⇒ trivial:** Ozawa's Corollary 16 (arXiv numbering; Corollary 12 in the journal), restated
  as BBSTWW Theorem 3.15(1) for tracial completions.
- **Z-stable algebras with a Bauer simplex ⇒ trivial completion:** BBSTWW Theorem 3.15(2).
- **Locally trivial ⇒ trivial, over any compact Hausdorff base:** Evington–Pennig Theorem 4.10, via Popa–Takesaki
  contractibility of `Aut(R)`.
- **Repo-internal on main** (C; proofs landed 09-12 at f095abc5d and 0bb74f48d; review status not re-checked):
  - countable-dimensional bases give trivial bundles (`r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial`);
  - the locus where local triviality fails lies where every neighbourhood is infinite-dimensional
    (`bauer-gamma-failure-localizes-to-infinite-dim-point`).
- **Infinite-dimensional bases, e.g. anything containing a Hilbert cube:** open in the literature as of Mommaerts,
  June 2026.
- **Consistency of the lane's witness with all of the above.**
  - `X̂` has infinite covering dimension and contains a Hilbert cube.
  - The bundle is not locally trivial.
  - The algebra is claimed not Z-stable.
  - Its consequence C2, that the reduced power has no unital `M_2`, is exactly the failure of Ozawa's Theorem 15(iii).
  - This is a consistency check, not a verification.

## Verdict

- **(a) and (b)** are quoted correctly on main: BBSTWW Question 3.14 (arXiv:1506.03974v3; Mem. AMS 2019) and Mommaerts
  Remark 4.7 (arXiv:2606.12134v1, "The (non)-existence of such a bundle is not known").
- **(c) Novelty.** No earlier nontrivial `R`-fibre W*-bundle was found. As of June 2026 the question is explicitly
  recorded as open. If the witness survives review, it looks like the first answer to BBSTWW Question 3.14.
- **Caution.** The claim is unreviewed. Any public statement needs the `ex-verify-analysis` pass the lane requested.
- **Bound.**
  - 4 sources read at the level of their theorem-like environments;
  - one arXiv abstract listing;
  - no citing-work lists;
  - Evington's thesis not read;
  - no web search.
