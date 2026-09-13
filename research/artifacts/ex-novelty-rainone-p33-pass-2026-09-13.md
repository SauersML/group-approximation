# Rainone's page-33 question: open-status and priority pass (2026-09-13)

Lane `ex-novelty`, 10:10–10:50 CDT, at the coordinator's request.

**Claim checked.** Lane `ex2-rr0-clopen-type`, landings 7dc75e41d1..84f5d99869, unreviewed.
- `rainone-non-almost-unperforated-minimal-outer-action-exists`, via `rainone-question-answered-by-generic-witnesses`.
- The ingredients are `refinement-monoids-are-topologically-free-cantor-types` (Wehrung's realization with generically chosen witnesses) and `topologically-free-finite-clopen-type-via-generic-witnesses`.
- The result: minimal, topologically free actions of `F_∞` on the Cantor space whose type semigroups are not almost unperforated.

**Method.**
- Rainone's arXiv PDF: pages 32–34 read as images.
- LaTeX sources on MSI:
  - Rainone 1502.06153;
  - Boldrini–Prasad 2607.01896;
  - Ara–Bönicke–Bosa–Li 2001.00376;
  - Kerr 1710.00393;
  - Ma 1808.02404;
  - Kwaśniewski–Meyer–Prasad 2502.17190;
  - Geffen–Hua–Kranz 2608.13000.
- arXiv search-UI listings: type semigroup almost unperforated; dynamical comparison; Rainone; Wehrung; generic free Cantor actions; type semigroup of ample groupoids.

**Limits.** OpenAlex citing lists for Rainone returned HTTP 429 every time, and web search was exhausted.

**Tags.**
- S: source read;
- P: PDF page read;
- A: abstract or listing.

## (a) The question, verbatim, and its status

Rainone, *Finiteness and paradoxical decompositions in C\*-dynamical systems*, arXiv:1502.06153v1 (21 Feb 2015; the only
arXiv version). Published in J. Noncommut. Geom. 11 (2017), no. 2, 791–822, per the bibliography of Ma, arXiv:1808.02404
(S). The journal PDF was not reached.

**Theorem 4.22** (pp. 32–33, P):
> Let A be a unital, separable, exact C*-algebra whose projections are total. Moreover suppose A has cancellation and
> K_0(A)^+ has the Riesz refinement property. Let Γ be a countable discrete group and let α: Γ → Aut(A) be a minimal and
> properly outer action such that S(A,Γ,α) is weakly unperforated. Then the reduced crossed product A ⋊_λ Γ is a simple
> C*-algebra which is either stably finite or purely infinite. Moreover, if A is AF and Γ = F_r, then A ⋊_λ Γ is MF or
> purely infinite.

**The question** (p. 33, P; the same text is in `main.tex` line 888, S):
> We end our discussion with a few interesting questions. It is unknown to the author if there are examples of minimal and
> properly outer actions on C*-algebras satisfying the conditions in Theorem 4.22 for which the type semigroup is *not*
> almost unperforated. In particular, is there a free and action of the free group F_2 on the Cantor set X for which
> S(X, F_2, C) is not almost unperforated? Although Ara and Exel construct actions of a finitely generated free group on
> the Cantor set for which the type semigroup is not almost unperforated, these actions are not minimal [1]. Moreover,
> almost unperforation may be too strong a condition to establish (5) ⇒ (1) in Theorem 4.21. What is required is that
> every 'infinite element' (in the sense that (k+1)x ≤ kx for some k) is properly infinite. This is a priori a weaker
> condition than almost unperforation.

- "a free and action" is Rainone's own typo; the lane's quote reproduces it faithfully.
- The lane's quote on `rainone-non-almost-unperforated-minimal-outer-action-exists` omits the last sentence.
- As printed, the question was open in 2015.

## (b) Was it answered later?

**Yes, in substance, for `F_∞`, ten weeks before the lane.** P. Boldrini and A. Prasad, *Topologically free minimal actions without
dynamical comparison*, arXiv:2607.01896v1 (2 Jul 2026) (S, A).

Introduction theorem (S):
> There exist topologically free minimal actions of F_∞ on the Cantor space without dynamical comparison. Moreover, these
> actions can be chosen to be either Bernoulli-measure-preserving, or without any invariant probability measure.

**Mechanism** (S, introduction).
- They cite Ara–Bönicke–Bosa–Li and Kwaśniewski–Prasad–Thiel–Wu for the equivalence of dynamical comparison with almost
  unperforation of the type semigroup. They cite [ABBL, Lemma 2.2] for "a dynamical system is minimal if and only if the
  type semigroup is simple".
- Strategy: "first construct a simple and non almost unperforated commutative monoid, and then realise it as the type
  semigroup of a countable group action", following Wehrung LNM 2188, Chapter 4.

**Results** (S):
- Theorem `thm.constructionP`: a countable cancellative 2-divisible simple refinement cone that is not almost unperforated,
  with a V-homomorphism to a subcone of `R_+`.
- Proposition `thm.constructionQ`: such a cone with no nontrivial states.
- Theorem `cor.Mistypesem`: `(M,u) ≅ (S(Aut(B,μ) ⋉ St(B)), [St(B)])` for a group-induced V-measure, obtained as a Fraïssé limit.
- Theorem `thm.minactnocomp`: every countable dense subgroup `H ≤ Aut(B,μ)` acts minimally and without dynamical comparison.
- Proposition `thm.generictopfreenessnew` and Corollary `thm.generictopfreeness`: a dense `G_δ` in `Aut(B,μ)^ℕ` on which every
  nontrivial word acts nontrivially on every nonzero `c`.
- Theorem `thm.genericnocomp`: "A generic countable subgroup of Aut(B,μ) is dense, isomorphic to F_∞, and acts topologically
  freely on St(B)."
- Corollaries: Bernoulli-preserving examples, and examples with no invariant measures.

**Why this answers Rainone's first sentence.**
- `C(X)` with `X` Cantor satisfies the standing hypotheses of Theorem 4.22.
- For commutative `C(X)`, properly outer is the same as topologically free.
- Their type semigroups are simple and not almost unperforated.

**Credit.**
- Their bibliography cites Rainone–Sims, but not Rainone 1502.06153 (S, `.bbl`).
- They thank Pere Ara "for giving the idea about a minimal action whose type semigroup is not almost unperforated".
- The lane's nodes do not cite Boldrini–Prasad. The generic-witness Baire argument and the Wehrung realization are theirs.
- The lane was messaged at 10:45.

**Other sources checked (no answer to the question).**
- Ara–Bönicke–Bosa–Li, arXiv:2001.00376 (S). Theorem A: minimal ample groupoids have almost unperforated `S(G)` iff they have
  dynamical comparison. Proposition `Prop:purely infinite order units`: when every measure in `UM(G)` is trivial, dynamical
  comparison holds iff every element of `S(G)` is properly infinite. Almost finite implies almost unperforated. They give no
  minimal counterexample.
- Kerr, arXiv:1710.00393 (S). For free minimal Cantor actions, almost finiteness ⇒ `S(X,G)` almost unperforated ⇒ comparison.
  No counterexample.
- Ma, arXiv:1808.02404 (S). For minimal measure-free actions, `W(X,G)` is almost unperforated iff dynamical comparison holds.
  No counterexample.
- Kwaśniewski–Meyer–Prasad, arXiv:2502.17190 (S): the dichotomy under "plain paradoxes". Their example `{0,1,∞}` is paradoxical
  but not properly infinite at the monoid level. No dynamical realization.
- Geffen–Hua–Kranz, arXiv:2608.13000 (A, S): positive results only.

## (c) Generic topological freeness

- **Already in Boldrini–Prasad** for the Fraïssé-limit `(M,u)`-measured Cantor algebra: Proposition `thm.generictopfreenessnew`,
  Corollary `thm.generictopfreeness`, Theorem `thm.genericnocomp`. That is the setting and the argument of the lane's route
  (Baire category over sequences in `Aut(B,μ)^ℕ`, steering one word at a time).
- **Wider generic-freeness literature** in `Homeo(2^ℕ)` and `Aut(X,μ)`:
  - Boldrini–Prasad cite Kechris and Glasner (S, `.bbl`).
  - arXiv:2409.03078, "Asymptotic dimension and hyperfiniteness of generic Cantor actions", surfaced in the listing.
  - Neither was read.
- **The lane's own firewall** (84f5d9986): exhaustive pairs are not dense in `Aut(B,μ)^2`, so the argument does not run verbatim
  for `F_2`.

## Verdict

- **(a)** The question was printed on p. 33 of arXiv:1502.06153v1 (J. Noncommut. Geom. 11 (2017)). As printed it is open, and the
  lane quotes it faithfully apart from the omitted last sentence.
- **(b) Not new.** Its general form, for `F_∞` acting minimally and topologically freely on the Cantor space, is answered in
  substance by Boldrini–Prasad arXiv:2607.01896v1 (2 Jul 2026), who do not cite Rainone. The lane's result is an independent
  rediscovery with the same mechanism, and it must credit them.
- **What may still be new, bounded:**
  - the explicit match with Rainone's question and his Theorem 4.21/4.22 framing;
  - failure of his weaker "infinite element" condition. This probably follows from Boldrini–Prasad's no-measure examples
    together with ABBL's Proposition `Prop:purely infinite order units`, but that was not checked in detail.
- **Still open, as far as found:** the `F_2` sub-question, asking for a free action.
- **(c)** Generic topological freeness in `Aut(B,μ)` is already in Boldrini–Prasad.
- **Bound.**
  - 8 sources grepped;
  - 6 listings;
  - no citing-work lists (OpenAlex 429);
  - the journal PDF of Rainone not reached;
  - no web search.
