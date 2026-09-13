---
rg: 2
id: bk-relative-lemma-b
kind: claim
title: Relative Lemma B — kill the boundary in a radical quotient when the only annihilating trace is faithful on a proper ideal and infinite beyond it
distinct_from:
  moutzouris-faithful-trace-zero-class-both-signs: that realizes a killing embedding into a simple AF target using one faithful trace on the whole algebra; this asks to kill a subgroup when the annihilating trace is faithful only on a proper ideal and infinite beyond it.
  bk-rr0-uct-stably-finite-algebras-are-qd: that is the real rank zero UCT case of Problem VII; this is the general ideal-relative killing tool whose successor step would settle it.
  bk-radical-traces-vanishing-on-boundary-are-zero: that forbids a nonzero densely finite trace on the whole radical annihilating the boundary; this concerns the surviving traces, which are finite only on a proper ideal.
---

**OPEN.**  Let `A` be separable, nuclear and quasidiagonal with `A` and every
quotient of `A` satisfying the UCT.  Let `G ⊆ K_0(A)` be singular
(`G ∩ K_0^+(A) = {0}`).  Suppose there are an ideal `I ⊴ A` and a lower
semicontinuous trace `τ` on `A` with:

1. `τ` is faithful and densely finite (finite on `Ped(I)`) on `I`, and `τ̂`
   annihilates `G_I := G ∩ im(K_0(I) → K_0(A))`;
2. `τ` is `+∞` on every nonzero positive element of `A` outside `I` (its induced
   trace on `A/I` is degenerate);
3. up to scaling `τ` is the only l.s.c. trace on `A` annihilating `G`.

Then there is a faithful \*-homomorphism of `A` into a quasidiagonal algebra
killing `G`; i.e. `A` has the K_0-embedding property for `G`.

**Role.**  By `bk-radical-traces-vanishing-on-boundary-are-zero` (Theorem 7), a
Blackadar--Kirchberg counterexample with UCT quotients has no nonzero densely
finite trace on `R = R_qd(E)` annihilating `H = ∂(K_1(E/R))`.  So every
annihilating trace is infinite somewhere, and relative Lemma B is exactly the
tool that kills `H` at one archimedean level.  Iterated up a filtration of `R`
by archimedean classes it would settle both surviving residuals:
`bk-rr0-uct-stably-finite-algebras-are-qd` (real rank zero radicals with
non-archimedean `K_0`) and the type I Toeplitz points of
`bk-radical-projection-quotients-are-toeplitz-infinite`.

## Attempts

- **Moutzouris' realisation needs a global faithful trace.**  Lemma B and
  Corollary 4.5 (Moutzouris arXiv:2112.03224v3, from Schafhauser Cor 5.4 via
  Theorem 4.1) build a killing embedding into a *simple* AF algebra with *unique*
  trace, and require a *faithful* trace on all of the source.  Here the
  annihilating trace is faithful only on the proper ideal `I`; on `A/I` it is
  infinite.  The germ is Moutzouris Example 4.6, `A = C(S²) ⊕ C`,
  `x = (0,1,-1)`: the annihilating state (living on `C(S²)`) is not induced by
  any faithful trace of `A`, because the infinitesimal Bott class `(0,1,0)`
  pairs to `0` with every state while the `C`-summand class pairs positively
  with every faithful trace.  Moutzouris flags this exact frontier (p. 22): his
  class `G` demands that every state on `K_0` be induced by a faithful trace,
  and he records no interesting algebra escaping it.

- **Split/direct-sum escape works, but does not cross an extension.**
  Proposition 5.6 (class `O` = finite direct sums of members of `G` and AF
  algebras) kills every singular subgroup of `⊕ A_i`.  The mechanism: choose a
  total order on `K_0(A_i)/G_i^{zero}` (Lemma 4.2) making the `i`-th projection
  of `G` negative, realise it by a faithful trace `τ_i` on `A_i` (needs
  `A_i ∈ G`), lift by Theorem 4.1 to a simple AF `B_i`; an AF summand needs *no*
  trace, since Elliott's classification lifts the positive `K_0`-map and
  property SP forces injectivity.  So `C(S²) ⊕ C` is fine (both summands are in
  `O`), confirming the direct-sum obstruction dissolves.  But none of
  Propositions 3.1--3.5 glue an ideal representation to a quotient
  representation: Moutzouris' local machinery approximates `A` by *subalgebras*,
  and a non-split `A` is not locally `I ⊕ A/I`.

- **Traceless quotient: partial.**  If `A/I` is *traceless* (not merely
  infinite-traced) then by `gabe-traceless-exact-qd-af-embedding` it is
  AF-embeddable, and if the six-term boundary `∂ : K_1(A/I) → K_0(I)` vanishes
  on the relevant classes a Brown--Dadarlat gluing (Theorem 3.4) kills the image
  `Ḡ`.  Where it dies: in general `A/I` is infinite-traced but *not* traceless
  and *not* AF, so neither Elliott nor Gabe lifts a `K_0`-map into it without a
  faithful trace.

- **The missing input is an ideal-equivariant realisation.**  Realise a
  positive, ideal-compatible `K_0`-map `A → B` into an AF algebra `B` with a
  distinguished ideal `B_I` carrying the faithful trace of `I`, killing `G`.
  This is the non-simple / relative form of Schafhauser Cor 5.4, deferred by
  Schafhauser (p. 4) to forthcoming Carrión--Gabe--Schafhauser--Tikuisis--White
  work — a classification-of-embeddings question.  Whether it holds, or fails and
  lets a non-split infinitesimal obstruction survive as a genuine Problem VII
  counterexample, is the crux.

## Resolution so far (2026-09-13)

`bk-relative-boundary-descends-or-is-positively-detected` establishes that this
tool cannot be an *unconditional* boundary-killer.  The surviving property (no
densely finite annihilating trace, Theorem 7) descends down every quotient, and
at the finiteness ideal `I` of `τ` the boundary splits:

- **Ideal-captured (`π_*(G) = 0`):** `G` lives in `im(K_0(I) → K_0(A))` and
  `τ|_I` is a genuine faithful densely finite trace annihilating the lift.  The
  problem reduces to Lemma B on `I` plus one Brown--Dadarlat gluing step.  Two
  residual conditions remain even here: (i) `τ|_I` must also annihilate the
  *inner* extension boundary `∂(K_1(A/I)) ⊆ K_0(I)`, which a trace need not do
  (Toeplitz: `Tr(∂[z]) = 1`), and (ii) the combined subgroup
  `G̃ + ∂(K_1(A/I))` must stay singular in `K_0(I)` (a sum of two singular
  subgroups need not be).

- **Escaping with positive detection (`π_*(G) ∩ K_0^+(A/I) ≠ 0`):** the quotient
  detects a singular boundary class positively, `E/K` is forced infinite
  (Theorem 9), and no faithful embedding into a *stably finite* QD algebra kills
  `G`.  Corollary 10 shows a type I counterexample is forced into this shape at
  its elementary points.  This is the shape the tool must avoid.

So the two crisp open questions are: **(A)** in the ideal-captured case, do the
two residual conditions (i),(ii) hold for the radical's finiteness ideal? and
**(B)** can the escaping-with-positive-detection shape be realised by a *stably
finite* nuclear UCT `E`?  A yes to (B) is a Problem VII counterexample; a
provable no closes the glued UCT case.  Question (B) is internally consistent
(no trace obstruction survives the descent) and coincides with Problem VII for
the glued UCT radical itself.
