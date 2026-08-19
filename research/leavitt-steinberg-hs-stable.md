---
rg: 2
id: leavitt-steinberg-hs-stable
kind: claim
title: The binary Leavitt Steinberg cover is normalized-HS stable
distinct_from:
  wreath-flexible-hs-stability: This concerns the finitely presented Steinberg cover and ordinary normalized-HS stability; the other concerns flexible stability of a wreath candidate.
  leavitt-steinberg-hs-unstable: These are mutually exclusive branch selections for the same explicit group.
  hs-expander-block-decomposition: That is a general decomposition property of almost-representations of every Kazhdan group; this is the branch selection for one explicit group, which that property would imply.
artifacts:
  - notes/ATLAS_HS_CRITERION.md
  - notes/NOTEPAD.md
---

Prove normalized Hilbert--Schmidt stability of
`St_5(L_(F_2)(1,2))`.  Hyperfinite HS stability is already known here, but
is insufficient: a counterexample sequence may generate a nonamenable
limiting von Neumann algebra.

## Ideas

**External corroboration of the payoff, source-verified 2026-08-14.**
The implication this branch buys is a published theorem, not only the
repository's `leavitt-steinberg-hs-stability-fork`.  Becker--Lubotzky,
*Group stability and Property (T)*, arXiv:1809.00632, J. Funct. Anal. 278
(2020) 108298, Theorem 1.3(ii): "If `Gamma` is hyperlinear and has Property
(T), then it is not HS-stable, unless it is finite."  Their `HS` is the
**strict, normalized** metric `d_n(A,B)=‖A-B‖_HS` with
`‖T‖_HS=((1/n)Tr(T^*T))^(1/2)` and no dimension padding, i.e. exactly the
metric of this claim.  `U` is infinite and Kazhdan (Ershov--Jaikin-Zapirain,
arXiv:0809.4095, Theorem 6.2, `St_n(R)` for every `n>=3` and every finitely
generated associative unital `R`), so their theorem contraposes to
`U HS-stable ==> U nonhyperlinear`.  The fork's own proof needs less --
minimal almost periodicity alone -- but the manuscript may now cite an
external referee-visible statement for the branch payoff.

**The strongest published *instability* theorems are vacuous for `U`.**
This is the important negative mapping, and it is why the branch cannot be
decided by importing.  Becker--Lubotzky Theorem 1.4 and Theorem 4.1(ii)
obstruct HS-stability of a Kazhdan (respectively `(T;FD)`) group by
concluding that it has **only finitely many finite-index subgroups**; a
group with many finite-index subgroups is therefore not HS-stable.  `U` has
exactly one.  If `H<=U` had finite index its normal core would give a
nontrivial finite quotient, hence a nontrivial finite-dimensional unitary
representation of `U`, contradicting minimal almost periodicity.  So the
conclusion of their obstruction holds trivially and carries no information.
Every published route to "not HS-stable" runs through residual finiteness or
a rich finite-quotient lattice, and `U` has neither.

**`2`-Kazhdan is the wrong norm, confirmed from the source.**
De Chiffre--Glebsky--Lubotzky--Thom, arXiv:1711.10238, Forum Math. Sigma 8
(2020) e18, Theorem 1.2 concludes **Frobenius** stability, and the authors
name the obstruction themselves: "When the norm is submultiplicative (as is
the case of the Frobenius norm but not of the normalized Hilbert--Schmidt
norm) the kernel of this splitting problem is abelian", and again "The
operator norm and the Frobenius norm enjoy this property, but the normalized
Hilbert--Schmidt norm does not."  Submultiplicativity is a hypothesis of
their general engine (Theorem 3.6), not an artifact.  So the exact
`2`-Kazhdan reduction recorded for `U` -- vanishing of `H^2(U,H_pi)` for
every `pi` with `H_pi^U=0` -- would **not** select this branch even if
proved.  The branch needs a *dimension-free* degree-two vanishing, which is
a different theorem in a norm the DGLT machine does not accept.

**Hyperfinite stability is automatic here, and says why.**  The concession
in the statement above is now a node with its proof imported from the
corpus: `steinberg-hyperfinite-hs-stable`, from `notes/NOTEPAD.md:22220-22238`,
with the correct attribution (Dogon--Vigdorovich arXiv:2506.20843 Thm 6.2,
not Hadwin--Shulman) and the two citation traps recorded on its route.  It
constrains only the amenable part of the trace simplex, so it fences the
opposite branch without touching this one.

**The `(TT)/T` route is refuted and explicitly forbidden.**  Property
`(TT)/T` of `E_n(L_(F_2)(1,2))` for `n>=3`, and hence of `St_5(L)` by
invariance under Kazhdan central extensions, is **established** in the
corpus (`notes/LEAVITT_TT_T.md:203-241`).  It does not give this claim.
`notes/FALSE_TT_T_IS_NOT_DIMENSION_FREE_HS_STABILITY.md` isolates two losses:
normalized-HS control does not imply operator-norm control uniformly in the
dimension (`‖A‖_op <= sqrt(d)‖A‖_(2,d)`), and the Burger--Ozawa--Thom
statement fixes `d` before compactness, so it cannot be diagonalized into a
dimension-free modulus.  The same file's consistency check is the one I
reconstruct above from Becker--Lubotzky, and its directive at `:96-100` is
"Do not route the current proof through abstract `(TT)/T -> stability`."
Its `:79-93` lists what would finish instead: a dimension-free stability
modulus for the atlas relator packet, flexible normalized-HS stability with
`o(d_n)` padding, or a direct word-kill inequality.

**A constraint on the shape of any proof.**  Fournier-Facio--Gerasimova--Spaas,
arXiv:2307.13155: an infinite hyperlinear property-`(T)` group is never
*locally* HS-stable.  This does not obstruct the fork, which is about
ordinary normalized-HS stability, but it means a proof of this claim cannot
proceed by first establishing a local version and globalizing -- the local
version is unavailable on the hypothesis that would make globalizing
interesting.

**Where this claim sits in the formalization.**  By
`pointwise-hs-stability-from-no-hyperlinear-quotient`, this claim is exactly
the missing hypothesis of a third instance of a pattern already proved twice
in `GroupApproximation/Stability/MixedApproximation.lean`, for the Hamming
and operator-norm metrics.  The mathematics of the implication is three
lines; the only missing Lean ingredient is that the unitary group of a
tracial matrix ultraproduct is hyperlinear.  All the difficulty is in the
hypothesis, none of it in the deduction.

**A cheap consistency test that has not been run.**  By
`kervaire-laudenbach-holds-for-hyperlinear`, the Kervaire--Laudenbach
property holds for every hyperlinear group -- Nitsche--Thom, *Universal
solvability of group equations*, J. Group Theory 25 (2022) 1--10,
**Theorem 1.2** (attributed by them to Gerstenhaber--Rothaus and Pestov);
their Theorem 1.3 is the stronger covering result which implies it, and is
the number the OpenAI chapter cites.  So if this claim is false, every
one-variable equation over `Q` with nonzero total exponent is solvable in
some overgroup.  The Leavitt unit group is concrete enough for equations
over it to be testable, so positive KL evidence accumulates *against* this
claim cheaply.  The converse use is the open node
`kl-violating-equation-over-leavitt-unit-group` with its route
`kl-violation-refutes-hyperlinearity-route`; see that node's own difficulty
paragraph before spending on it, since a KL-violating equation would also
refute the Kervaire--Laudenbach conjecture and is therefore a red flag on
any candidate rather than a plan.

**Character rigidity cannot be the engine, for a structural reason.**
The higher-rank technology (Dogon--Vigdorovich Theorem 1.6; Lavi--Levit,
arXiv:2007.15547, Adv. Math. 419 (2023) 108948) routes stability through
character rigidity.  That is substantive for a lattice, which has many
characters.  It is empty for `Q=EL_4(L_(F_2)(1,2))`, because simplicity
already forces every nontrivial homomorphism into a tracial matrix
ultraproduct to be faithful: nothing remains for a character classification
to rule out.  Separately, Lavi--Levit assume `R` commutative Noetherian and
`d` above the stable range, and a literature sweep on 2026-08-14 found **no**
character-rigidity theorem for `EL_n` over a noncommutative ring; the
binary Leavitt algebra is noncommutative, non-Noetherian and of infinite
Bass stable rank.  So this lane is closed both by hypothesis mismatch and
by vacuity.

**Where the branch is actually decided.**  The only mechanism that has ever
closed a question of this shape for this group is the one that proved `Q`
nonsofic: Kun's expander decomposition, a conservation identity, and a
majority matching.  Transcribing it to the normalized-HS metric needs
exactly one new input, `hs-expander-block-decomposition`; the other two
steps do transcribe, and the transcription is written out in
`hs-block-decomposition-to-steinberg-stable`.  That route is currently the
sharpest formulation of what proving this claim requires.
