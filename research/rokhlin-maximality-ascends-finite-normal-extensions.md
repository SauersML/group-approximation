---
rg: 2
id: rokhlin-maximality-ascends-finite-normal-extensions
kind: claim
title: If N is a finite normal subgroup of W and W/N is Rokhlin-maximal, then W is Rokhlin-maximal
distinct_from:
  rokhlin-maximality-ascends-amenable-normal-extensions: that allows every amenable kernel and would reach the Kun–Thom wreath; this is its finite-kernel case, where the obstruction is the extension class rather than Følner counting along the kernel.
  rokhlin-maximality-descends-along-finite-normal-quotients: that is the proved descent from W to W/N; this is the open ascent from W/N to W.
  finite-normal-subgroups-do-not-affect-surjunctivity: that transfers surjunctivity across finite kernels; this transfers maximal Bernoulli Rokhlin entropy, which gives surjunctivity of W whenever W/N is maximal.
artifacts:
  - research/artifacts/rokhlin-finite-kernel-ascent-equivalence-2026-09-13.md
  - research/artifacts/rokhlin-finite-kernel-quotient-formula-2026-09-13.md
---

**OPEN.** Let `W` be countably infinite and `N ◁ W` finite. If `W/N` is Rokhlin-maximal at every `q`, then so is
`W`.

**Why it matters.**
- **Deligne's triple cover.** `Sp_4(Z)` is residually finite, hence sofic and maximal. This claim would make `E_3`
  maximal. By Seward's Corollary 4.1 it would then be surjunctive and satisfy Kaplansky's direct finiteness
  conjecture, settling `deligne-triple-cover-surjunctive` positively. That would be a Rokhlin lower bound over a
  group whose soficity is open.
- **Surjunctivity across finite kernels.** For every maximal quotient it gives surjunctivity of the extension,
  inside the finite residual too. That is the open direction of `finite-normal-subgroups-do-not-affect-surjunctivity`
  there.
- **Rigid extensions.** Gohla–Thom central extensions (`gohla-thom-stable-base-nonsofic-extension`) are nonsofic under
  their hypotheses, and they have residually finite quotients. They would be maximal: a Rokhlin lower bound over a
  nonsofic group.
- **The converse holds.** `rokhlin-maximality-descends-along-finite-normal-quotients`.

**Pair by pair.** For finitely generated `Q = W/N`, ascent for one pair is equivalent to
`sup_k h^Rok_Q(Ω/N × ((A^k)^N)^Q) = ∞`, where `Ω/N` is the twisted section action
(`rokhlin-finite-kernel-ascent-iff-liftable-entropy-unbounded`).

## Attempts

- **Reductions (ex-rokhlin-ascent-finite-kernel, 2026-09-13; artifact Section 4).**
  - The centralizer of `N` has finite index, and induction on `|N|` passes through central subgroups. So central
    kernels of prime order suffice.
  - By the Kaloujnine–Krasner embedding, `W <= C ⋊ Q` with `C` locally finite. So the split, locally finite case of
    `rokhlin-maximality-ascends-amenable-normal-extensions` implies this claim.
- **The kernel costs nothing.** For free ergodic `X`,
  `n h^Rok_W(X) <= h^Rok_Q(X/N) <= n h^Rok_W(X) + r log n`
  (`rokhlin-entropy-quotient-formula-for-finite-normal-subgroups`). So any liftable free action of `Q` with large
  finite entropy gives one for `W`. The problem is to find liftable actions whose large entropy is known.
- **Known entropy through weak containment.**
  - Bernoulli shifts over `Q` have known entropy, but they lift only if the extension class dies on their orbit
    relation.
  - Products `Y_0 × L^Q` of a liftable `Y_0` with Bernoulli shifts always lift. They have entropy at least `H(L)`
    when `Y_0` is weakly contained in all free actions (`finite-kernel-rokhlin-ascent-from-weakly-minimal-lift`).
- **Bernoulli lifting is dead over w-rigid quotients.** `bernoulli-lifts-across-finite-kernels-force-virtual-splitting`:
  by Popa's cocycle superrigidity, a Bernoulli shift of a w-rigid `Q` lifts only when the extension virtually
  splits. There ascent is already a finite-index statement. In particular no Bernoulli shift of `Sp_4(Z)` lifts to
  Deligne's `E_3`.
- **Property MD gives ascent, but misses higher rank.** Let `Q` be residually finite with property MD (a finitely
  modular action weakly contains every action).
  - Seward's Corollary 8.8 in arXiv:1602.06680v2, with a sofic approximation through finite quotients and
    `X = L^Q`, gives `h_Q(L^Q × Y | B(Y)) = H(L)` for every p.m.p. `Y`.
  - Case (iii) of `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift`, with `Y = Ω/N`, then makes every finite
    extension of `Q` maximal.
  - The same paper records that `SL_n(Z)` has MD exactly when `n = 2`, since MD needs property FD. So this does not
    reach Deligne-type extensions.
  - The known MD groups are good in Serre's sense and have no persistent classes. Their finite central extensions
    virtually split.

  Weak containment of `Ω/N` in finite actions probably already gives soficity of `W`, by reading approximate lifts
  on finite quotients. This was not written out. Artifact Section 7.
- **Where it dies (mechanism analysis, artifact Section 5).**
  - The canonical liftable action is the twisted section action `Ω/N`. Weak containment of `Ω/N` in Bernoulli shifts
    asks for an approximate trivialization of the extension class on Bernoulli orbit relations of `Q`.
  - For rigid extensions of Gohla–Thom type, their obstruction is nonzero on actions weakly contained in finite
    actions.
  - No lower-bound tool without finite models other than weak containment appears in the sources read.
- **What a counterexample needs** (proved constraints). A pair where ascent fails has all of these:
  - `W` is nonsofic;
  - the extension is non-split over every infinite co-amenable subgroup of `Q`;
  - no liftable free action of finite entropy is weakly contained in all free `Q`-actions, and no Bernoulli shift of
    `Q` lifts;
  - `seward-direct-product-relative-rokhlin-entropy-conjecture` fails over `Q`, with
    `h^Rok_Q(Ω/N × ((A^k)^N)^Q)` bounded in `k`. So the small twisted action absorbs the entropy of arbitrarily
    large Bernoulli shifts.
- **Følner windows along `N` are not the issue.** The `N`-quotient carries all the entropy. The coherent-window
  analysis on `rokhlin-maximality-ascends-amenable-normal-extensions` leaves finite and central kernels open for the
  same reason: there the extension class, not the kernel, is the obstruction.
