---
rg: 2
id: fpbs-finite-to-one-quasigeodesic-ray-codes-die
kind: claim
title: On any hyperbolic group (in particular a cocompact Sp(n,1) lattice), a uniformly quasi-geodesic Borel ray code whose position-to-endpoint map is finite-to-one forward and countable-to-one backward carries no class with a conservative diagonal, whatever its off-orbit matches; so off-orbit matches, transverse or not, never rescue a ray-code BB certificate, and a survivor needs infinite endpoint fibres (for invariant measures, positive entropy or infinite spelling multiplicity)
distinct_from:
  fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups: that needs match rigidity (MR), i.e. no off-orbit match g zeta(x) = zeta(x') at all, and leaves codes with off-orbit matches open. This allows off-orbit matches on all of X_0 and replaces (MR) by finiteness of the endpoint fibres. For uniformly quasi-geodesic codes, (MR) implies the new hypothesis, so that theorem is the special case with fibres of bounded size inside one orbit.
  fpbs-transverse-skeleton-ray-codes-are-match-rigid: that proves (MR) for skeleton codes whose insertions satisfy the transversality (I1) and names non-transverse insertions with off-orbit matches as the only escape. This kills the non-transverse skeleton codes too, whenever their endpoint fibres are finite; no transversality and no skeleton subgroup is used.
  fpbs-dini-boundary-class-diagonal-dissipative: that kills classes by their size (a convergent shadow-product sum). This uses no size estimate. It kills classes of dimension zero and with divergent shadow sums, provided they are carried by a finite-to-one quasi-geodesic code.
---

**ESTABLISHED (written proof: `research/fpbs-finite-to-one-quasigeodesic-ray-codes-die-proof.md`).** The proof uses
the Morse lemma, compactness of `Gamma ∪ dGamma`, a pigeonhole on finite balls, and the Fubini/recurrence step of
`fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups`. It needs no torsion-freeness, no trivial stabilizers, no
carrying subgroup and no measure on the base.

**Why this matters for the flagship.** For a cocompact `Sp(n,1)` lattice `Gamma` (property (T), fixed price open), the
Bevilacqua--Bowen (BB) route needs an amenable ergodic PDR imp action. Its boundary class must pass the Dini, shadow
and quasiconvex-null filters. The odometer line built such classes from ray codes. It found that match rigidity kills
them (`fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups`, `fpbs-transverse-skeleton-ray-codes-are-match-rigid`).
The step left open was: build a quasiconvex-null code with **positive-measure off-orbit matches** through
non-transverse insertions, or kill that class.

This claim kills it, in a stronger form. Off-orbit matches are not the relevant invariant. The diagonal is decided by
the **size of the endpoint fibres of positions**. If every endpoint is reached from a given base point by only
finitely many code positions, the diagonal is totally dissipative, with or without off-orbit matches. So:
- non-transverse insertions that create off-orbit matches, even on all of `X_0`, give nothing unless they also make
  endpoint fibres infinite;
- a ray-code BB certificate on a lattice must have **infinite forward endpoint fibres** (or uncountable backward ones)
  on a non-null set of positions.

For invariant measures this is sharp in a concrete sense (Corollary 3). Infinite fibres come either from positive
entropy (then the future does not determine the position) or from **infinite spelling multiplicity**: infinitely many
distinct forward words from one base point with a common endpoint.

## Setting

`Gamma` is hyperbolic, with finite symmetric generating set `S` and `delta`-hyperbolic Cayley graph. `(X_0, T)` is an
aperiodic Borel automorphism, and we write `x + t = T^t x`. The letters `G : X_0 -> Gamma \ {1}` are Borel. Each letter
`s` has a fixed spelling `sigma(s)`, a nonempty word in `S` representing `s`, chosen Borel in `s` (shortlex geodesic,
say; geodesic spellings are not needed). Write `|s|_sigma` for its length.

- **Positions.** `X^# = {(x, i) : x ∈ X_0, 0 <= i < |G(x+1)|_sigma}`, with the obvious successor map `T^#`. The position
  `(x, i)` sits `i` letters of `S` into the spelling of `G(x+1)`.
- **Refined path.** For `p = (x, i)`, read from `1` forward the rest of `sigma(G(x+1))`, then `sigma(G(x+2))`, and so on.
  Read backward the first `i` letters of `sigma(G(x+1))` inverted, then `sigma(G(x))` inverted, and so on. This gives a
  bi-infinite word in `S` and a bi-infinite path `P_p` in the Cayley graph with `P_p(0) = 1`.
- **(UQ) uniform quasi-geodesics.** There are `lambda, c` such that every `P_p` is a `(lambda, c)`-quasi-geodesic.
  Then `P_p` has distinct endpoints: `zeta^#(p) = lim_{t -> +∞} P_p(t)` and `zeta^{-#}(p) = lim_{t -> -∞} P_p(t)`.
  At `p = (x, 0)` these are the rays `zeta(x) = G(x+1) G(x+2) ...` and `zeta^-(x) = G(x)^{-1} G(x-1)^{-1} ...` of
  `fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups`. Also `zeta^#(x, i) = u^{-1} zeta(x)` for the prefix `u` of
  length `i`, so `Gamma zeta^#(X^#) = Gamma zeta(X_0)`.
- **(FT) finite forward fibres.** `zeta^# : X^# -> dGamma` is finite-to-one.
- **(CT) countable backward fibres.** `zeta^{-#} : X^# -> dGamma` is countable-to-one.

Only (FT) and (CT) replace (MR). An off-orbit match `g zeta(x) = zeta(x')`, `x' ∉ x + Z`, is allowed everywhere.

## Theorem

**Theorem 1 (finite fibres kill every class on the rays).** Assume (UQ), (FT) and (CT). Let `(Z, mu_Z)` be an imp
`Gamma`-space with a measurable equivariant `xi : Z -> dGamma`, such that `xi_*(mu_Z|_E)` is nonatomic and carried by
`Gamma zeta(X_0)` for every `E` of finite measure. Then `Gamma` acts totally dissipatively on `(Z x Z, mu_Z x mu_Z)`.
So no ergodic such `Z` is PDR. Every class `nu_rho = sum_g c_g g_* zeta_* rho` with `zeta_* rho` nonatomic dies,
together with its Maharam extension and every imp action over it, whatever its Krieger type, its dimension and its
shadow sum. None of them is the boundary class of a BB certificate.

The hypotheses may be checked on a `T`-invariant Borel set that carries `rho`. Restricting `X_0` changes neither the
class nor the conclusion.

**Mechanism (the whole proof in four lines).**
- Take distinct joint returns `g_n`, with `g_n eta = h zeta(y_n)` and `g_n eta' = h' zeta(y'_n)`, and let `g_n^{-1}`
  converge to `theta ∈ dGamma`.
- The code ray from `g_n^{-1}` to `eta` (and the one to `eta'`) passes within a fixed distance `R` of a fixed point of
  the geodesic `(eta, eta')`. Pigeonhole on that finite ball, then (FT) on the finite fibre, freezes the position.
- So `g_n^{-1}` runs down the **backward** half of one fixed code line, and `theta` is its backward endpoint.
- Hence `theta` is a backward endpoint attached to `eta` and also to `eta'` (or equals one of them). By (FT) and (CT)
  this happens only on a relation with countable sections, which is null for nonatomic product measures.

## Corollaries

**Corollary 2 (match rigidity is the bounded-fibre special case).** Let `Gamma` be torsion-free and assume (UQ), (MR)
and (MR±) of `fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups`. Off a countable invariant set, each fibre of
`zeta^#` lies on one code line and has at most `2 lambda c + 1` points, and each fibre of `zeta^{-#}` is countable. So
(FT) and (CT) hold there. Theorem 1 therefore contains Theorem 1 of
`fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups` for uniformly quasi-geodesic codes. It also contains the
conclusion of `fpbs-transverse-skeleton-ray-codes-are-match-rigid` for injective transverse skeleton codes.

**Corollary 3 (invariant measures: entropy or spelling multiplicity).** Let `rho^#` be a finite `T^#`-invariant
ergodic measure on `X^#` (for instance the tower measure of an invariant `rho` with `∫ |G| d rho < ∞`), and suppose
the two-sided `S`-coding of positions is injective. Let `pi^+(p)` be the forward word of `p`. Then:
1. if `h(T^#, rho^#) > 0`, the fibres of `pi^+` are infinite on a set of positive measure, so (FT) fails;
2. if `h(T^#, rho^#) = 0`, then `pi^+` and `pi^-` are injective on an invariant conull set. So (FT) and (CT) there are
   equivalent to **finite spelling multiplicity**: only finitely many forward words in the support, read from `1`,
   share an endpoint, and only countably many backward words do.

So a ray-code BB certificate over an invariant zero-entropy code (every odometer, rotation and skeleton code of the
earlier nodes) needs infinitely many distinct forward words from one base point converging to one boundary point, on
a set of positive measure.

**Corollary 4 (the lattice step).** Let `Gamma` be a cocompact `Sp(n,1)` lattice. A quasiconvex-null ray code on
`Gamma` with off-orbit matches on a set of positive measure, built from non-transverse insertions or in any other way,
carries no BB boundary class if it satisfies (UQ), (FT) and (CT). No torsion-free passage is needed.

## Calibration

- **Recoding example (off-orbit matches everywhere, still dead).** Take the lattice odometer code of
  `fpbs-quasiconvex-null-lattice-odometer-class-dies` on `Omega`, and a second copy `Omega x {1}`. On the second copy
  merge each insertion `s_j` with the whole preceding `F`-run `w` into one letter `w s_j`, spelled `sigma(w) sigma(s_j)`.
  These merged insertions contain `F`-stretches of unbounded length, so (I1) fails for every `D`. Every point of the
  second copy has an off-orbit match (with `g = 1`) in the first copy, so (MR) fails on a set of measure `1/2`.
  Neither earlier theorem applies. The refined paths of the two copies coincide. By Corollary 2 applied to the first
  copy (match-rigid and symmetric by that node), the position fibres have at most `2(2 lambda c + 1)` points off a
  countable set, and Theorem 1 kills the class. So off-orbit matches are a property of the code, not of the class:
  recoding creates them.
- **Surface groups, Lebesgue class.** The diagonal is conservative (Hopf--Tsuji--Sullivan). So every uniformly
  quasi-geodesic code carrying Lebesgue measure has infinite forward or uncountable backward fibres. This is what
  happens: in the natural extension of the Bowen--Series map, the endpoint depends only on the future, and the fibres
  are all compatible pasts, a continuum. The entropy is positive, as item 1 of Corollary 3 requires.
- **`F_2`, Bernoulli sign code.** Positive entropy gives continuum fibres. The theorem is silent, and the harmonic class
  is killed separately as a Dini class.
- **`F_2`, odometer and rotation codes.** Reduced words give spelling multiplicity one, and zero entropy gives injective
  codings. Theorem 1 reproduces the deaths recorded in `fpbs-odometer-killing-class-dies-by-support-rigidity`.

## What this leaves (named open statement)

**Infinite spelling multiplicity on a lattice.** On a cocompact `Sp(n,1)` lattice, is there a zero-entropy,
uniformly quasi-geodesic, quasiconvex-null ray code such that, on a set of positive measure, infinitely many distinct
forward words from `1` converge to the same boundary point, and whose class has a conservative diagonal? By Theorem 1,
every ray-code certificate with an invariant zero-entropy base must have this feature. Alternatively, a positive-entropy
code must avoid the Dini filter, i.e. have lower local dimension zero while its future does not determine its past.
The fibre geometry is also explicit: at a conservative pair, infinitely many base points `g^{-1}` lie on backward
halves of distinct code lines through one finite ball, whose backward endpoints accumulate at a common point.
