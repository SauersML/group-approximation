---
rg: 2
id: fpbs-backward-locally-finite-ray-codes-die
kind: claim
title: On any hyperbolic group (in particular a cocompact Sp(n,1) lattice), a uniformly quasi-geodesic ray code whose code relation R of (backward, forward) endpoint pairs is backward locally finite (each section R^eta accumulates only at eta) and forward null carries no class with a conservative diagonal, of any entropy and any spelling multiplicity; zero-entropy lattice codes with continuum spelling multiplicity exist and die this way, so a ray-code BB certificate needs accumulating backward sections
distinct_from:
  fpbs-finite-to-one-quasigeodesic-ray-codes-die: that assumes finite forward fibres of positions (FT) and countable backward fibres (CT), which are properties of the coding. This assumes only local finiteness and nullity of the code relation R, a Gamma-invariant subset of the space of boundary pairs that ignores spellings. (FT) implies local finiteness and (CT) implies nullity, so that theorem is the special case; this one also kills codes with infinite, even continuum, spelling multiplicity, and positive-entropy codes, which that theorem leaves open.
  fpbs-zero-entropy-ray-codes-are-support-rigid: that kills zero-entropy codes inside a free subgroup through two-sided injectivity of the coding and stops at positive entropy. This uses no entropy at all; entropy is not the invariant that decides the diagonal.
  fpbs-dini-boundary-class-diagonal-dissipative: that kills classes of positive dimension. Proposition 4 here shows every zero-entropy code class has local dimension zero, so the dimensional form of the Dini filter never sees the zero-entropy branch; this theorem does.
---

**ESTABLISHED (written proof: `research/fpbs-backward-locally-finite-ray-codes-die-proof.md`).** The proof uses the
Morse lemma, compactness of `Gamma ∪ dGamma`, a pigeonhole on finite balls and the Fubini/recurrence step of
`fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups`. It checks and reuses the freezing step of
`fpbs-finite-to-one-quasigeodesic-ray-codes-die`, with the fibre of positions replaced by a section of `R`.

**Why this matters for the flagship.** For a cocompact `Sp(n,1)` lattice `Gamma` (property (T), fixed price open),
the Bevilacqua--Bowen (BB) route needs an amenable ergodic PDR imp action whose boundary class passes the Dini, shadow
and quasiconvex-null filters. The ray-code line builds such classes from codes. The previous step
(`fpbs-finite-to-one-quasigeodesic-ray-codes-die`) killed codes with finite endpoint fibres and named the open
statement **infinite spelling multiplicity on a lattice**: is there a zero-entropy, quasi-geodesic, quasiconvex-null
code with infinitely many forward words from `1` sharing an endpoint on a positive-measure set, and a conservative
diagonal? It also asked about the positive-entropy route with lower local dimension zero.

This claim settles both questions as posed, and replaces them by the one statement that remains.
- **Construction half: yes, and it is useless.** Such codes exist on every cocompact `Sp(n,1)` lattice, with
  *continuum* spelling multiplicity on a set of full measure (Theorem 3). Their classes die.
- **The deciding invariant is not the spelling.** It is the **code relation** `R`: the `Gamma`-saturated set of pairs
  (backward endpoint, forward endpoint) of code lines. Theorem 1 kills every class when each section
  `R^eta = {theta : (theta, eta) ∈ R}` accumulates only at `eta` and each forward section is null. Spelling
  multiplicity multiplies positions without changing `R`.
- **Entropy is not the invariant either.** Theorem 1 uses no invariant measure and no entropy, so it kills
  positive-entropy codes too, including those of lower local dimension zero, unless their backward sections
  accumulate. Proposition 4 shows the zero-entropy branch always has local dimension zero, so size filters cannot
  help there.

## Setting

As in `fpbs-finite-to-one-quasigeodesic-ray-codes-die`: `Gamma` hyperbolic with finite generating set `S`;
`(X_0, T)` aperiodic Borel; letters `G(x) ∈ Gamma \ {1}`; each letter spelled by a nonempty `S`-word
`sigma_x(G(x+1))`, which may now depend Borel on `x` and not only on the letter. Positions `p ∈ X^#`, refined paths
`P_p` with `P_p(0) = 1`, (UQ) with constants `(lambda, c)`, and endpoints `zeta^#(p)`, `zeta^{-#}(p)`.

**Code relation.** `R = {(g zeta^{-#}(p), g zeta^#(p)) : p ∈ X^#, g ∈ Gamma} ⊂ dGamma^2 \ Delta`. It is analytic and
`Gamma`-invariant. Sections: `R^eta = {theta : (theta, eta) ∈ R}` (backward), `R_theta = {eta : (theta, eta) ∈ R}`
(forward). `R^eta` is the set `B(eta)` of the previous node.

Let `nu` be a quasi-invariant class carried by `Gamma zeta(X_0)`, nonatomic.
- **(LF) backward local finiteness.** For `nu`-a.e. `eta`, every accumulation point of `R^eta` in `dGamma` is `eta`.
  Equivalently, `{theta ∈ R^eta : (theta|eta)_o <= r}` is finite for every `r`. (Then `R^eta` is countable.)
- **(NF) forward nullity.** `nu(R_theta) = 0` for every `theta ∈ dGamma`.

Both are properties of `R` and `nu` only: two codes with the same code relation satisfy them together.

## Results

**Theorem 1 (backward-locally-finite codes die).** Assume (UQ), (LF) and (NF). Let `(Z, mu_Z)` be an imp `Gamma`-space
with a measurable equivariant `xi : Z -> dGamma` such that `xi_*(mu_Z|_E) << nu` for every `E` of finite measure. Then
`Gamma` acts totally dissipatively on `(Z x Z, mu_Z x mu_Z)`. No ergodic such `Z` is PDR. The class `nu`, its Maharam
extension and every imp action over it are not the boundary class of a BB certificate, whatever the entropy, Krieger
type, dimension and shadow sum. The hypotheses may be checked on a `T`-invariant Borel set carrying the code measure.

**Proposition 2 (the previous theorem is the special case).** (FT) implies (LF) for every `eta`, and (CT) implies
(NF) for every nonatomic `nu`. So Theorem 1 contains Theorem 1 of `fpbs-finite-to-one-quasigeodesic-ray-codes-die`.

**Theorem 3 (continuum spelling multiplicity exists on lattices and dies).** Let `Gamma` be a cocompact `Sp(n,1)`
lattice, `n >= 2`. There is a zero-entropy, uniformly quasi-geodesic ray code on `Gamma`, with an invariant
probability measure, whose class is ergodic, nonatomic and quasiconvex-null, such that for a.e. position `p` the
fibre `(zeta^#)^{-1}(zeta^#(p))` contains **uncountably many** positions with pairwise distinct forward words from
`1`. So (FT) fails on every conull set, and by Corollary 3 of the previous node this is infinite spelling multiplicity.
Its class has totally dissipative diagonal by Theorem 1.

The code is the lattice odometer code of `fpbs-quasiconvex-null-lattice-odometer-class-dies`, respelled by a Toeplitz
choice: a split generator `s = s_1 s_2` is written as `s` or as `s_1 s_2` according to a 2-adic digit. The group path
at letter boundaries is unchanged, so `R` and the class are unchanged.

**Proposition 4 (zero entropy gives local dimension zero).** Let `rho^#` be a `T^#`-invariant probability measure on
`X^#` of zero entropy, with (UQ). Then every measure in the class `nu = sum_g c_g g_* zeta^#_* rho^#` has local
dimension `0` (upper and lower, for a visual metric) at `nu`-a.e. point. So the zero-entropy branch passes every
positive-dimension test, and Theorem C of `fpbs-dini-boundary-class-diagonal-dissipative` never applies to it.

## Calibration

- **Surface group, Lebesgue class.** Conservative diagonal (Hopf--Tsuji--Sullivan). The Bowen--Series code has
  `R^eta = dGamma \ {eta}` up to null sets: every past is compatible. (LF) fails, as it must.
- **`F_2`, odometer and rotation codes; lattice odometer codes.** (FT), (CT) hold off a countable set, hence (LF), (NF).
  Theorem 1 reproduces their deaths.
- **`Z` (elementary, excluded).** A code on `<a>` has `R = {(a^{-∞}, a^{+∞})}` and an atomic class; no conclusion is
  claimed.

## What this leaves (named open statement)

**Accumulating backward sections on a lattice.** On a cocompact `Sp(n,1)` lattice, is there a uniformly quasi-geodesic,
quasiconvex-null ray code whose code relation has, for `nu`-positively many `eta`, backward sections `R^eta`
accumulating at a point `theta ≠ eta`, with a conservative diagonal? By Theorem 1 every ray-code BB certificate, of
any entropy, has this feature (or violates (NF)). Concretely, at a conservative pair `(eta, eta')`, returns force
infinitely many distinct code lines through one finite ball, all ending at `eta`, whose backward endpoints converge
to a common `theta ∈ cl(R^eta) ∩ cl(R^{eta'})`. A Borel--Cantelli count over such accumulations, using the
`Gamma`-invariant Radon current carried by `R` (proof, Remark 7.2), is the natural next test.
