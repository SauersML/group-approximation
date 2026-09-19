---
rg: 2
id: fpbs-ray-code-deaths-depend-only-on-the-current
kind: claim
title: For a quasi-geodesic ray code with a finite invariant measure on a hyperbolic group, whether the backward-locally-finite death applies is decided by the invariant current mu_R, not by the code relation R; quasiconvex-nullness does not force a locally finite current (the geodesic-flow Markov code of a cocompact Sp(n,1) lattice accumulates everywhere), so a surviving ray-code BB certificate needs an essentially accumulating current over a Dini-singular class
distinct_from:
  fpbs-backward-locally-finite-ray-codes-die: that assumes local finiteness (LF) and nullity (NF) of the set R of all code lines. Here the hypotheses are a.e. conditions on the Gamma-invariant Radon current mu_R carried by R, which ignores null sets of positions. Theorem 1 derives that theorem's hypotheses on a conull invariant restriction, and Corollary 2 shows the current conditions are also necessary for any restriction to satisfy them, so the dichotomy is exact.
  fpbs-dini-boundary-class-diagonal-dissipative: that kills classes by their size. This node shows that size, not quasiconvex-nullness, is what kills the one natural code whose current accumulates (the Markov code of the geodesic flow), so the two filters are complementary and neither implies the other.
---

**ESTABLISHED (written proof: `research/fpbs-ray-code-deaths-depend-only-on-the-current-proof.md`).** The proof uses
the fundamental-domain construction of the current, disintegration of sigma-finite measures, the restriction clause
of `fpbs-backward-locally-finite-ray-codes-die`, Bowen's Markov partitions for Anosov flows, the growth gap of
Dahmani--Futer--Wise for quasiconvex subgroups, and the Dini filter.

**Why this matters for the flagship.** For a cocompact `Sp(n,1)` lattice (property (T), fixed price open), the
Bevilacqua--Bowen (BB) route needs an amenable ergodic PDR imp action whose boundary class passes the Dini, shadow
and quasiconvex-null filters. The ray-code line builds candidate classes from codes.
`fpbs-backward-locally-finite-ray-codes-die` killed every code whose code relation `R` has backward sections
accumulating only at their forward point, and named the open statement **accumulating backward sections on a
lattice**. The proposed test was a Borel--Cantelli count against the current `mu_R`, aiming to show that
quasiconvex-nullness forces `mu_R` to be carried by a locally finite set, which would close the ray-code route.

This node settles that test, in both directions.
- **The right object is the current.** For codes with a finite invariant measure, the death theorem holds under
  a.e. conditions on `mu_R` (Theorem 1), and these conditions are exactly what any conull restriction of the code
  needs (Corollary 2). "Accumulating backward sections" is replaced by the precise, restriction-invariant notion
  **essential accumulation of the current**.
- **The closure fails.** Quasiconvex-nullness does not force a locally finite current. The Markov code of the
  geodesic flow of a compact quaternionic hyperbolic manifold is a uniformly quasi-geodesic code with an invariant
  probability measure, an ergodic, nonatomic, quasiconvex-null class, and a current whose backward conditionals are
  nonatomic at a.e. point (Theorem 3). Its diagonal dies, but by the Dini filter, not by any property of `R`.
- **What survives is sharp.** A ray-code BB certificate with a finite invariant measure needs an essentially
  accumulating current *and* a Dini-singular class (Corollary 5). At zero entropy the past of a code line is a
  function of its forward word (Proposition 4), so essential accumulation needs forward words with a common endpoint
  whose pasts, and not only whose spellings, differ.

## Setting

As in `fpbs-backward-locally-finite-ray-codes-die`: `Gamma` hyperbolic with finite generating set `S`, positions
`p ∈ X^#`, refined paths `P_p` with `P_p(0) = 1`, (UQ) with constants `(lambda, c)`, endpoints `zeta^{-#}(p)`,
`zeta^#(p)`, code relation `R ⊂ dGamma^2 \ Delta`. In addition `rho^#` is a finite `T^#`-invariant measure on `X^#`
(for instance induced by a `T`-invariant probability with integrable spelling length).

**The current.** `mu_R` is the image of `(rho^# x count)|_D` under `(p, g) -> g (zeta^{-#}(p), zeta^#(p))`, where `D`
is a fundamental domain of the skew product `(p, g) -> (T^# p, g P_p(1))` (proof, Step 1). It is a `Gamma`-invariant
Radon measure on `dGamma^2 \ Delta` carried by `R`. Its forward and backward marginal classes are the forward code
class `nu` and the backward code class `nu^-` (the classes of `sum_g 2^{-|g|} g_* zeta^{±#}_* rho^#`).

**Conditionals.** Disintegrate `mu_R` over the forward coordinate: `mu_R = ∫ mu^eta d nu_1(eta)` with `nu_1` a finite
measure in `nu`, and `mu^eta` a sigma-finite measure on `dGamma \ {eta}`, finite on each `K_r(eta) =
{theta : (theta|eta)_o <= r}`.
- **(LF_mu)** For `nu`-a.e. `eta`, `mu^eta` is purely atomic and has finitely many atoms in each `K_r(eta)`.
- **Essential accumulation** is the failure of (LF_mu) on a `nu`-positive set.

## Results

**Theorem 1 (the current decides).** Assume (UQ), a finite invariant `rho^#`, a nonatomic backward class `nu^-` and
(LF_mu). Then there is a conull `T`-invariant Borel set `X_1` whose restricted code has the same class `nu` and a code
relation `R_1 ⊂ R` satisfying (LF) and (NF). Hence, by `fpbs-backward-locally-finite-ray-codes-die`, every imp action
`Z` with a boundary map into `nu` has totally dissipative diagonal, and no ergodic such `Z` is PDR.

**Corollary 2 (exact dichotomy).** Under (UQ) and a finite invariant `rho^#` with `nu^-` nonatomic, exactly one holds:
1. (LF_mu): some conull restriction satisfies (LF) and (NF), and the class dies by Theorem 1;
2. essential accumulation: for **every** conull `T`-invariant Borel `X_1`, the code relation `R_1` has, for
   `nu`-positively many `eta`, backward sections `R_1^eta` accumulating at a point `theta ≠ eta`.

**Theorem 3 (quasiconvex-null does not force a locally finite current).** Let `Gamma` be a cocompact lattice in
`Sp(n,1)`, `n >= 2` (the argument works in any rank-one symmetric space). There is a uniformly quasi-geodesic ray code
on `Gamma` with an invariant probability measure, whose class is the Lebesgue class of `dGamma = S^{4n-1}`: ergodic,
nonatomic and quasiconvex-null. Its relation is `R = dGamma^2 \ Delta` up to a countable set of pairs, its current is
equivalent to the Liouville current, and a.e. conditional `mu^eta` is equivalent to Lebesgue measure. So it is
essentially accumulating at a.e. point. Its crossing diagonal (for every imp action over the class) is totally dissipative, and no ergodic such action is PDR, by the Dini filter
(`fpbs-dini-boundary-class-diagonal-dissipative`, Theorem B) and not by any property of `R`.

**Proposition 4 (zero entropy: the future word determines the past).** If `rho^#` is a `T^#`-invariant probability
of zero entropy, then `zeta^{-#}(p)` is, for `rho^#`-a.e. `p`, a measurable function of the forward `S`-word of `p`.
So `mu^eta` is the image, under this function, of the conditional law of forward words from a finite ball given
the forward endpoint `eta`. Essential accumulation at zero entropy therefore needs, over `nu`-positively many
`eta`, an infinite family of forward words with endpoint `eta` from a finite ball (nonatomic, or with infinitely many atoms) whose determined pasts have infinitely many distinct endpoints.
Respellings (Theorem 3 of `fpbs-backward-locally-finite-ray-codes-die`) never do this.

**Corollary 5 (what a surviving ray-code certificate must look like).** Let `Gamma` be a cocompact `Sp(n,1)` lattice
and let a (UQ) ray code with a finite invariant measure and nonatomic backward class carry the boundary class of a BB
certificate. Then its current is essentially accumulating, and the boundary class of the certificate is singular to every Dini measure (so every
measure in it has lower local dimension zero a.e.). Theorem 3 shows the first condition alone is compatible with
quasiconvex-nullness; the example violating the second is exactly the one that dies.

## Calibration

- **Lattice odometer codes and their respellings.** (LF_mu) holds (the relation is already (LF)); they die, as before.
- **Surface groups, Bowen--Series or Markov code.** Essential accumulation, Lebesgue class; conservative on
  `dGamma^2` but the Maharam diagonal is dissipative, consistent with cost `> 1`.
- **Codes without a finite invariant measure** have no current; Theorem 1 of the previous node still applies to them
  directly, and this node says nothing new about them.

## What this leaves (named open statement)

**Essentially accumulating Dini-singular code currents.** On a cocompact `Sp(n,1)` lattice, is there a (UQ) ray code
with a finite invariant measure whose class is quasiconvex-null and singular to every Dini measure, whose current is
essentially accumulating, and over whose class some imp action has a conservative diagonal? By Proposition 4 and
Proposition 4 of the previous node, a zero-entropy candidate has a dimension-zero class automatically, and must
realise essential accumulation by forward-word fibres that move the past. The first concrete test is a zero-entropy
code built from an asymptotic-pair structure of a Toeplitz system: infinitely many left-extensions of one right ray
whose group paths diverge in the past.
