---
rg: 2
id: common-corner-mutual-bicommutant-extraction
kind: claim
title: Two transverse robust packets exactify as mutual commutants on one positive-density corner
artifacts:
  - research/artifacts/nonhyperlinear-breakout-portfolio-2026-08-21.md
distinct_from:
  full-packet-bicommutant-synchronization: that starts with one raw packet and asks every unitary in its coordinate commutant to commute with one transported carrier; this recovers two named word-generated packet algebras and identifies each as the full commutant of the other.
  tensor-independent-child-carrier-gap: that gives an analytic distance floor once two trace-independent child algebras and one common carrier are supplied; this is the finite-dimensional perturbation theorem intended to identify the physical tensor factors before applying such a floor.
  paired-same-reservoir-boundary-lemma: that follows a compressor branch and charges leaving one reservoir; this makes the reservoir itself observable as a second packet algebra.
---

Let one fixed finite label packet and one scalable word-generated transverse
reservoir algebra be represented in a compressor presentation.  Suppose a
matrix microstate has vanishing packet, generation, and cross-commutation
defects and a canonical spectral projection `P` of trace at least `alpha>0`
on which both structures occur.  Then, after a dimension-free `o(1)`
perturbation and an `o(1)` change of `P`, there are exact finite-dimensional
semisimple algebras `Atilde,Btilde` on the same corner satisfying

```text
Atilde' cap P M_d P = Btilde,
Btilde' cap P M_d P = Atilde,
W*(Atilde,Btilde)=P M_d P.                              (CCMB1)
```

In particular `Atilde ~= M_r tensor I_m` and
`Btilde ~= I_r tensor M_m` on each selected simple summand.  A compressor
cycle that enlarges the simple degree of `Atilde` while returning the named
`Btilde` packet to itself must therefore lose positive normalized rank or pay
a packet/transport defect: the anonymous multiplicity reservoir has become a
second word-generated algebra and cannot exchange roles with the label factor.

## Attempts

- **One cross-Gram scalar extracts the common gauge.**
  `one-cross-gram-moment-extracts-the-common-polar-gauge` gives the precise
  post-exactification hypothesis.  If two contractions `T_1,T_2 in qMp`
  intertwine the same exact source/target packet and
  `Delta=tau(p)-tau(T_1^*T_2T_2^*T_1)`, then the polar part of `T_2^*T_1`
  extends to a unitary `V` in the source commutant and
  `||T_1-T_2V||_2<=sqrt(2Delta)`.  Two orthogonal coordinate embeddings into
  `alpha direct_sum alpha` show that separate Gowers--Hatami intertwiners and
  full self-Gram moments do not suffice.  The common-corner problem has
  therefore narrowed to forcing this one cross-Gram overlap before the paths
  are separated; after it, the two mixed Pauli commutators lock `V` into the
  smaller reservoir.

- **Only two mixed moments are needed after the relative gauge is exposed.**
  `two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge` proves that
  if `V` is the common relative unitary between the two child extension
  routes, then its commutators with the child Pauli `X,Z` force
  `dist_2(V,I_2 tensor U(m))` to be at most the sum of the two commutator
  errors.  The constant is dimension-free, and one commuting test is
  insufficient.  Thus `(CCMB1)` does not require a large new finite packet at
  the analytic endpoint.  The remaining load-bearing task is to decode the
  **same** `V` on the **same** positive-density corner from the mixed words;
  Gowers--Hatami uniqueness alone supplies only separate same-level
  intertwiners.

- **Nested Gowers--Hatami uniqueness does not expose the reservoir.**
  `gowers-hatami-uniqueness-does-not-lock-nested-pauli-reservoirs` gives the
  exact countermodel.  At fixed depth one may exactify the largest
  extraspecial group once and restrict, obtaining perfect coherence; the
  canonical representation still has label dimension doubling and
  multiplicity halving at every inclusion.  Moreover the next `M_2` child
  factor can be conjugated arbitrarily inside the old commutant without
  changing the old packet table at all.  Approximate uniqueness therefore
  aligns same-level label representations but leaves precisely the relative
  commutant gauge which `(CCMB1)` must make word-visible.  The new mixed
  relation must force that gauge into the smaller child commutant; a nested
  Clifford tower plus one same-level transported copy is insufficient.

- **A second fixed finite group cannot expose an unbounded reservoir.** Its
  irreducible degrees are bounded, and repetitions leave a common spectator
  algebra.  Thus finite-group exactification may anchor the label coordinates
  but cannot by itself produce the variable `M_m` factor in `(CCMB1)`.  The
  second algebra must be scalable (for example a word-generated matrix tape),
  or an independent argument must kill the residual spectator.  This is a
  load-bearing compiler requirement, not bookkeeping.
- **Rectangular firewall.** Add the proposed second packet to the exact
  `rectangular-escape`.  If the joint words still admit a larger tensor
  decomposition with an unused spectator factor, `(CCMB1)` is false for that
  packet choice.  The packet pair must exhaust the corner.
- **Bass--Serre firewall.** A finite graph of finite groups has exact finite
  quotient models, so endpoint type matching alone cannot force `(CCMB1)` or
  charge forbidden rank-one mass.  The required fullness must come from
  genuinely transverse compressor/holonomy relations.
- **Hybrid endpoint.** Once `(CCMB1)` pins one transverse generator, the
  fixed-PI-degree claim needs only one tuple outside every embedded
  `M_r` subfactor; conversely the PI value can certify fullness.  The two
  targets should be tested together on the same exact rectangular model.
