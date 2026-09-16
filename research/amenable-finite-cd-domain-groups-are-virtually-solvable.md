---
rg: 2
id: amenable-finite-cd-domain-groups-are-virtually-solvable
kind: claim
title: An amenable group of finite cohomological dimension whose integral group ring is a domain is virtually solvable
distinct_from:
  amenable-groups-of-finite-cd-are-virtually-solvable: that is Kropholler's question without the domain hypothesis; this adds the hypothesis that Z[G] is a domain, the setting of Degrijse's Theorems A and B, and with amenable-finite-cd-integral-group-rings-are-domains it gives that question
  hillman-linnell-finite-hirsch-length-theorem: that is the established structure theorem for elementary amenable groups of finite Hirsch length; this is the open statement for amenable groups not known to be elementary amenable
artifacts:
  - research/artifacts/kropholler-question-zero-divisor-split-2026-09-16.md
---

**OPEN.** Let `G` be an amenable group with `cd_Z G < ∞` such that `Z[G]` has no zero divisors.
Then `G` is virtually solvable.

**Known cases.** Section numbers refer to the artifact, and each case is proved there from cited
theorems.

1. **Dimension at most 2.** If `cd G <= 2`, then `G` is solvable: `1`, `Z`, a noncyclic subgroup
   of `Q`, or `BS(1,m)` (Proposition 3.1). The source is D. Degrijse, arXiv:1609.07635,
   Theorem B.
2. **Linear groups.** If `G` is linear over a field, it is virtually solvable. The domain hypothesis
   is not needed (Corollary 2.3, Tits alternative).
3. **Fibred groups of cd 3.** If `cd G = 3` and some map `G -> Z` has a kernel of type `FP_2`, then
   that kernel is `BS(1,m)` and `G` is solvable of derived length at most 3 (Proposition 4.1). The
   key step is Lemma 4.2: an FP kernel of cd `m` gives `cd(N ⋊ Z) = m + 1`.
4. **Ascending HNN with a small base.** If `cd G = 3`, `G` is of type `FP_2`, `b_1(G) > 0`, and the
   Bieri–Strebel ascending-HNN base has `cd <= 2`, then `G` is solvable (Proposition 6.3).
5. **`PD_3` groups.** If `G` is `PD_3` and some finite-index subgroup has an elementary amenable
   quotient with infinite kernel, then `G` is virtually solvable. This covers positive virtual first
   Betti number (Proposition 5.1, via Strebel's theorem).
6. **Finitely generated groups suffice.** The claim holds for all `G` if and only if it holds for
   finitely generated `G` (Proposition 2.2).

## Attempts

- **2026-09-16 (lane `hi-fron-amenable-groups-of-finite-cd-a`): transplanting Degrijse's
  dimension-2 proof to dimension 3.** It yields cases 3–5 above and stops at three points
  (artifact, Section 6).
  - **(B1) Finite type.** Finite generation does not give `FP_2`. The group `Z[1/6] ⋊_{2/3} Z` is
    finitely generated, has domain group ring and cd 3, and is not `FP_2` (Section 6.1). So
    Degrijse's Theorem A cannot be entered from finite generation alone.
  - **(B2) A map onto `Z`.** A vanishing Euler characteristic does not force `b_1 > 0`. The
    Hantzsche–Wendt group has `b_1 = 0` (Section 6.2).
  - **(B4) The base.** In an ascending HNN extension `G = K *_φ` of cd 3 with base `K` of cd 3, the
    Mayer–Vietoris argument needs two things. One is that `α` is onto `H^2(K; ZG)`, where
    one-endedness gives nothing (G1). The other is that `K` is of type `FP_2` (G2).
- **Open question (Q-a).** For an ascending HNN extension of a type-FP base of cd `m`, is the cd
  `m + 1`? A grading argument proves this when restriction to the image of the endomorphism is
  injective in degree `m`. A positive answer, together with (G2), would settle case 4 without
  assuming anything about the base.
