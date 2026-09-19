# Property-(T)-free MF inheritance and envelope audit

Date: 2026-08-30

## Outcome

There is a strong Property-`(T)`-free envelope theorem, but it is an
**inheritance theorem rather than a seed theorem**.  If a finitely generated
non-MF group `Gamma` has solvable word problem, the August 2026
Boone--Higman--Thompson normal-intersection construction produces a finitely
presented group `P` for which every homomorphism to an MF group is trivial.
The same is true of every quotient of `P`.  Every maximal proper normal
quotient is therefore finitely generated, simple and non-MF; it is finitely
presented exactly when the maximal kernel is finitely normally generated.

The two-line mechanism is worth isolating.  If `phi:P -> A` has nontrivial
MF image, then `ker(phi)` is proper.  The normal-intersection property makes
`phi|Gamma` injective, embedding the non-MF seed in the MF group `A`, a
contradiction.  No analytic input, trace, stability, compression or Kazhdan
statement occurs.

What it does **not** do is prove the seed non-MF.  If the only available proof
of that hypothesis uses Property `(T)`, the composite existence proof still
uses Property `(T)`.

## Exact audit of the proposed wrappers

| Wrapper | Rigorous MF consequence | Verdict for a new Property-(T)-free seed |
|---|---|---|
| Subgroup or retract `B <= G` | `G` MF implies `B` MF; equivalently `B` non-MF implies `G` non-MF. The retraction map adds no converse because MF is not quotient-closed. | One-sided inheritance only. |
| Direct product with MF `A` | `B x A` is MF iff `B` is MF, by product closure and the canonical subgroup `B <= B x A`. | Exactly MF-neutral. |
| Finite extension / finite-index overgroup | `H <= G` of finite index satisfies `H` MF iff `G` MF (`mf-is-commensurability-invariant`). | Exactly MF-neutral. |
| Symmetric amalgamated double `G *_H G` | `G *_H G` is MF iff `G` is MF. The positive implication is Shulman's 2026 theorem; the converse is subgroup heredity. | Exactly MF-neutral; this strengthens the old residually finite special case. |
| Arbitrary simple envelope containing `B` | If `B` is non-MF, the envelope is non-MF; simplicity then makes its MF radical total. | Strong saturation, but still needs a non-MF seed and gives no finite presentation by itself. |
| BHT normal-intersection envelope | A non-MF seed forces the finitely presented envelope and **every nontrivial quotient** to have full MF radical. | Strongest Property-(T)-free inheritance result found; still conditional on the seed. |
| Amenable-quotient extension | No positive permanence theorem exists: `mf-not-closed-under-integer-extensions` gives an LEF kernel and quotient `Z` with non-MF total group. Trivial/direct-product extensions give MF totals with the same endpoint properties. | Kernel/quotient labels do not decide the middle group. The known negative instance has Kazhdan-dependent non-MF provenance. |
| Quotient or retract image | A free group is MF and surjects onto every finitely generated group, including non-MF ones. | Non-MF of a quotient never forces non-MF of the source. |

## Recent primary-source check

1. Tatiana Shulman, [*The MF property for amalgamated free
   products*](https://arxiv.org/html/2603.13564), Theorem 10 and the sentence
   immediately following it.  The paper defines group MF using the same norm
   matrix corona and explicitly states that every symmetric double of an MF
   group is MF.  Hence the exact invariance theorem above is not a C-star
   convention inference.

2. Francesco Fournier-Facio, Xiaolei Wu and Matthew Zaremsky,
   [*Abstract twisted Brin--Thompson
   groups*](https://arxiv.org/html/2603.24687v2), Appendix A, Lemma A.1,
   Proposition A.4 and Corollary A.5.  These give the normal-intersection
   envelope used in the saturation proof.

3. Benjamin Bachner, Alon Dogon and Alexander Lubotzky,
   [*On `L^1`-approximation of
   groups*](https://arxiv.org/html/2508.17392v3), Proposition 1.5 and
   Conjecture 1.8.  The April 2026 revision gives a conditional operator-HS
   stability route to non-MF for Deligne-type groups, and explicitly leaves
   the stability input conjectural.  It therefore supplies no unconditional
   Property-`(T)`-free seed.  Its definition of Deligne type also requires a
   central involution in the finite residual, so it does not bypass the
   finite spectral-corner mechanism.

## Sharp frontier after the audit

The wrapper search is complete at the level of the proposed operations:

- direct products, finite extensions and symmetric doubles are MF-neutral;
- retracts, arbitrary overgroups and simple envelopes transport non-MF only
  from a subgroup;
- amenable extensions have no endpoint-only permanence rule;
- BHT normal-intersection envelopes amplify a seed all the way to a
  finitely presented quotient-hereditary full radical, but cannot prove the
  seed hypothesis.

Consequently a proof whose entire provenance avoids Property `(T)` still
requires a native non-MF obstruction, such as the open Higman four-cycle
operator-norm collapse or the open binary-Leavitt native cross-Gram route.
No envelope operation audited here substitutes for that obstruction.
