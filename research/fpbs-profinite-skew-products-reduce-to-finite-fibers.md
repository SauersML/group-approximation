---
rg: 2
id: fpbs-profinite-skew-products-reduce-to-finite-fibers
kind: claim
title: Homogeneous skew products with totally disconnected fibre group preserve cost whenever uniform finite-fibre factors do
distinct_from:
  fpbs-finite-fiber-cost-bound: that bounds cost across one uniform finite-fibre factor and shows universal preservation there is equivalent to finite-index multiplicativity; this passes that preservation to every homogeneous skew product with a compact totally disconnected fibre group, through an increasing chain of finite-fibre quotients
  fpbs-traffic-variational-cost-identities: that proves, among other things, continuity of cost along increasing generating factors; this applies the continuity to the specific quotient chain W x K/(L K_n) of a profinite skew product, and identifies what remains of compact-extension cost preservation
artifacts:
  - research/artifacts/fpbs/docs/zimmer-tower-cost-split-2026-09-17.md
  - research/artifacts/fpbs/docs/fpbs-profinite-skew-products-reduce-to-finite-fibers-proof-2026-09-17.md
---

**OPEN.** Let Gamma be countably infinite, W a free p.m.p. Gamma-action with
finite cost, and K a compact metrizable totally disconnected group with
closed subgroup L. Let rho be a measurable cocycle into K, and
Z = W x_rho K/L the homogeneous skew product. Fix a decreasing basis of
open normal subgroups K_n, and let Z_n = W x_rho K/(L K_n).

* Each Z_n -> W is a uniform [K : L K_n]-point factor.
* The Z_n increase and generate Z.
* C(Z_n) decreases to C(Z).

Consequently, suppose every uniform finite-fibre factor map of free
Gamma-actions preserves cost. By `fpbs-finite-fiber-cost-bound`, this is
equivalent to finite-index multiplicativity of cost minus one. Then
C(Z) = C(W) for every such skew product.

**Meaning for the compact premise.** Among homogeneous skew products,
which are all ergodic relatively compact extensions by the imported
isometric-extension theorem, the part of
`fpbs-compact-extensions-preserve-cost` beyond finite-index
multiplicativity consists of fibre groups with nontrivial identity
component, for example circle-valued rotation cocycles, together with
non-ergodic compact extensions. For such fibre groups the finite
quotients no longer separate points of K/L.

Proof attempt: artifact Theorem 4.1. Referees found the second sentence
of the consequence and the "Meaning" paragraph false as stated; see
Attempts.

## Attempts

1. **Filter the fibre by open normal subgroups and apply increasing-factor
   continuity (b-t-block, 2026-09-17, refuted by referee).** Formerly route
   `fpbs-profinite-skew-products-reduce-to-finite-fibers-proof`, requiring
   `fpbs-traffic-variational-cost-identities` and
   `fpbs-finite-fiber-cost-bound`. The proof is kept as the attempt artifact
   `research/artifacts/fpbs/docs/fpbs-profinite-skew-products-reduce-to-finite-fibers-proof-2026-09-17.md`.
   Referee lenses 1 and 2 returned *refuted*; lens 3 returned *survives*. All
   three lenses checked parts (a) and (b) and the conditional first sentence
   of (c): given uniform finite-fibre preservation for Gamma, C(Z) = C(W).
   - **Lens 2 (verdict 9f8be2cb).** Quantifier mismatch in the second sentence
     of (c), and in the hole's reframing. `fpbs-finite-fiber-cost-bound`
     proves (F)<=>(I) only over a class of groups (finite-fiber-cost-descent.md
     Section 2). (F)=>(I) works for one group through the diagonal coset
     extension X x Gamma/H. (I)=>(F) applies (I) to Gamma x Stab(1) inside
     the different group Gamma x Sym(q), so multiplicativity for Gamma alone
     gives nothing. This breaks the per-Gamma equivalence. It also breaks the
     hole's claims that finite-fibre extensions are "the one regime that
     multiplicativity already captures" and that the remainder is "new
     content beyond finite-index multiplicativity" for fixed Gamma. Second,
     the "Meaning for the compact premise" paragraph states the
     isometric-extension theorem backwards: ergodic relatively compact
     extensions are homogeneous skew products, not the reverse. A skew product
     need not be ergodic, and the theorem is never quoted. Third, the residue
     is misidentified: the open normal subgroups of K intersect to K^0, so
     the L K_n intersect to L K^0. The chain argument works whenever
     K^0 <= L, and fails only when K/L is not totally disconnected.
   - **Lens 1 (verdict 0021e6fa, posted on
     `fpbs-relative-cycle-block-localization`).** The hole reframing says all
     three recorded rounding countermodels (determinantal, fixed-certificate,
     retained-boundary) are finite-fibre extensions, so they say nothing about
     the circle-fibre and relatively weakly mixing regimes. Artifact Section 5
     adds that no localization countermodel over a relatively weakly mixing
     extension is recorded. Both claims are false.
     `fpbs-retained-boundary-rounding-isoperimetric-floor` holds for every
     free factor Y -> X, with worked case a x b -> b on F_2 x Z for any a,
     including weakly mixing a (floor F_0 >= 5/3).
     `fpbs-oblivious-certificates-never-localize` covers lifts on a x b -> b
     for any a, already on Z^2.
   - **Lens 3 (verdict 1ae2d07a), survives.** It checked (a), (b) and (c)
     against (10.1) in Section 10 of fixed-price-conditional-traffic.md. It
     found the claim correctly conditional, and added nothing new beyond the
     tower remark already in Section 10 of that artifact.
