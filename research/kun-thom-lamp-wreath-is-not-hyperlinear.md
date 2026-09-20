---
rg: 2
id: kun-thom-lamp-wreath-is-not-hyperlinear
kind: claim
title: The binary Kun--Thom lamp wreath over the q = 2, r = d = 3 Theorem E pair is not hyperlinear (Liu's claim, under review)
distinct_from:
  non-hyperlinear-group: that is the program root, which asks for some explicit non-hyperlinear group; this is one specific group with one specific claimed proof, recorded so that the root can follow its review.
  kun-thom-nonsofic-wreath: that is nonsoficity (permutation models, normalized Hamming metric) of the same family of wreath products, established by citation of Kun--Thom; this is the strictly stronger statement in the normalized Hilbert--Schmidt metric.
  wreath-not-sofic: that is nonsoficity of the same wreath candidate; nonhyperlinearity implies it, but no converse is supplied here.
  kt-centralizer-normalization-hs: that asks whether trace-preserving representations into a tracial matrix ultraproduct normalize the Gamma-commutant; the claimed proof answers it for arbitrary homomorphisms (internality, then normalization) and draws the group conclusion recorded here.
  kt-canonical-hs-normalization-fails: that is the opposite branch of the same fork, a Connes-embeddable model with a non-normalized Gamma-commutant; this claim, if its proof stands, refutes it.
  kt-wreath-hyperlinear-iff-double-hyperlinear: that is an established equivalence between the wreath, the double and relative embeddability, and it decides neither side; this claim decides the wreath side negatively.
  kun-thom-wreath-is-not-rational-character-approximable: that excludes approximation by rational characters, which is weaker than excluding all hyperlinear approximations.
  kun-thom-wreath-weak-mf: that concerns operator-norm (weak MF) approximation of the same wreath; this concerns normalized Hilbert--Schmidt approximation.
artifacts:
  - research/artifacts/gq-nh-record-consistency-sweep.md
  - research/artifacts/liu-cairn-integration-2026-09-20.md
  - research/artifacts/liu-block-construction-audit-2026-09-20.md
  - research/artifacts/liu-internality-normalization-audit-2026-09-20.md
---

**OPEN (proof claimed, under review).**

J. Liu, *Nonhyperlinear groups exist*, dated September 20, 2026, posted at
https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf, claims the
unconditional theorem below.

- The paper states that its main result was obtained using the Danus automated mathematical
  reasoning system (Appendix A).
- Appendix A.1 describes the reviews behind it: "These are automated textual mathematical
  reviews; the records contain no formal proof-assistant certification or external human
  verification."

This node records the claim. It stays OPEN until independent reviews of the proof are
complete: §§3–5, and §§6–8 checked against Thom's preprint.

**Integrated review update, 2026-09-20.** Three targeted audits now cover the
block construction, internality/normalization (including Thom comparison), and
the separate Leavitt application. They found no concrete gap in the inspected
steps but do not certify the entire paper or all imported inputs. The shared
analytic claim is `kazhdan-commutants-are-internal`, explicitly credited to
Jihao Liu. Conditional routes now connect it through all-trace normalization
to this exact marked-lamp statement and the existing root. The long imports
remain OPEN rather than being accepted by a blanket citation route.

## Statement

Definition 8.1 of the paper, in plain text:

```text
R_+ = F_2[x_1, x_2, x_3],   R = F_2[x_1^(±1), x_2^(±1), x_3^(±1)].
EL_3(B) = <I_3 + b E_ij : b in B, i != j>  for a unital ring B.
alpha_A(x^v) = x^(Av)  for A in SL_3(Z), extended to R and to matrix entries.
Gamma = EL_3(R_+),   G = EL_3(R) semidirect_alpha SL_3(Z),
W = (direct_sum_(G/Gamma) C_2) semidirect G,
```

Here:
- `Gamma` lies in the first factor of `G`;
- the cosets are left cosets, and `G` permutes the lamps by left translation;
- `a_x` is the nonidentity lamp at the coset `x`.

The elements used are

```text
t = (I_3, I_3 + E_12),   gamma_0 = (I_3 + x_2 E_12, I_3),   b = a_(gamma_0 t Gamma) a_(t Gamma).
```

Theorem 8.3, verbatim, with `‖x‖_(2,d) = (Tr(x*x)/d)^(1/2)`:

> The group W of Definition 8.1 is countable and b ≠ e. For every nonprincipal ultrafilter
> ω on ℕ, every sequence d_n ≥ 1, and every homomorphism ρ : W → U(∏_{n→ω}(M_{d_n}(ℂ),
> tr_{d_n})), one has ρ(b) = I.
>
> There exist a finite symmetric F ⊂ W containing e and η > 0 such that for every d ≥ 1 and
> every φ : F → U(d) with φ(e) = I_d, at least one of the following holds:
> (i) Some g, h, gh ∈ F satisfy ‖φ(gh) − φ(g)φ(h)‖_{2,d} ≥ η.
> (ii) Some distinct g, h ∈ F satisfy |‖φ(g) − φ(h)‖_{2,d} − √2| ≥ η.
> In particular, W is not hyperlinear.

## Credit

- **J. Liu (Danus system), 2026-09-20:**
  - Theorem 1.2 = Theorem 6.7, internality of Kazhdan commutants in tracial matrix
    ultraproducts, in the original dimensions. The paper presents it as a positive answer to
    Alekseev--Thom, arXiv:2608.05362, Open Problem 6.2(a), the centralizer problem.
  - The unconditional assembly, Theorem 8.3.
- **A. Thom**, *A conditional construction of a nonhyperlinear group and the centralizer
  problem*, preprint, https://andreasthom.github.io/pdf/nonhyperlinear.pdf.
  - **Dates:** Liu's paper (p. 4) reports, from Thom, that the preprint was circulated on
    10 August 2026, submitted to arXiv on 17 August 2026 (still on hold), and public on
    Thom's homepage since 25 August 2026.
  - **What Thom proves:** a positive answer to the centralizer problem implies normalization
    (Thom's Theorem 1.2). Under the same assumption, the group double `G *_H G` is not
    hyperlinear (Thom's Theorem 1.3).
  - **Priority:** Liu's Theorem 1.3 = Theorem 7.4 overlaps Thom's Theorem 1.2, "which has
    priority, and the credit for it belongs to Thom." The conditional construction is Thom's.
- **G. Kun and A. Thom**, arXiv:2608.06222, Theorem E and Section 5.2: the group pair and
  the lamp construction (Liu's Theorem 8.2).
- **OpenAI**, *Nonsofic groups exist*, Chapter 3 of *Ten advances in mathematics and
  theoretical computer science* (2026), Proposition 2.3: the compression criterion. This is a
  group generated by a Kazhdan subgroup together with finitely many elements that conjugate it
  into itself.
- **Further inputs Liu cites:**
  - Kun, arXiv:1606.04471, Theorem 1: the expander decomposition, whose exceptional-set and
    smoothing method Liu adapts;
  - Houdayer--Vaes 2013, Lemma 2.1;
  - Ioana 2025, Lemma 2.2(1).

No priority is claimed here for any part of this chain.

## Claimed proof architecture (as written by Liu; not reviewed here)

1. **Internality.** Theorem 6.7 (Theorem 1.2), verbatim:

   > Let H be a finitely generated discrete group with property (T), let ω be a nonprincipal
   > ultrafilter on ℕ, let d_n ≥ 1, and let π : H → U(M) be a homomorphism. Then there are
   > unital ∗-subalgebras A_n ⊆ M_{d_n}(ℂ) such that π(H)′ ∩ M = [A_n]_ω.

   The paper builds it in four stages:
   - §3: uniform repair from a quotient spectral gap (Proposition 3.1, Theorem 3.2);
   - §4: equivariant rounding of operator-valued partitions;
   - §5: physical scalar-expanding decompositions;
   - §6: matching the expanding blocks across unequal ranks.
2. **Normalization.** Theorem 7.4 (Theorem 1.3), verbatim:

   > Let H be a countable group with property (T), let Λ ≤ H, and suppose that
   > H = ⟨Λ, t_1, …, t_s⟩ for finitely many t_i satisfying t_iΛt_i^{−1} ≤ Λ. Let
   > π : H → U(M) be a homomorphism into a tracial matrix ultraproduct with specified ω and
   > dimensions d_n. Suppose D = π(Λ)′ ∩ M = [A_n]_ω is internal. Then π(H) normalizes D,
   > and there are unital abelian subalgebras B_n ⊆ Z(A_n) satisfying Z(D) ∩ π(H)′ = [B_n]_ω.
3. **The group.** Theorem 8.3, Steps 1–5:
   - `b != e`, because `x_2` does not lie in `F_2[x_1, x_1 x_2, x_3]`.
   - `Gamma` is generated by 24 elementary involutions, and `G = <Gamma, t_ij>` with
     `t_ij Gamma t_ij^(-1) <= Gamma`.
   - Normalization gives `rho(a_(gamma_0 t Gamma)) = rho(a_(t Gamma))`, so `rho(b) = I`.
   - A compactness argument over all dimensions turns this universal collapse into the finite
     set `F` and the tolerance `eta`.

The group-level step transcribes Kun--Thom's Theorem A argument to tracial ultraproducts; the
same reduction is recorded in `kt-centralizer-normalization-hs`. The weight of the claim is on
step 1.

## Graph consequences of the full claimed chain (not of this group statement alone)

The distinctions here matter. General internality and all-trace normalization,
not the displayed one-wreath statement alone, feed the uniform compression and
normalization-countermodel conclusions below. The integrated routes enforce
that stronger prerequisite. The Leavitt conclusion is a separately checked
Cairn conditional application of Jihao Liu's Theorem 1.2/6.7; it does not use
the wreath theorem and does not assert arbitrary-channel rounding.

Artifact `gq-nh-record-consistency-sweep` has the details. No established node was found to
contradict the claim.

- **Decides the root.** `non-hyperlinear-group` is answered by `W`.
- **Settles the equivalent groups.** Through `kt-wreath-hyperlinear-iff-double-hyperlinear`,
  none of these is hyperlinear: the double `G *_Gamma G`, the centralizer HNN group, the free
  binary coset wreath, and the Gaussian crossed product listed there. Liu's paper reaches the
  double separately, through Thom's Theorem 1.3.
- **Settles the action.** Through `kt-free-action-hyperlinear-iff-wreath-hyperlinear`, the
  Kun--Thom free nonsofic action is not hyperlinear.
- **Settles the A_5 wreath.** Through `a5-wreath-contains-binary-kun-thom-wreath`, the
  A_5-lamp wreath is not hyperlinear.
- **Would establish these OPEN claims:**
  - `hs-uniform-compression-stability-at-the-theorem-e-pair`, via the established
    `kazhdan-commutant-compression-stability-is-finitary`;
  - the canonical instance of `kt-centralizer-normalization-hs`.
- **Would refute these OPEN claims:**
  - `kt-canonical-hs-normalization-fails`;
  - `hs-compression-stability-fails-at-the-theorem-e-pair`;
  - `hyperlinear-wreath-model`;
  - `kt-double-reduced-cstar-is-mf`, since the established unique trace would make the double
    hyperlinear;
  - `kun-thom-finitary-action-lifts-to-normalizer`.
- **Most consequential, and needing a direct check.** `leavitt-channel-rounding-forces-nonhyperlinearity`
  is an established conditional. It records that a positive answer to Open Problem 6.2(a),
  for every canonical embedding of `L_(F_2)(1,2)^x`, supplies its rounding property (R).
  Theorem 6.7 is stated for every homomorphism of every finitely generated Kazhdan group.
  Together these would make the binary Leavitt unit group non-hyperlinear.

## Attempts

- **2026-09-20, recorded by lane nh-record.** Liu's proof is claimed and under review. The
  independent review is split between two referee lanes:
  - **nh-ref-a:** §§3–5;
  - **nh-ref-b:** §§6–8, against Thom's preprint.

  Flip this node to ESTABLISHED only after both reviews pass, citing their review artifacts.
