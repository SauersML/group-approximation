---
rg: 2
id: fpbs-amalgam-over-amenable-descends-fixed-price-proof
kind: route
title: Apply the amalgamation formula to every free action and sandwich against the Bernoulli restriction
target: fpbs-amalgam-over-amenable-descends-fixed-price
requires: []
artifacts:
  - research/artifacts/fpbs-amalgam-descent-amenably-generated-2026-09-16.md
---

Direct proof, with cited literature imports. The full argument is §1 and §2
of the artifact. The steps are as follows.

1. **Amalgamation formula for every free action.** Let `b` be a free p.m.p.
   action of `G`. On the conull set of points with trivial stabilizer, the
   orbit relations satisfy `R_1 cap R_2 = R_3`, `R_1 cup R_2` generates
   `E_b`, and no alternating chain with steps in `R_{j} minus R_3` closes up.
   Here `R_i = E_{b|Gamma_i}` and `R_3 = E_{b|A}`. This is Lemma 1.5 of the
   artifact, from the normal form theorem for amalgams. `R_3` is hyperfinite
   (Ornstein-Weiss, [GL] Thm 1.13), and `R_1`, `R_2` have finite cost by
   hypothesis. [GL] Thm 2.27 (Gaboriau 2000, Theoreme IV.15) gives
   `C(b) = C(b|Gamma_1) + C(b|Gamma_2) - C(E_{b|A})`. Since `A` is infinite
   and `b|A` is free, `E_{b|A}` has a treeing of cost 1 ([GL] Thm 2.20 and
   Thm 2.24). So `C(b) = C(b|Gamma_1) + C(b|Gamma_2) - 1` for every free `b`.
2. **The value of `c(G)`.** Co-induction and a diagonal product (Lemmas
   1.2-1.4, re-deriving [GL] Thm 2.12) give free actions `b_eps` of `G` whose
   two restrictions are `eps`-close to `C(Gamma_1)` and `C(Gamma_2)`.
   Restrictions of free actions are free, so each restriction costs at least
   the infimum. With fixed price this gives
   `c(G) = C(Gamma_1) + C(Gamma_2) - 1`.
3. **Rigidity.** For every free `b`, `C(b|Gamma_1) + C(b|Gamma_2)` equals
   `C(Gamma_1) + C(Gamma_2)`. All four numbers are finite and each
   restriction is at least its infimum, so `C(b|Gamma_i) = C(Gamma_i)`.
4. **Bernoulli.** Take `b = s_G`, which is free. Since `s_G|Gamma_i` is
   conjugate to `s_{Gamma_i}` (Lemma 1.6), `C(s_{Gamma_i}) = C(Gamma_i)`.
5. **Fixed price of the factors.** Let `a` be a free action of `Gamma_i`.
   Abert-Weiss (arXiv:1103.1063) gives `s_{Gamma_i} weakly contained in a`.
   Tucker-Drob (arXiv:1211.6395) Cor 6.20 gives
   `PC(a) <= PC(s_{Gamma_i})`, Def 6.6 gives `PC <= C`, and Cor 6.8(1) gives
   `C(a) = PC(a)` because `C(a)` is finite. So `C(a) <= C(Gamma_i) <= C(a)`.

**Trust surface.**
- [GL]: D. Gaboriau, lecture notes, version of October 3, 2025. The text of
  Thms 1.13, 2.12, 2.20, 2.24, 2.27 and the sentence before Thm 2.27 was read
  from the PDF on September 16, 2026.
- Gaboriau 2000: the definition of `R_1 *_{R_3} R_2` in Invent. Math. 139 was
  not re-read. Lemma 1.5 verifies the natural freeness conditions directly
  (intersection, generation, no closed alternating chain), and these imply
  any variant with length or parity restrictions. The formula is used only
  through [GL] Thm 2.27.
- Abert-Weiss and Tucker-Drob: read in full text on September 12, 2026, per
  `research/artifacts/fpbs/docs/fixed-price-countable-passage.md` §1. Not
  re-read on September 16.
- Normal form for amalgams: Serre, *Trees*, Ch. I; Lyndon-Schupp, Ch. IV.

Everything else (joins, lifting graphings through factor maps, co-induction,
restricting a Bernoulli shift) is proved in full in §1 of the artifact.
