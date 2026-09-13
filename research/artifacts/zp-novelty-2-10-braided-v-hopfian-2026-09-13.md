# Novelty check: braided V is Hopfian (Zaremsky Problem 2.10, first question), 2026-09-13

Requested by z-verify-groups after its review PASS (`research/artifacts/zp-review-groups-2026-09-13-part2.md` §11,
d228d90964) of claim `braided-thompson-v-is-hopfian` (lane z2-10-bv-hopfian, f7c5912d5d and cda0020eb3).

**Verdict: NEW within the sources checked (bounded).** No source found proves or disproves that Brin's braided
Thompson group V_br (= bV) is Hopfian. The list's own author still asks the question in July 2026.

## Evidence

1. **Zaremsky's list, version of July 12, 2026, Problem 2.10**: "Is braided V Hopfian? Is every quotient of braided V
   finitely presented? (This would imply Hopfian.)"
2. **Zaremsky, "On normal subgroups of the braided Thompson groups", arXiv:1403.8132** (v1 31 Mar 2014, v2 31 Jan
   2018; Groups Geom. Dyn.). Abstract: every proper normal subgroup of V_br lies in the kernel of the quotient map to V.
   For F_br, a normal subgroup lies in the kernel of the map to F or contains the commutator subgroup. Σ¹(F_br) is
   computed. Question 4.7, which z-verify-groups reports asks Hopficity, was not re-read here.
3. **Semantic Scholar citations of arXiv:1403.8132** (16 entries). Every citing paper whose title mentions braided
   Thompson groups was checked by abstract, as were two others:
   - Cumplido, arXiv:2311.12763: pure subgroups of infinitely braided Thompson groups are bi-orderable.
   - Fournier-Facio–Lodha–Zaremsky, arXiv:2204.05272: quasimorphisms and bounded cohomology; bV is not uniformly
     perfect.
   - arXiv:2106.15571: divergence of Brown–Thompson and braided Thompson groups.
   - Zaremsky, arXiv:1803.02717: CAT(0) cube complexes and Σ^m(F_br).
   - Macedo Lins de Araujo–Oliveira-Tosti–Santos Rego, arXiv:2105.07096: fixed points of automorphisms, property
     R_∞ for F-like groups including braided F.
   None mentions Hopficity or surjective endomorphisms in its abstract.
4. **OpenAlex title-and-abstract searches**:
   - "Hopfian" AND "Thompson": 0 works.
   - "Hopfian" AND "braided": 15 works. All concern co-Hopfian or Hopfian properties of braid, virtual braid, welded
     braid or twin groups (e.g. Bell–Margalit, J. Algebra 2006; arXiv:math/0403145). None concerns braided Thompson
     groups.
   - "maximal condition on normal subgroups" AND "Thompson": 0 works.
   - "braided Thompson", publication date ≥ 2026-07-01: nothing relevant (see
     `zp-novelty-2-11-braided-v-inner-amenable-2026-09-13.md`).

## Bounds

- The session's web-search budget was exhausted: only API citation lists and arXiv abstract pages were used.
- Citing papers were checked by title except item 3's.
- No MathSciNet, zbMATH or Google Scholar.

## Remarks

- **No general theorem gives it.** V_br is finitely presented (Brin) but not residually finite, since it surjects
  onto the infinite simple group V. So Malcev's theorem does not apply, and I found no other general Hopficity result
  that covers it.
- **Credit to carry in the node:**
  - Zaremsky arXiv:1403.8132, for the normal-subgroup theorem used in Lemma A;
  - Brin (arXiv:math/0406042) and Dehornoy, for V_br;
  - Artin's representation and Andreadakis, for the residual-nilpotence input of Lemma B.
  - The owner lane should also check Falk–Randell (residual nilpotence of pure braid groups) and Burillo–González-Meneses,
    "Pure braid subgroups on braided Thompson's groups" (Publ. Mat. 52, 2008), and credit them if they overlap.
- **Relay wording:** "answers the first question of Zaremsky's Problem 2.10 positively; first proof within the
  sources checked (bounded search)". The second question, whether every quotient of V_br is finitely presented, stays
  open.
