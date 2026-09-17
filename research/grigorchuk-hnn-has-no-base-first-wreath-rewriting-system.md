---
rg: 2
id: grigorchuk-hnn-has-no-base-first-wreath-rewriting-system
kind: claim
title: A finite complete rewriting system for Grigorchuk's HNN extension under a wreath-type ordering cannot rank base letters generating an infinite subgroup below the stable letter
distinct_from:
  grigorchuk-hnn-extension-is-fp-infinity: that asks whether the extension is of type FP_infinity; this kills one family of certificates for it, namely finite complete rewriting systems under alphabet-monotone orderings with the base generated first.
  basilica-hnn-extension-is-fp-infinity: that is the torsion-free candidate's FP_infinity question; this node's corollary C3 kills only the base-first certificates for it.
artifacts:
  - experiments/hnn-rewriting-2026-09-17/RESULTS.md
  - experiments/hnn-rewriting-2026-09-17/kb.cpp
---

**ESTABLISHED (obstruction to a family of certificates).** A finite complete rewriting system
(FCRS) for a group certifies type `FP_∞` (Anick; Groves; Squier; Kobayashi). With finite
presentation, this is `F_∞`. So an FCRS for `𝔊^` would settle
`grigorchuk-hnn-extension-is-fp-infinity` and answer
`zaremsky-1-12-f-infinity-amenable-non-elementary-amenable`. This node kills a whole class of such
certificates.

**Terms.** A reduction ordering on `Σ*` is *alphabet-monotone* for a ranking `ρ` of `Σ` if every
word containing a letter outside the `k` lowest letters is greater than every word in those `k`
letters. Sims' wreath ordering and the recursive path ordering with precedence `ρ` are
alphabet-monotone. Shortlex is not.

**Statement.**

- Let `𝔊^` be Grigorchuk's finitely presented HNN extension of the first Grigorchuk group, and let
  `χ : 𝔊^ → Z` be the character with kernel `N ⊇ 𝔊`.
- Let `R` be an FCRS for `𝔊^` over a finite alphabet `Σ`, compatible with an ordering that is
  alphabet-monotone for a ranking `ρ`.
- **Conclusion:** every initial segment of `ρ` consisting of letters in `N` generates a *finite*
  subgroup.
- **In particular:**
  - no FCRS for Grigorchuk's presentation on `a A b B c C d D t T` is compatible with the wreath
    ordering;
  - more generally, no monotone FCRS ranks letters generating an infinite subgroup of `N` (e.g. a
    conjugate of `𝔊`) below every letter of nonzero `χ`.

**The step where these certificates fail.** Restrict the rewriting system to its lowest letters.
The restricted system is still complete and presents the submonoid those letters generate, so
that submonoid is finitely presented (Lemma 1 of the proof). `N` is a 2-group, and every infinite
finitely generated subgroup of `𝔊` is commensurable with `𝔊` (Grigorchuk–Wilson, J. London Math.
Soc. 2003). `𝔊` is not finitely presented. So the segment must generate a finite group.

**Corollary C3, Basilica.** For the Basilica extension `B^`, a monotone FCRS cannot rank letters
generating a non-finitely-presented subgroup of `ker χ` (e.g. `a, b = t a t^(−1)`) below all
letters of nonzero `χ`.

**Scope.** This kills the base-first class only. It does not rule out:

- shortlex;
- orderings with the stable letter early;
- other certificates of `FP_∞`, such as Brown's criterion or discrete Morse theory.

Proof: `grigorchuk-hnn-has-no-base-first-wreath-rewriting-system-proof`.

## Computation (bounded Knuth–Bendix searches over the surviving orderings)

Script: `experiments/hnn-rewriting-2026-09-17/` (`kb.cpp`, `pres.py`, `runall.sh`, raw outputs in
`out/`; results in `experiments/hnn-rewriting-2026-09-17/RESULTS.md`).

- **Completer.** `kb.cpp` is a C++ Knuth–Bendix completer with wreath and shortlex orderings. It
  re-checks all critical pairs of any system it reports as complete.
- **Presentations checked.** The substitutions `σ` of both presentations were checked on level 14
  of the binary tree (`basilica_sigma_check.py`, `grigorchuk_sigma_check.py`). A control
  substitution fails.
- **Calibration.** `BS(1,2)` with wreath ordering `a A t T` completes to a verified 8-rule system.
- **Bounds.** At most 3000 active rules, and equations with a side longer than 30 letters are
  deferred. Each run is single-threaded with a 300 s timeout.
- **Rules out only this.** No FCRS is reached by this completion procedure within these bounds.
  Completion is sensitive to the processing order, so this is not a proof that no FCRS exists for
  these orderings.

Results:

| group | order (low→high) | ordering | outcome |
|---|---|---|---|
| BS(1,2) | a A t T | wreath | COMPLETE, 8 rules, verified |
| BS(1,2) | t T a A / T t A a | wreath | no completion (timeout 120 s, >1000 rules) |
| Basilica HNN | a A t T / A a t T | wreath | overflow at 3000 rules, lhs length 21–24 |
| Basilica HNN | t T a A | wreath | timeout 300 s, 2673 rules |
| Basilica HNN | a A t T | shortlex | overflow at 3000 rules |
| Grigorchuk HNN | a A b B c C d D t T | wreath | timeout 300 s (killed by the theorem above) |
| Grigorchuk HNN | t T a A b B c C d D | wreath | timeout 300 s, 2773 rules |
| Grigorchuk HNN | a A b B c C d D t T | shortlex | overflow at 3000 rules |

For `BS(1,2)`, the only ordering that completed is t-highest wreath. For `𝔊^`, that is exactly the
base-first ordering that the theorem forbids.
