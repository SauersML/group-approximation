---
rg: 2
id: binary-left-inverse-pairs-are-boolean-adically-formalizable
kind: claim
title: Every binary left-inverse pair is formalizable in the Boolean-adic completion, so formalizability is exactly termination
distinct_from:
  binary-left-inverse-pairs-are-formalizable: that asked for polynomial formalizing representatives, and is refuted; this shows representatives always exist in the Boolean-adic completion, so what fails is termination at finite degree and memory.
  binary-left-inverse-pairs-need-not-be-formalizable: that shows the marker involution has no polynomial formalizing representatives; this shows it does have a unique Boolean-adic one for each Lemma C encoder representative, which is not a polynomial.
  formalizability-conormal-obstruction-is-jacobian-cokernel: that computes the conormal layer of the obstruction for a fixed encoder representative; this shows every graded layer vanishes for a Lemma C representative.
artifacts:
  - research/artifacts/formalizability-obstruction-class-2026-09-12.md
---

Notation as in `formalizability-is-a-boolean-ideal-cokernel-class`. Let
`sigma o tau = id` on `(F_2^n)^G`, for any group `G`.

**Claim.** Choose an encoder representative `hat tau^*` whose reduced Jacobian is the
identity at every `{0,1}`-configuration, i.e. `J_B = I` (always possible, Lemma C). Then:
1. For every `k >= 1` the graded map `gr_k(hat tau^*)` on `I^k/I^{k+1}` is onto, and
   bijective when `tau` is bijective.
2. The decoder correction equation `hat tau^*(delta) = eps` has a solution in the
   `I`-adic completion, as an `I`-adically convergent sum `delta = sum_k delta_k` of
   equivariant finite-memory `delta_k in I^k`. The solution is unique when `tau` is
   bijective.
3. The pair is formalizable with this encoder representative iff some such solution is a
   finite-memory polynomial.
4. For the marker involution of `binary-left-inverse-pairs-need-not-be-formalizable`, the
   unique Boolean-adic solution is not a finite-memory polynomial, for every Lemma C
   representative.

So every binary left-inverse pair is formalizable Boolean-adically, no associated-graded
obstruction class survives, and the obstruction to formalizability is exactly
**termination**: whether the degree-by-degree correction stops at finite degree and
finite memory.

## Attempts

- **Proved,** by `binary-left-inverse-pairs-boolean-adic-formalization-proof`.
- **Consequence for the Kaplansky route:** a positive formalization theorem must bound
  the memory and degree growth of the `delta_k`; a negative invariant must see that
  growth. Associated-graded cohomology is blind to it, since every graded piece vanishes.
- **Open:** an invariant that measures the growth and detects the marker involution
  directly, and whether it survives ancilla tracks
  (`injective-binary-automata-are-stably-formalizable`).
