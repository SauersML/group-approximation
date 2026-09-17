---
rg: 2
id: gottschalk-via-quantum-surjunctivity
kind: route
title: A strict automaton would transfer to a strict quantum automaton, and quantum automata are onto
target: gottschalk-surjunctivity-conjecture
requires:
  - quantum-surjunctivity-conjecture
  - strict-automata-yield-strict-quantum-endomorphisms
---

**Why sufficient.** Suppose a group `G` carried an injective non-surjective automaton on a finite full shift.
- The transfer premise gives a non-surjective quantum automaton on `(x)_G M_d` for some `d`.
- The quantum premise says there is none.

So every group is surjunctive.

**Why the decomposition has content.** The premises can fail on their own.
- **Quantum premise without the target.** Suppose a strict quantum automaton exists on a group that is
  classically surjunctive. Then the quantum premise fails while the target may hold.
  - The quantum premise is already at least as strong as Kaplansky stable finiteness over every `F_p`
    (`clifford-quantum-surjunctivity-iff-stable-finiteness`).
  - It holds on every sofic group (`sofic-groups-are-quantum-surjunctive`).
  - No index or K-theory invariant can prove it (`quantum-endomorphisms-split-off-their-relative-commutant`).
- **Transfer premise without the target.** Suppose a strict classical pair exists while quantum automata are
  onto. Then the transfer premise fails.
  - Its natural decoder-extension form splits further into (D1), measure preservation by some decoder, and (D2), a
    multiplicative extension off the diagonal (see its Attempts).

**Honesty note.** If the quantum premise holds, the transfer premise is equivalent to the target, as for any
two-premise contrapositive route. The route is useful only if the transfer is proved constructively, by turning
a strict pair into a strict *-endomorphism.
- This is the premise that replaces `injective-ca-pullbacks-extend-to-matrix-observables` in
  `gottschalk-via-matrix-observable-extension`.
- That premise asks the *encoder* pullback to extend, which by `split-ca-quantization-has-sharp-defect` is
  equivalent to the goal outright.
- The premise here asks only for *some* strict quantum automaton, with the decoder as the candidate source.
