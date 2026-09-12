---
rg: 2
id: candidate-amplification-envelope-closes-kleene
kind: claim
title: A uniform candidate-indexed amplification envelope closes the Kleene search
distinct_from:
  dimension-kleene-threshold-needs-amplification-envelope: that gives the necessary dimension-profile envelope; this verifies the stronger candidate-indexed version, including effective rational-unitary density and search quantifiers.
  post-candidate-nemesis-has-a-finality-dilemma: that excludes appending a challenge after recognizing a tuple; this theorem assumes every challenge and its verifier already belong to one fixed presentation.
---

**ESTABLISHED CONDITIONAL THEOREM.**  Fix a finite presentation `P`, a word
`w`, and rationals

```text
0<alpha<beta<sqrt(2),                    rho>0.          (CAE1)
```

Suppose rational unitary tuples have effective codes `c`.  For every such
code and amplification factor `k>=1`, suppose a positive rational
`delta(c,k)` is computable.  Assume both:

1. **acceptance completeness:** the fixed exhaustive verifier halts on
   `(c,k)` whenever the amplified tuple has
   `Def_P(c)<delta(c,k)` and `M_w(c)>beta`;
2. **final-presentation soundness:** if it halts, every tuple in the selected
   dimension with defect below `delta(c,k)` has marked value at most `alpha`.

All verifier branches and challenge templates must be pre-encoded in `P`.
Finally assume the effective, uniform envelope

```text
sup_(k>=1) delta(c,k) >= rho                         (CAE2)
```

for every rational code `c` with `M_w(c)>beta` that can occur in the search.
Then a hyperlinear canonical model retaining `w` is impossible.

The acceptance-completeness clause is load-bearing.  Soundness merely of the
form “if the machine happens to halt, then ...” does not imply that the
exhaustive search ever halts.  Likewise `rho` must be a known computable
positive lower bound; an existential, non-effective lower bound does not
give the advertised algorithm.

The theorem remains conditional because `(CAE2)` is a very strong semantic
property of the pre-encoded activator.  It is nevertheless logically
coherent and is stronger than the dimension-only amplification envelope.

