---
rg: 2
id: thompson-v-one-word-strict-hs-ceiling
kind: claim
title: Bound one nontrivial Thompson-V word strictly below regular Hilbert--Schmidt energy
artifacts:
  - research/artifacts/thompson-v-one-word-ce-frontier-2026-08-21.md
distinct_from:
  cyclic-carrier-energy-stability: that seeks equality with an exact finite-dimensional energy ceiling for a general cyclic carrier; the Thompson-V character simplex means any strict bound below the regular value automatically collapses to that equality.
  thompson-v-not-lef: that rules out finite local embeddings and operator-norm-separated exact models; this is a normalized-HS statement about approximate unitary representations.
  thompson-pauli-prefix-rounding-has-polynomial-cost: that rounds addressed Pauli data carried by V prefix words; this target concerns the bare group V and one ordinary group word.
---

Fix a finite presentation `V=<X|R>` and one word `w!=1`. Prove that there are
`epsilon>0` and `delta>0` such that every finite-dimensional unitary tuple
`U=(U_x)_(x in X)` satisfying

```text
max_(r in R)||r(U)-I||_2<delta
```

also satisfies

```text
||w(U)-I||_2^2<=2-epsilon.                              (TV2)
```

Equivalently,

```text
lim_(delta->0) sup_(def_R(U)<=delta)||w(U)-I||_2^2<2.
```

By `thompson-v-ce-one-word-trace-face-is-binary`, `(TV2)` is equivalent to
nonhyperlinearity of `V`: it is a concentrated one-word reformulation of the
root problem, not an established gap.

## Attempts

- Fournier-Facio--Rangarajan prove uniform Ulam stability of `V` with a
  linear estimate for unitary targets equipped with submultiplicative norms
  (operator norm and unnormalized Frobenius/Schatten norms). Normalized HS is
  not submultiplicative with dimension-free constants, and their paper
  explicitly leaves Hilbert--Schmidt approximability of Thompson groups open.
  Their fragmentation and bounded-generation mechanism is motivation, not a
  theorem implying `(TV2)`.
- More precisely, their final bounded-generation lemma is compatible with any
  bi-invariant norm once the relevant point-stabilizer has already collapsed:
  a fixed product costs only a fixed triangle-inequality factor. The missing
  input is collapse on `V(x)`. Their proof obtains it from uniform stability
  for submultiplicative norms, while `V(x)` itself is a directed union of
  copies of `V`. Replacing that input by pointwise normalized-HS estimates
  therefore recurses to the same problem and supplies no contraction.
- The deeper obstruction is `normalized-hs-tangent-quotient-is-nonabelian`:
  the asymptotic-cohomology proof first linearizes near-identity errors by
  making their tangent quotient abelian, and sparse Pauli blocks refute that
  step in normalized HS at exactly first order.
- The proof in the cited paper controls the uniform defect
  `sup_(g,h)||phi(gh)-phi(g)phi(h)||`, whereas a presentation microstate gives
  only pointwise/local control. Finite presentability does not bound the areas
  of all multiplication identities. Fixing `w` makes the final product
  telescoping finite, but does not provide uniform stability on `V(x)`.
- The Dudko--Medynets character theorem removes every intermediate limiting
  trace once a strict ceiling is proved, but it supplies no quantitative
  control on approximate representations by itself.
- Infinite-dimensional Cuntz/permutative representations do not furnish
  finite matrix microstates and therefore neither prove nor refute `(TV2)`.
- Full normalized-HS stability would prove `(TV2)` but is unnecessary. A
  successful argument may control only the one scalar moment
  `Re tr(w(U))`.
- No dimension-free group-algebra positivity or sum-of-squares identity valid
  in all tracial representations can prove `(TV2)`, because the exact regular
  representation has energy `2`. The missing estimate must be genuinely
  finite-matrix/Connes-embeddability sensitive.
- Pure prefix copying is also insufficient. The locally finite exact model in
  `affine-clone-model-defeats-pure-thompson-prefix-error-spreading` supports
  arbitrary finite refinement into commuting conjugate children and finite
  leaf symmetry while the root retains energy `2`. A live attack must isolate
  a specifically Thompson collision/overlap relation absent from that model.
- The cohomology-free permutation argument in the cited paper uses an exact
  finite-order return of a permutation shift. A unitary shift can have
  arbitrary continuous spectrum; cyclic `d`-shift matrices show that every
  return exponent may grow with `d`, reintroducing an uncontrolled word-area
  factor.
- Finite cutoffs and summable attempts to average over all possible return
  exponents are ruled out by
  `summable-power-return-detectors-miss-growing-cycles`: uniform `d`-cycle
  spectra converge to Haar moments and push every summable return weight into
  the tail. Only a constant-cost infinite family, coupled by a relation that
  also defeats the affine clone model, could evade both firewalls.
