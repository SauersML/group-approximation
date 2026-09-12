---
rg: 2
id: higman-embedding-preserves-occurrence-coset-separation
kind: claim
title: A malnormal quasi-isometric Higman embedding preserves occurrence cosets and sign double cosets
distinct_from:
  colored-cayley-pauli-incidence-separation: that must first construct a recursively presented separated occurrence address group; this proves that finite presentation can be imposed afterward without losing its algebraic separation.
  quantitative-higman-embedding-with-dehn-control: that controls distortion and Dehn area for a computation group; this uses injectivity for cosets and Wagner's malnormal congruence-extension refinement for the occurrence and phase data.
  phase-safe-toric-gap-game-exists: that asks for a game whose scalar phase survives clause normal closure; this only says an already proved normal-closure separation survives the chosen embedding.
artifacts:
  - research/artifacts/relative-small-cancellation-occurrence-support-2026-08-21.md
---

Let `G` be finitely generated and recursively presented.  Let `H_X,H_Z<=G`
be finitely generated, let `P_0,P_1` be finite, and suppose selected occurrence
cosets are distinct and

```text
H_X P_0 H_Z intersect H_X P_1 H_Z = empty.             (HOC1)
```

Wagner, arXiv:2404.00841v2, Theorem A, embeds `G` quasi-isometrically and
malnormally as a congruence-extension subgroup of a finitely presented group
`A`.  Under this embedding:

1. every selected left/right coset remains distinct;
2. the two image double cosets remain disjoint;
3. every finite offset set is represented by a finite set of words of one
   fixed maximum length in `A`; and
4. for every `S subset G`,

   ```text
   G intersect <<S>>_A = <<S>>_G,                     (HOC2)
   ```

   after identifying `G` with its image.

The first three conclusions need only injectivity (and finite generation for
the bounded offset list).  The fourth is Wagner's congruence extension
property.  Thus neither occurrence separation nor an already established
phase/normal-closure firewall is lost in the final finite-presentation step.

For a countable source with a computable length function, Wagner's Corollary B
gives the analogous finitely presented malnormal/CEP embedding.  The theorem
does not manufacture the separated source group, and it does not turn
unbounded source edge words into bounded offsets; the occurrence construction
must provide a finite offset alphabet before embedding.
