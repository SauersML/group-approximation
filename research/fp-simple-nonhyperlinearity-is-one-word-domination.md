---
rg: 2
id: fp-simple-nonhyperlinearity-is-one-word-domination
kind: claim
title: One word detects nonhyperlinearity of a finitely presented infinite simple group
distinct_from:
  hyperlinear-radical-presentation-compactness: That characterizes one word in the hyperlinear radical for an arbitrary finite or recursively enumerable presentation; this uses simplicity to identify that one-word condition with nonhyperlinearity of the whole group and also adds the linear character-domination form.
  character-domination-collapse-equivalences: That linearizes phase-insensitive finite-dimensional character collapse for an arbitrary group, finite relator set and word; this identifies its qualitative hypothesis with the hyperlinear radical of a presented simple quotient.
  thompson-v-ce-one-word-trace-face-is-binary: That computes a zero-or-two support value over Connes-embeddable traces of Thompson V; this characterizes, for any finitely presented infinite simple group, when a relator-defect collapse modulus and a finite-dimensional character-domination constant exist.
---

Let

```text
G = <S | R>
```

be a finitely presented infinite simple group, and fix a word `w in F(S)`
whose image `wbar` in `G` is nontrivial.  For a unitary tuple
`U in U(d)^S`, write `g(U)` for evaluation of `g in F(S)`.  For the
normalized character `chi` of an exact finite-dimensional unitary
representation of the free group `F(S)`, put

```text
q_chi(g) = 1-|chi(g)|^2.
```

The following are equivalent.

1. `G` is nonhyperlinear.
2. The word `w` has a dimension-free normalized-HS collapse modulus: for
   every `epsilon>0` there is a `delta>0` such that, for every `d` and every
   `U in U(d)^S`,

   ```text
   max_(r in R) ||r(U)-I||_(2,d) < delta
   => ||w(U)-I||_(2,d) < epsilon.
   ```

3. There is a finite constant `C>=0`, independent of the matrix dimension,
   such that every normalized finite-dimensional unitary character `chi` of
   `F(S)` satisfies

   ```text
   q_chi(w) <= C sum_(r in R) q_chi(r).                 (FS1)
   ```

The two quantitative formulations meet through the same statement:
`wbar` belongs to the hyperlinear radical of `G`.  They are not a
term-by-term comparison of their defects.  In particular, `q_chi(r)=0` can
hold when the matrix assigned to `r` is a nontrivial scalar, so `(FS1)` does
not directly control the scalar phase measured by `||r(U)-I||_(2,d)`.
Conjugate doubling removes that phase in the character-radical argument.

For a finitely presented infinite simple group, one nontrivial word is
therefore enough: finiteness of its optimal character-domination constant,
or existence of its normalized-HS collapse modulus, proves
nonhyperlinearity of the entire group.  Equivalently, the conditions hold
for some nontrivial `wbar` if and only if they hold for every nontrivial
`wbar`.
