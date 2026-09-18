---
rg: 2
id: arithmetic-frames-are-capped-machines-live-in-orbits-not-words
kind: claim
title: Piece identifications from any class with exponentially bounded description growth under composition and a polynomial identity test (rational transducers, residue-class-affine Conway maps, piecewise-affine or projective maps with integer data) give operad groups with single-exponential word problem, so machine-universal piecewise maps cannot supply the non-finite-state frames; their universality lives in orbits, and residue-class operads even have unary squares
requires:
  - rational-frame-operads-are-capped-whatever-their-spine
  - complexity-bounded-host-classes-are-not-universal
  - symmetric-ore-operads-containing-their-carrier-are-full-groups
  - ct-p-z-has-the-ore-tree-presentation
distinct_from:
  rational-frame-operads-are-capped-whatever-their-spine: that caps finite-transducer frames; this caps every frame class whose composites grow at most exponentially in description size and admit a polynomial identity test, which covers the Conway, RCWA and piecewise-affine candidates proposed for the machine operad.
  ct-z-rational-base-machines-carry-a-potential: that closes one exact coding of rational-base machines inside CT(Z) by a conservation law; this shows that no residue-class or piecewise-affine frame system, exact or not, can make an operad host uncapped.
  ct-z-finite-cycle-problems-are-undecidable: that is an undecidable orbit-type question in CT(Z); this explains why such undecidability never reaches the word problem of hosts built from those maps.
---

**ESTABLISHED** (lane bh-typeA-universal, 2026-09-18). Elementary lane proofs below, not
independently reviewed. No priority claimed; the complexity facts about each frame class are
standard and recalled. This node answers the suggestion to realize the merged target R-b + R-c
of `rational-frame-operads-are-capped-whatever-their-spine` with piecewise-affine or Conway-type
identifications. **The answer is negative.**

## Sized frame classes

A **sized frame class** `𝔉` on a Cantor space `Z` is a family of homeomorphisms between clopen
subsets of `Z`, each with a finite description of size `|f|`. It must be closed under
composition, inversion and patching over finite clopen partitions described in the class, and
satisfy:
- **(S1) growth.** For every finite `F ⊆ 𝔉` there is `C_F` such that every composite of `n`
  elements of `F ∪ F^{-1}` has a description of size at most `C_F^n`, computable in time
  polynomial in `C_F^n`;
- **(S2) identity test.** Whether `f = id` on its domain is decidable in time polynomial in `|f|`.

## Statement

1. **Cap.** Take a dissection operad (setting of
   `symmetric-ore-operads-containing-their-carrier-are-full-groups`) whose generator frames,
   transformations and object identification lie in a sized frame class `𝔉`.
   - Then every finitely generated subgroup of its group has word problem in time `2^{O(n)}`.
   - The class of all such hosts, over all sized frame classes, is not
     universal (`complexity-bounded-host-classes-are-not-universal`, `T(l) = 2^l`).
   - No Ore, spine, square or refinement hypothesis is used.
2. **The classical machine-universal piecewise maps are sized.**
   - **(a) Finite transducers** (rational maps): this is
     `rational-frame-operads-are-capped-whatever-their-spine`. It includes generalized shifts
     (Moore), which are piecewise prefix replacements.
   - **(b) Residue-class-affine maps** (RCWA, Conway's generalized Collatz permutations, class
     transpositions). The size is the modulus times the coefficient bit-length.
     - Composing multiplies moduli (up to a factor from the denominators) and adds bit-lengths.
     - The identity test checks every class.
     - The same holds on `Ẑ_P` for the continuous extensions.
   - **(c) Piecewise-affine or piecewise-projective maps with integer or rational data** on
     rational polyhedral pieces, in `R^k` or its Cantorizations. This covers Koiran–Cosnard–Garzon
     type universal maps and the frames of the edge-split operad.
     - Composing multiplies the number of pieces and adds bit-lengths.
     - The identity test is exact linear algebra.
3. **Residue-class operads have unary squares.** Take the operad on `Ẑ_P` (or `Z`) whose
   generators split a residue class by a prime `p ∈ P`. The frames are canonical up to a finite
   group of affine symmetries.
   - Every square is unary: a `p`-split and a `q`-split meet in the classes modulo `pq` for
     `p ≠ q` (CRT), with exactly one split on each piece.
   - So Ore is automatic (`branching-squares-are-the-only-operadic-escape-from-the-cap`,
     Statement 1). This is the colour-exchange relation of `ct-p-z-has-the-ore-tree-presentation`.
   - For such operads, even the halting-theorem half R-b cannot occur.
4. **Consequence for the merged target.**
   - Frames that compute must lie outside every sized frame class. Their composites must admit no
     description of size `2^{O(n)}` with an identity test polynomial in that size.
   - The group they generate is then itself a carrier `Λ` with a hard word problem.
   - So the merged R-b + R-c target is exactly the operadic actor problem in the dynamics channel,
     namely a finite, symmetric Ore `Λ`-substitution (finite spine, or (G)_2) for a `Λ` of
     unboundedly hard word problem, as in Statement 3 of
     `symmetric-ore-operads-containing-their-carrier-are-full-groups`.
   - The mortal machine enters only through the Ore condition of that substitution.

## Proofs

1. **Cap.**
   - Each generating fraction agrees, on each piece of a finite clopen partition, with a
     composite of frames and inverse frames, as in the proof of
     `rational-frame-operads-are-capped-whatever-their-spine`. By closure under composition,
     inversion and patching, it is an element of `𝔉`.
   - A word of length `n` in a finite symmetric set `F` of such fractions is a composite of `n`
     elements of `F`. By (S1) it has a description of size at most `C_F^n`, computed in time
     polynomial in `C_F^n`.
   - Triviality is (S2), polynomial in the size. So the total time is `2^{O(n)}`, with the
     constant depending on `F`. This is the form required by
     `complexity-bounded-host-classes-are-not-universal` with `T(l) = 2^l`.
2. **The three classes.**
   - (a) is that node.
   - (b) An RCWA map is a modulus `m` and affine data `(a_r, b_r, c_r)` for each `r mod m`.
     - In `f∘g`, the class of `n` modulo `m_g·m_f·c_g` (with `c_g` the largest denominator of `g`)
       determines both affine pieces.
     - Along a composite of `n` maps from a finite set, coefficient bit-lengths grow additively,
       to `O(n)`, and the modulus grows by a bounded factor at each step, to `2^{O(n)}`. So (S1)
       holds.
     - `f = id` iff every piece is `n ↦ n`.
   - (c) Pieces of `f∘g` are intersections of a piece of `g` with the preimage of a piece of `f`.
     - Their number is at most the product of the two counts, and each is cut out by the
       hyperplanes of both.
     - Matrices multiply with additive bit growth.
     - The identity test compares each piece's matrix with `I`, using exact rational arithmetic.
3. **Squares.** For `p ≠ q`, a class `r + mẐ` split by `p` has children `r + jm + pmẐ`.
   - The `q`-split of the parent has pieces `r + im + qmẐ`. By CRT each of them meets the child
     `r + jm + pmẐ` in exactly one class modulo `pqm`.
   - So on each child the `q`-split restricts to a partition into `q` classes modulo `pqm`. In the
     child's canonical frame `x ↦ (x − r − jm)/(pm)`, this is the partition into the `q` classes
     modulo `q`, i.e. one `q`-split of the child.
   - Two splits by the same prime have the same pieces. Their frames then differ by a finite
     affine symmetry, which is a transformation.
   - So some common multiple has at most one generator on each piece, and (U) holds.
4. **Consequence.** This follows from 1 and 2 together with Statement 3 of the saturation node,
   whose carrier is the group generated by the frames' germs. ∎

## Where machine universality lives

Moore's generalized shifts, Conway's permutations and piecewise-affine maps simulate Turing
machines through their **iterates**, and reachability and orbit questions about them are
undecidable. Examples are Conway's theorem and `ct-z-finite-cycle-problems-are-undecidable`.

The word problem of the group they generate never iterates one map an unbounded number of
times without the word saying so. It only composes the `n` maps named in the word, and 1 shows
that composing costs at most `2^{O(n)}` for sized classes.

This is bh-kourovka-2174a's dichotomy from the host side:
- thin questions (orbits, cycles, reachability) are undecidable;
- the thick question that matters for hosts, the word problem, is capped.

## Lesson for general BH

**Machine-universal maps are capped as groups: their universality lives in orbits, not in
words.** Any host built from piece identifications with polynomially describable composites is
capped at single-exponential word problem, however universal the iterates of those maps are.
This covers finite transducers, Conway and RCWA maps, and integer piecewise-affine maps.

So the machine operad cannot be assembled from a clever frame class. Its frames must already
generate a group with a hard word problem, and then the task is the operadic actor problem
itself: a finite Ore `Λ`-substitution for a hard `Λ`.

The mortal machine belongs in the Ore condition of that substitution, not in the frames. This is
the carrier principle once more, now stated as a theorem about frame classes.
