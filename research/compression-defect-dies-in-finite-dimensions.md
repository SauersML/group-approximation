---
rg: 2
id: compression-defect-dies-in-finite-dimensions
kind: claim
title: Every finite-dimensional representation kills the whole compression-centralizer defect
distinct_from:
  compression-wreath-five-radicals-coincide: that computes five residuals of one concrete doubling family and identifies them with the telescope kernel; this is the general sterility theorem for the intrinsic defect of an arbitrary pair L <= H, with no family and no approximation property attached.
  commutant-no-growth: that says commutants do not grow under genuine finite-dimensional representations, the mechanism; this is the resulting statement about the defect subgroup lying in every such kernel.
  infinite-cyclic-compression-lamp-mf: that exhibits a group whose nontrivial defect survives inside a faithful MF group; this is the theorem saying the defect always dies in finite dimensions. Together they are the two halves of the phase boundary.
  unsquared-defect-finite-model-invisible: that is the same phenomenon for one specific element u = [t c t^-1, v_1] of one specific group E; this is the general theorem for the whole defect subgroup of an arbitrary pair L <= H, of which that claim is an instance.
artifacts:
  - GroupApproximation/Criterion/CompressionCentralizerDefect.lean
  - GroupApproximation/Criterion/FiniteDimensionalKill.lean
  - research/artifacts/strong-atiyah-audit-2026-08-17.md
  - research/artifacts/finite-memory-self-hashing-non-mf-2026-08-23.md
---

For `L <= H` put

    Comp(L)   = { s in H : s L s^{-1} <= L }        one-sided compressors
    G_comp(L) = < Comp(L) >
    D(H,L)    = << [ g z g^{-1}, l ] : g in G_comp(L),
                     z in C_H(L), l in L >>_H

the **intrinsic compression--centralizer defect**, a normal subgroup of `H`.

**Claim.**  For every field `k`, every finite-dimensional `k`-vector space
`V`, and every homomorphism `pi : H -> GL_k(V)`,

    D(H,L) <= ker pi.

ESTABLISHED and machine-checked:
`compressionCentralizerDefect_le_ker` in
`GroupApproximation/Criterion/CompressionCentralizerDefect.lean`, over Lean
definitions (`compressionSet`, `compressionGroup`,
`compressionCentralizerDefectSet`, `compressionCentralizerDefect`) that match
the display above verbatim, including the generator shape.

## Where the hypothesis is spent

Exactly once, and it is worth knowing where.  Conjugation by `pi(s)` carries
the commutant `C` of `pi(L)` into itself for every compressor `s`; the map is
injective and `C` is finite-dimensional, so it is **surjective**, and hence
every element of `G_comp(L)` normalizes `C`.  Finite dimension is used for
that injective-implies-surjective step and nowhere else.

That is why the theorem extends verbatim to any target where a finite
dimension can be recovered -- centrally finite division rings
(`compression-defect-dies-in-centrally-finite-division-rings`), and then
weakly locally finite ones -- and why it fails beyond them.  It is also why
`infinite-cyclic-compression-lamp-mf` is not a contradiction: an infinite
compressor index gives the commutant room to grow.

This node was created on 2026-08-17 for a theorem that had been formalized
here for some time without ever being stated in the graph; it was noded
because two division-ring extensions and one refutation all hang off it.

## One-step self-copy interpretation

The proposed finite-memory HNN detector is not a new theorem and should not be
duplicated.  If an ascending HNN letter conjugates a parent group into one
child while a sibling packet centralizes that child, the sibling lamp is an
element of the parent commutant and the HNN letter is a one-sided compressor.
`map_marked_commutator_eq_one` then kills the sibling's transported marked
commutator in every finite-dimensional representation.  Its proof is exactly
the finite-algebra argument: an injective conjugate copy of the commutant is a
same-dimensional subspace contained in it, hence equal to it.
