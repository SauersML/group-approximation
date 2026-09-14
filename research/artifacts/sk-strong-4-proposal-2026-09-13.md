# sk-strong-4 proposal

Line numbers refer to main's `simple_kazhdan_sofic_group.tex` at rev1 (5b1890ce6c).
Status of everything below: established with full proofs in
`research/artifacts/sk-strong-4-boundaries-2026-09-13-part1.md`, unreviewed, queued with
sk-verify-4.

## P1 (recommended): the general statement says "topologically free", not "free"

This is for the lanes that state the theorem over an arbitrary acting group
(sk-draft-general, sk-general-actions-a, sk-universal-embedding-a/-b, sk-lef-embedding-c/d/e).
The manuscript over `Z` is unaffected, since an infinite minimal `Z`-subshift has no periodic
points and the action is free.

(a) Current general form, `finite-model-subshift-elementary-groups-simple-kazhdan-lef`:

    Let Γ be a finitely generated group acting on A^Γ, and X ⊆ A^Γ an infinite minimal
    subshift on which Γ acts freely.

Replacement:

    Let Γ be a finitely generated group acting on A^Γ, and X ⊆ A^Γ an infinite minimal
    subshift on which Γ acts topologically freely.

(b) The proof changes in one place. Where the current argument takes a clopen partition into sets
`C` with `C ∩ γC = ∅` for `γ` in a ball, it instead takes small sets inside every atom of the
constancy partition. Those sets do not cover `X`, but they cover a dense open set, and the
identities the argument extracts are vanishing statements about locally constant functions, which
a dense set decides. Proposition 3 of part 1 is the replacement, written out.

(c) Length: no change in the manuscript. In a general statement, `-1` word.

(d) Reader-facing trade-off: strictly more general at the same length, and by the equivalence
`clopen-towers-at-every-scale-iff-topologically-free` it is the exact hypothesis, so nothing is
left on the table. No new machinery and no new fact to trust.

(e) Status: `binary-el-simple-iff-minimal-topologically-free` and
`clopen-towers-at-every-scale-iff-topologically-free`, both established, unreviewed.

## P2 (recommended, for whoever writes the RF-embedding corollary)

Decision 22 budgets at most 20 lines for "every finitely generated residually finite group embeds
in an infinite finitely generated simple Kazhdan LEF group". Its current proof spends a step on
`rf-toeplitz-subshifts-act-freely`, because Theorem T supplies only a free dense orbit and the
tower argument was believed to need freeness at every point. That step is now unnecessary for the
simplicity half:

    An action with a dense free orbit is topologically free: a fixed nonempty clopen set would
    meet that orbit.

So the corollary can quote Theorem T as it stands. This shortens the corollary's proof and removes
one lemma from the chain.

## P3 (optional, only if the manuscript states a general theorem): the boundary as a remark

If a general version is adopted, the following two sentences make the hypothesis sharp at a cost
of 3 lines. They are a theorem, not a comment on the proof.

```latex
For any countable group $\Gamma$ acting on a compact zero-dimensional space, $\EL_n$ of the
crossed product over $\F_2$ is simple if and only if the action is minimal and topologically
free, and it then has trivial center. An infinite minimal subshift over $\Z$ has no periodic
points, so both conditions hold.
```

Reader-facing trade-off: it tells the reader exactly which systems the construction covers, and
the converse half costs one citation to the Steinberg algebra simplicity criterion. Against it:
the manuscript is about `Z`, where the equivalence adds nothing to Theorem 1. My recommendation is
to include it only in a general draft, not in the `Z` note.

## Not proposed
- A hypotheses paragraph for the `Z` note: decision 20 settled this, and part 2 of the artifact
  supports it. The hypotheses are visibly used.
- Any `F_q` remark from this lane: the binary scalar step does not generalize, and sk-coefficients
  owns that case.
- The boundary map itself: it is a working document for the swarm, not manuscript material.
