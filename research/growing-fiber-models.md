---
rg: 2
id: growing-fiber-models
kind: route
title: Growing-fiber models with no surviving coarse index set
target: hyperlinear-wreath-model
requires: [fiber-masa-free-cocycle]
artifacts:
  - notes/TRUE_BLOCK_MONOMIAL_COORDINATE_COLLAPSE.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

# Growing-fiber models with no surviving coarse index set

The architecture that survives `coordinate-action-not-sofic`, stated in the
only form the demolition below leaves standing.

## Where the room is

`coordinate-action-not-sofic` says a hyperlinear model of `W` cannot have
permutation normalizers for the lamp algebra. It does **not** say the lamps
cannot sit in a diagonal: Kun–Thom Corollary D forbids the pair (diagonal
lamps, permutation group unitaries), not the first half alone. And the first
half is free — the repository's diagonalization lemma conjugates any separable
abelian trace-preserving image into the diagonal ultraproduct, since it has a
self-adjoint generator whose representing matrices can be diagonalized one at
a time.

So the only thing a model must avoid is permutation-ness of the `Θ(u_g)`. The
natural currency is a fiber the lamps cannot see: model space
`ℂ^{Y_n} ⊗ ℂ^{m_n}` with `m_n → ∞`, lamps in `D_{Y_n} ⊗ 1`, and the group's
Hilbert–Schmidt separation stored in the `U(m_n)` part. Trace is additive
under refinement, so it cannot tell a block from a point — this is precisely
the trace-blindness the flexible branch has been looking for, and `τ(Θ(u_g))`
genuinely bears no relation to the fixed-point fraction of any coordinate
permutation.

## The demolition, and why it fixes the specification

The naive version of that idea is dead, unconditionally
(`block-monomial-coordinate-collapse`, proved in the artifact). If the
`Θ(u_g)` are exactly block-monomial over `Y_n`, then:

- permutation parts exist and are a homomorphism on `U(m) ≀ Sym(Y)`;
- `‖A − B‖₂² ≥ 2 d_H(π(A), π(B))` **uniformly in `m`**, because a mismatch of
  permutation parts displaces a whole unitary block, so multiplicativity of
  `Θ` descends to the permutation parts;
- conjugating `D_{Y_n} ⊗ 1` by a block-monomial cancels the blocks exactly, so
  the lamps stay covariant for those permutations, and faithfully so;
- the one thing the fiber bought — non-faithfulness on `G` — is bought back
  for free by tensoring with a sofic representation of `G`, which exists
  because `G` is residually finite.

What comes out is a genuine sofic-action witness, contradicting Corollary D.
The trace really is blind to the fiber; the obstruction simply does not live
there. It rides on the lamps, and the lamps are on the coordinates.

That is why this route requires `fiber-masa-free-cocycle` rather than "build a
fiber model". The requirement is not that no *masa* be invariant — that would
be the weaker condition `diagonal-normalizer-rigidity` already handles, and its
own sharpness note (the Fourier block `⊕_j F_m` centralizes a coarse
subalgebra at distance `√2` from every monomial) is exactly the case the
collapse shows is not a door. The requirement is that no **coarse index set**
survive: no splitting `ℂ^{d_n} ≅ ℂ^{Y_n} ⊗ ℂ^{m_n}` carrying the lamps on
`Y_n` may be preserved, and since such a splitting is always present
approximately — a window of `k` lamps has `2^k` atoms of equal trace — the
content is that its defect stay bounded away from zero.

## Why the defect could be non-zero, and where that leaves things

The defect for the atom decomposition of a window `E ⊆ G/Γ` is controlled by
the boundary of `E` under the `G`-action, and `G ↷ G/Γ` has no Følner sets:
property (T) with infinite index. So the boundary carries a constant fraction,
and one mismatched coordinate costs a configuration-space defect of order one.
That is the amplification obstruction of `notes/OBSTRUCTIONS.md` §3, and on this
reading it changes sign: it has always been recorded as an argument against
models, and it is the only known *source* of the non-vanishing defect a model
now has to exhibit. The open question is whether amplification supplies the
defect or destroys the model first. That is one quantitative question about one
number, which is a considerably better position than a search for an
architecture.

## Not a variation on the recorded dead architectures

Not a finite quotient of `G` — the coordinate part no longer carries
separation, but it still cannot come from a finite quotient, since finite
quotients collapse `G/Γ` to `G/⟨⟨Γ⟩⟩` and take the lamps with them. Not a
free-probability carrier — the carrier is `∏_𝒰 M_{d_n}`, which contains
`L(G) ⊇ L(Γ)`, a diffuse (T) algebra, with no Haagerup property in sight. Not
a half-space tensor model — the fiber is not a one-sided shift and there is no
tail to fall into. Not a one-variable Laurent fiber, and not a graded tower —
nothing is graded and nothing shifts levels.

Both standing diagnostics pass. `no_strict_compression_of_invariantSize` does
not bite: the carrier is a `II₁` ultraproduct whose only conjugation-invariant
size is the trace, and `notes/OBSTRUCTIONS.md` §1 shows the blindness of the
trace to refinement is sharp, so no invariant argument can settle this branch.
(T)-compatibility costs nothing: `G` is residually finite, hence sofic, hence
hyperlinear, so `L(G)` is already Connes-embeddable. The entire difficulty is
the lamps, and the entire difficulty in the lamps is now one defect estimate.
