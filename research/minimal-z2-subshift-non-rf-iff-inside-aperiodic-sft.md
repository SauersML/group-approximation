---
rg: 2
id: minimal-z2-subshift-non-rf-iff-inside-aperiodic-sft
kind: claim
title: A minimal Z^2 subshift fails residual finiteness exactly when it lies in a Z^2 SFT without periodic points, so the commuting-automorphism survivor exists iff the aperiodic-SFT question has a positive answer
distinct_from:
  zn-subshift-is-rf-iff-periodically-approximable: that proves the direction "inside a weakly aperiodic SFT implies non-RF" for any subshift; this proves the converse for minimal Z^2 subshifts, where non-RF forces a single window SFT to be strongly aperiodic.
  sfts-without-finite-orbits-are-not-residually-finite-actions: that is the obstruction for subshifts inside an SFT without finite orbits; this shows that for minimal Z^2 subshifts it is the only obstruction.
  rf-subshifts-are-periodic-window-approximable: that is the covering criterion at every window for any perfect subshift; this removes the covering clause under minimality and then upgrades weak to strong aperiodicity in rank 2.
  commuting-subshift-automorphisms-die-when-space-time-is-rf: that reduces the survivor to non-RF space-time subshifts and shows candidates are free minimal Z^2 subshifts with an expansive minimal direction; this closes the gap between "non-RF" and "inside an aperiodic SFT", making the survivor equivalent to the open SFT question.
  aperiodic-sft-minimal-subsystem-with-expansive-minimal-direction: that is the open existence question; this proves it equivalent to the existence of any commuting-automorphism survivor and corrects its claim that a negative answer would not kill the survivor.
artifacts:
  - research/minimal-z2-subshift-non-rf-iff-inside-aperiodic-sft-proof.md
---

**ESTABLISHED** (proof: `minimal-z2-subshift-non-rf-iff-inside-aperiodic-sft-proof`; swarm-0917 w14,
2026-09-19; elementary, unreviewed; no priority claimed).

## Theorem A (minimal Z^2 subshifts)

Let `Y ⊆ A^(Z^2)` be an infinite minimal `Z^2`-subshift. For a finite window `W` let `X_W(Y)` be its window
SFT, as in `rf-subshifts-are-periodic-window-approximable`. The following are equivalent.

- (a) `Z^2 ↷ Y` is not residually finite in the Kerr–Nowak sense.
- (b) Some window SFT `X_W(Y)` has no point with finite `Z^2`-orbit.
- (c) Some window SFT `X_W(Y)` has no point with a nonzero period.
- (d) `Y` lies in a `Z^2` SFT without periodic points, i.e. a strongly aperiodic one.

Under these conditions `Y` is free. So, for minimal `Y`, "non-RF", "inside a weakly aperiodic SFT" and
"inside a strongly aperiodic SFT" are the same condition.

## Lemma (freeness of minimal abelian actions)

A minimal action of an abelian group `Λ` is free iff it is faithful. The fixed set of `g ∈ Λ` is closed and
`Λ`-invariant, so it is empty or everything.

## Theorem B (the survivor question is the SFT question)

The following are equivalent.

- (i) `aperiodic-sft-minimal-subsystem-with-expansive-minimal-direction` holds.
- (ii) Some infinite minimal subshift `X ⊆ A^Z` and some `ψ ∈ Aut(X,T)` have a non-RF space-time subshift
  `Y_ψ`.
- (iii) Some infinite minimal subshift `X` and some block code `F` of some `ψ ∈ Aut(X,T)` violate
  `(*)_F` of `commuting-subshift-automorphisms-die-when-space-time-is-rf`. That is, there is `M` such that
  every periodic `y ∈ A^Z` has some iterate `F^j(y)`, `j ≥ 0`, containing a length-`M` word outside `L_M(X)`.
- (iv) Some minimal `Z^2`-subshift, not assumed free, has a rational direction that is both expansive and
  minimal and is not residually finite.

In (ii) and (iii), `ψ` automatically has infinite order modulo `⟨T⟩`, because `Y_ψ` is free by Theorem A.

## Corollary C (a negative answer kills the whole survivor class)

Suppose `aperiodic-sft-minimal-subsystem-with-expansive-minimal-direction` is false. Then, for every
infinite minimal `X`, every `ψ ∈ Aut(X,T)`, every prime power `q` and every `σ ∈ Aut(LC(X,F_q) ⋊_T Z)` with
`σ^m = Ad(w) ∘ σ_ψ^k`, condition `(G2)` of `simple-ring-with-centralizer-compressing-automorphism` fails.
This follows from Theorem 2 of `commuting-subshift-automorphisms-die-when-space-time-is-rf`, since every
`Y_ψ` is then RF by Theorem B.

**Correction.** `aperiodic-sft-minimal-subsystem-with-expansive-minimal-direction` states that "a negative
answer does not by itself kill the survivor, because a non-residually-finite `Y_ψ` need not lie in an
aperiodic SFT". That is false.
- `Y_ψ` is always minimal, because its horizontal shift is conjugate to `T` on `X`.
- A non-RF minimal `Z^2`-subshift always lies in an aperiodic SFT, by Theorem A.

Likewise, the qualifier "when `Y_ψ` sits inside an aperiodic SFT" in the gate consequence of
`commuting-subshift-automorphisms-die-when-space-time-is-rf` is always satisfied.

## Consequences

- **One question, two faces.** The commuting-automorphism survivor of the centralizer-compression gate is
  now a single dichotomy, with no third case left open.
  - *Positive:* an aperiodic SFT with a minimal subsystem carrying an expansive minimal rational direction.
    This gives a survivor that no permutation model reaches.
  - *Negative:* every such `σ` dies at `(G2)`.
- **One-dimensional form.** By (iii), the question is about one block code on `A^Z`. Is there an infinite
  minimal `X` with an automorphism code `F` and a scale `M` such that no periodic word keeps its forward
  `F`-orbit `M`-legal forever? For a fixed period `p`, `F` maps the finite set of `p`-periodic words to
  itself. So the forward orbit of each `p`-periodic `y` is eventually periodic, and checking it is a
  finite computation.
  - A search over `p` refutes a candidate `(X, F, M)` by finding a `p`-periodic word whose whole forward
    orbit stays `M`-legal.
  - Certifying a candidate needs an aperiodicity proof for `X_W(Y_ψ)`.
- **Where the aperiodic SFT comes from.** In (ii) ⇒ (i), the aperiodic SFT is the window SFT
  `X_W(Y_ψ)` itself, for the first window `W` at which (b) fires. So a positive answer needs no external
  tile set: a window SFT of the space-time subshift must be aperiodic. Conversely, a proof that every window
  SFT of every such `Y_ψ` has a periodic point is a complete negative answer.
- **Standing constraints transfer.** Any witness of (ii) must avoid the obstructions of
  `minimal-z2-directions-forbid-eigenvalues-vanishing-on-them`. `Y_ψ` has no non-cyclic finite factor and no
  quadratic toral factor with `Γ* ∩ Q^2 = 0`. Also, by Attempt 2 of the open question, no two points of
  `Y_ψ` differ only near a half-line.
