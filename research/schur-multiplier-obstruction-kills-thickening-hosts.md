---
rg: 2
id: schur-multiplier-obstruction-kills-thickening-hosts
kind: claim
title: Schur multiplier obstruction — an FP_2 group with a perfect normal subgroup N and FP_3 quotient has finitely generated H_2(N)_Γ; so no residually finite thickening host over an FP_3 acting group is finitely presented, including the projective SL_d(Z[1/2]) candidate
distinct_from:
  affine-thickening-hosts-are-never-fp: that uses periodized fake actions and works for every affine acting group, FP_3 or not; this is a homological argument that works for every acting group of type FP_3, affine or not, and decides the projective candidate.
  neumann-projective-host-candidate: that built the higher-rank projective host and left finite presentability open; this proves it is not finitely presented.
  neumann-alternating-product-group-embeds-in-fp-rf-group: that is Minasyan's open question; this rules out every host in which the coordinate alternating groups stay normal factors over an FP_3 quotient.
---

**ESTABLISHED** (lane bh-free-59, written inline, not independently reviewed). Textbook
inputs: the Lyndon–Hochschild–Serre spectral sequence; `H_2` of a finitely presented group
is finitely generated; `H_2(A_n; Z) ≠ 0` for `n ≥ 4`; S-arithmetic groups are of type
`FP_∞` (Borel–Serre).

## The lemma

**Lemma.** Let `Γ` be of type `FP_2` (for instance finitely presented), and let `N ◁ Γ` be
**perfect**. Suppose `Q = Γ/N` has finitely generated `H_3(Q; Z)` (for instance `Q` of type
`FP_3`). Then the coinvariants `H_2(N; Z)_Γ` are finitely generated.

*Proof.* In the LHS spectral sequence `E^2_{p,q} = H_p(Q; H_q N) ⇒ H_{p+q}(Γ)`, the bottom
piece of `H_2(Γ)` is

    E^∞_{0,2} = H_2(N)_Q / (im d_2 + im d_3).

- The source of `d_2` is `H_2(Q; H_1 N) = 0`, because `N` is perfect.
- The source of `d_3` is `E^3_{3,0} = H_3(Q)`, because `H_1(Q; H_1 N) = 0`. It is
  finitely generated.
- `E^∞_{0,2}` is a subgroup of the finitely generated group `H_2(Γ)`, hence finitely
  generated.

So `H_2(N)_Q` is an extension of finitely generated groups. The coinvariants under `Q`
equal those under `Γ`, since `N` acts trivially on its own homology. ∎

**Corollary A (normal direct sums).** Suppose an `FP_2` group `Γ` has a normal subgroup
`K = ⊕_{i∈I} S_i`, with `I` infinite and each `S_i` a finite perfect normal subgroup such
that `H_2(S_i)_Γ ≠ 0`. This holds for example when `S_i ≅ A_{n_i}` with the `n_i` pairwise
distinct and `≥ 8`, since `Aut` acts trivially on `Z/2`. Then `H_3(Γ/K; Z)` is not
finitely generated.

*Proof.* `H_2(K)_Γ = ⊕_i H_2(S_i)_Γ` (Künneth: the cross terms vanish because the factors
are perfect), and this is infinitely generated. So the image of `H_3(Γ/K)` must be
infinite. ∎

## The theorem for thickening hosts

**Theorem.** Let `Γ = N ⋊ Q ≤ ∏_{m∈S} Sym(X_m)` with `S` infinite, and suppose:
- (i) `N` is perfect;
- (ii) for each `m ∈ S`, `N` contains the coordinate factor `Alt(X_m)`, meaning the
  elements supported in coordinate `m` alone, and the coordinate projection
  `ρ_m: N → Alt(X_m)` is onto;
- (iii) `|X_m| ≥ 5`;
- (iv) `H_3(Q; Z)` is finitely generated.

Then `Γ` is **not finitely presented**, and not even of type `FP_2`.

*Proof.* Let `ι_m` be the inclusion of the coordinate factor. Then `ρ_m ι_m = id` and
`ρ_{m'} ι_m = 1` for `m' ≠ m`. Conjugation by `γ ∈ Γ` acts on coordinate `m` by an
automorphism of `Alt(X_m)`, which acts trivially on `H_2(Alt(X_m)) ≅ Z/2` (or `Z/6`). So
each `ρ_{m*}` factors through `H_2(N)_Γ`. The image of `H_2(N)_Γ → ∏_m H_2(Alt(X_m))`
contains `⊕_m H_2(Alt(X_m))`, via the `ι_{m*}`. That is infinitely generated, which
contradicts the Lemma. ∎

**Hypotheses hold for every host built so far.** Take `N` to be the normal closure of the
3-cycle `α`.
- (i) `α` lies in the window copy of `A_5`, on five points distinct in every coordinate,
  and `A_5` is perfect.
- (ii) The window proposition of `neumann-group-is-locally-finite-by-z-and-not-fp`
  gives a nontrivial element supported in coordinate `m` alone. Its normal closure in `N`
  is the whole coordinate factor, because `ρ_m(N) = Alt(X_m)` is simple.

So:
- **`neumann-projective-host-candidate` is decided: `⟨SL_d(Z[1/2]), α⟩` on `P^{d-1}(Z/m)`
  is not finitely presented**, for every `d`, because `SL_d(Z[1/2])` is S-arithmetic,
  hence `FP_∞`.
- The same proof covers:
  - Neumann's group (`Q = Z`);
  - the doubling host (`Q = BS(1,2)`);
  - the `ASL_d(Z[1/N])` hosts;
  - any thickening over an `FP_3` group, linear or not, higher rank or not.
- Rigidity of `Q` (NST, CSP) is irrelevant. The obstruction lives in the fibre `N`, not in
  the dynamics.

## Consequence for MO 491978

A finitely presented host `Γ ⊇ G` can never have a perfect normal subgroup that contains
the coordinate factors `A_m` as retracting normal factors over an `FP_3` quotient. By
Corollary A, if `Γ` has `⊕A_m` itself as a normal subgroup, then `Γ/⊕A_m` has infinitely
generated `H_3`. In every finitely presented host, the alternating subgroups must
therefore fail to be "coordinates":
- finite quotients of the host must mix them;
- infinitely many of their Schur classes must die in `H_2` of the host.

This is a necessary shape for any positive answer. The question itself stays open.

## Lesson for general BH

**Check `H_2` of the fibre before designing a host.** For every candidate of the form
`N ⋊ Q` with `N` perfect and `Q` of type `FP_3`, finite presentability forces
`H_2(N)_Γ` to be finitely generated. Infinitely many independent normal pieces with
nonzero Schur multiplier are fatal, and no amount of rigidity in `Q` helps.

This one-line spectral-sequence test replaces the fake-action constructions whenever the
acting group is `FP_3`. It applies verbatim to Boone–Higman host designs:
- Houghton-type hosts `Alt_fin(X) ⋊ Q` carry one Schur class, so they pass;
- any "restricted product over infinitely many coordinates" fails.
