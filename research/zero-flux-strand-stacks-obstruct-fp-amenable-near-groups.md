---
rg: 2
id: zero-flux-strand-stacks-obstruct-fp-amenable-near-groups
kind: claim
title: A group without free subgroups that acts on a Z-indexed stack of strands with equal offset speed at both ends, containing a uniform stack shift and a non-uniform kernel element, is not finitely presented; for polyhedral enumerations of Z^2 this kills every enumeration with an active zero-flux slice, including isometric ones
requires:
  - fp-groups-without-free-subgroups-split-ascendingly-over-kernels
  - piecewise-translation-z2-enumerations-are-not-fp
  - houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group
  - houghton-like-envelope-fp-pins-the-enumeration-by-near-relators
distinct_from:
  piecewise-translation-z2-enumerations-are-not-fp: that is the translation-only case for Z^2, where zero flux is automatic; this isolates the mechanism as an algebraic lemma about stack germs, allows strands to migrate out of the stack, and extends the kill to piecewise-isometric enumerations whose flux character vanishes at an active slice.
  houghton-like-envelope-fp-pins-the-enumeration-by-near-relators: that is the pinning side (fp forces rigid near relators); this shows that the rigid relators of linear type produce strand stacks, and that zero-flux stacks are then fatal whenever the near group has no F_2.
  fsym-extensions-lift-fp-via-pair-transitive-stable-subgroups: that is a sufficient lifting criterion; this is a necessary germ-level condition.
---

**ESTABLISHED** (lane proof, below, not independently reviewed, no priority claimed; the lemma is a Bieri–Strebel
tameness argument in permutational form).

## Lemma (zero-flux strand stacks)

**Stack germs.** Let `S` be a set containing a copy of `Z`, the *stack*. Let `W(S) = Z^S ⋊ Sym(S)` act on `S x N`
as germs, by `(c, k) -> (π(c), k + m_c)` for `k ≫ 0`, so that `m_c(gh) = m_c(h) + m_(π_h(c))(g)`.
Let `R` be a group with a homomorphism `γ : R -> W(S)` such that, for every `g ∈ R`:
- on stack offsets, `π_g(c) = c + χ(g)` for `c ≪ 0` and for `c ≫ 0`, with **the same** `χ(g) ∈ Z` at both ends
  (*zero flux*);
- `m_c(g)` is constant for `c ≪ 0` and for `c ≫ 0`, with values `m_-(g)` and `m_+(g)`.

Call `g` *uniform* if `π_g` translates the whole stack by `χ(g)` and `m_c(g)` is constant on the stack. Suppose:
- (i) some `t ∈ R` is uniform with `χ(t) ≠ 0`;
- (ii) some `g ∈ ker χ` is not uniform.

Then either `R` contains a free subgroup of rank 2, or `R` is not finitely presented.

**Proof.**
- `χ`, `m_-` and `m_+` are homomorphisms. Rescale `χ` to be onto `Z`.
- If `R` is finitely presented and has no `F_2`, then `fp-groups-without-free-subgroups-split-ascendingly-over-kernels`
  gives a finitely generated `H ≤ ker χ` and `w` with `χ(w) = ε = ±1` and `ker χ = ∪_(k≥0) w^k H w^-k`.
- **Case `ε = -1`.** Choose `M` such that:
  - every generator of `H`, and its inverse, fixes each stack offset `c ≥ M` with `m_c = m_+`;
  - `π_w(c) = c - 1` for `c ≥ M`.
- Both properties at `c ≥ M` are closed under products in `ker χ`, so all of `H` has the first one.
  `π_(w^-k)` maps `[M, ∞)` into itself.
- For `x = w^k h w^-k` and `c ≥ M`, put `c' = π_(w^-k)(c)`. Then `π_x(c) = c`, and
  `m_c(x) = m_c(w^-k) + m_+(h) + m_(c')(w^k) = m_+(h) = m_+(x)`.
- So every element of `ker χ` is `+`-uniform on `[M, ∞)`.
- By (ii) there is `c_+` with `π_g(c_+) ≠ c_+` or `m_(c_+)(g) ≠ m_+(g)`. For `x_k = t^k g t^-k ∈ ker χ` one has
  `m_c(x_k) = m_(c - kχ(t))(g)`. So `x_k` fails at `c_+ + kχ(t)`, which lies in `[M, ∞)` for suitable `k`.
  Contradiction.
- **Case `ε = +1`** is symmetric, with `c ≤ -M` and `m_-`. ∎

Nothing leaves the stack in the zone `c ≥ M`. Strands may migrate between the stack and `S \ stack` elsewhere.

## Corollary (polyhedral enumerations of Z^2, isometries allowed)

**Setting.** `nu : Z^2 -> N` has successor map `sigma` that agrees, off a finite set, with lattice isometries
`x -> Ax + b` on the pieces of a finite polyhedral partition, with all `A` in a finite subgroup `Γ ≤ GL_2(Z)`.
- `Θ` is the `Γ`-orbit of the critical directions of `sigma`.
- `R_0 ≤ R_nu` is the finite-index subgroup acting trivially on the arcs of `S^1 \ Θ` and with trivial linear part
  on each arc. On arc `I_j` it acts by translations `τ_j`.
- `S` is the set of far half-line germs `(θ, c)` in the directions `θ ∈ Θ`, and the stack at `θ` is `{θ} x Z`.
- As in Steps 0–3 of `piecewise-translation-z2-enumerations-are-not-fp`, applied to all slices together, every
  `g ∈ R_0` gives an element of `W(S)`. Its offset speeds at the two ends of slice `θ` are
  `χ_(θ,±)(g) = <n_θ, τ_±(g)>`. `R_0` has no `F_2`: `ker(τ_j)_j` embeds in `Z^(S) ⋊ FSym(S)`.
- The **flux character** at `θ` is `φ_θ = χ_(θ,+) - χ_(θ,-)`. Call `θ` *active* if some `g ∈ R_0` is not uniform
  on its stack.

**Statement.** If some active `θ` has `φ_θ ≡ 0` on `R_0`, then `R_nu` is not finitely presented. Hence none of
`E_nu(Z^2)`, `H_n(E_nu(Z^2))` (`n >= 1`) or the shell germ group is.

*Proof.* Apply the Lemma to `R_0` at the stack of `θ`, with `t = L_h` for `<n_θ, h> = 1` (uniform everywhere) and
with `g · L_h'` for an active `g`, choosing `h'` so that the product lies in `ker χ`. `R_nu` is a finite extension
of `R_0`. ∎

**Flux holonomy.** Suppose `sigma` has the same linear part on both sides of every critical ray. Then `sigma`
permutes slices by some `φ`, and `φ_θ(g)` is a sum of the transverse jumps `f(θ')` of `sigma` along the slice path
that the letters of `g` trace.
- For example, suppose the four rotated copies of a quadrant are enumerated in turn from a diagonal enumeration.
  There `f` sums to zero around the single slice cycle, so `φ ≡ 0` and the enumeration dies. This was checked by
  hand on `sigma^4` and on the conjugates `sigma L_h sigma^-1`.
- A survivor needs nonzero holonomy: two slice cycles with opposite flux, so that `sigma` transports half-lines from
  one slice to another.

## Lesson for general BH

- The Houghton `n >= 3` phenomenon recurs one level up, inside the near group.
  - A Z-indexed stack of strands is an `H_2`-type object: its two ends have antipodal inward characters.
  - An active stack with zero flux is fatal for finite presentation whenever the near group has no `F_2`.
- So an amenable germ group can be finitely presented only if every active stack has nonzero flux character. Then
  its ends behave like the three or more rays of `H_n`.
- Combined with pinning (`houghton-like-envelope-fp-pins-the-enumeration-by-near-relators`), which needs rigid
  near relators:
  - rigid **linear** relators create stacks;
  - so the only envelopes that can survive are those with transported stacks, or those whose near group contains
    `F_2`.
- In the `F_2` case, antipodal pairs in `Σ^c` are allowed and this obstruction says nothing. That case (one-ended
  inputs containing `F_2`) is exactly where Boone–Higman is open. A route kill there needs a mechanism not based on
  Σ-invariants.
- **Sharpening (after bh-free-48).**
  - Case (b) does not depend on `nu`: `R_nu ⊇ lambda(P)`, so every input containing `F_2` has `R_nu ⊇ F_2` for
    every enumeration.
  - Pinning cannot supply the missing step. Polyhedral one-ended designs pass it
    (`square-spiral-z2-enumeration-is-ball-rigid`).
  - So the gates split: pinning kills generic, free and infinite-index-supported designs, and zero flux kills
    F_2-free polyhedral designs. Inputs containing `F_2` need an obstruction that works for non-amenable near groups.
