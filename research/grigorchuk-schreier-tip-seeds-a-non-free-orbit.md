---
rg: 2
id: grigorchuk-schreier-tip-seeds-a-non-free-orbit
kind: claim
title: SFT compactifications are one-defect SFTs; the Grigorchuk group has a non-metric seed from its branch structure (the tip of the Schreier ray of 1^∞ is locally detectable, so G/Stab(1^∞) has a compactification with an isolated dense orbit), but free orbits and finite type stay open, and the growth argument against Cannon seeds does not close
requires:
  - grigorchuk-envelope-emitter-reduces-to-ie-prime-for-grigorchuk
  - finite-type-branch-blow-ups-are-sft-compactifications
distinct_from:
  finite-type-branch-blow-ups-are-sft-compactifications: that seeds free orbits metrically (Cannon cones) for hyperbolic groups; this reformulates the seed condition as a one-defect condition, and gives a seed of branch type for the Grigorchuk group whose orbit is not free.
  grigorchuk-envelope-emitter-reduces-to-ie-prime-for-grigorchuk: that reduces the envelope's blow-up to (IE′) for G with free orbits; this supplies the branch-type seed for the parabolic homogeneous space G/Stab(1^∞), and states exactly what is still missing for free orbits.
---

**ESTABLISHED** for items 1 and 3 (lane proof, bh-e3prime, 2026-09-18; elementary; not reviewed).
Item 2 records why the requested growth obstruction was **not** obtained. Item 4 is **OPEN**.

## Statement

1. **One-defect lemma.** Let `S` be finitely generated, `X ⊆ A^S` a subshift, and `x ∈ X` isolated
   with `\overline{Sx} = X`, witnessed by a pattern `P` with `[P] ∩ X = {x}`. Then:
   - in every `y ∈ X`, the occurrences of `P` form the empty set or a single left coset of
     `L = Stab(x)`; for free `x`, `P` occurs at most once;
   - the configurations with an occurrence of `P` are exactly the orbit `Sx`;
   - the remainder `X ∖ Sx = X_P` is `X` with `P` forbidden. So if `X` is an SFT, so is the remainder.

   So an SFT compactification of `S` with a free orbit is a one-defect SFT: some pattern occurs
   at most once in every configuration, and the defect-free configurations form an SFT. Permanence: products of such SFTs are such SFTs, using the product pattern.
2. **Metric seeds: the growth argument does not close.**
   - The Cannon seed of `finite-type-branch-blow-ups-are-sft-compactifications` needs (TP). Since
     `C_q(g) = C_1(q^(-1) g)`, (TP) is equivalent to "cone types are determined by `k`-tails". So it
     implies finitely many cone types, and hence a regular geodesic language.
   - A regular language has rational growth, so the *geodesic* growth of `S` would be polynomial or
     exponential. That is compatible with intermediate *element* growth, because geodesic growth
     dominates element growth.
   - Passing from finitely many cone types to rational element growth needs unique geodesic
     representatives chosen by a finite-state rule (shortlex cone types, fellow travelling). This is
     not available for the Grigorchuk group, which is not automatic, since it is not finitely presented.
   - So "intermediate growth rules out Cannon seeds" is **not proved** here. Whether the Grigorchuk
     group has finitely many cone types for some generating set is not known to this lane.
3. **A branch-type seed (non-free orbit).** Let `G = ⟨a, b, c, d⟩` be the first Grigorchuk group,
   `ξ = 1^∞`, and `P = Stab_G(ξ)`. For `η ∈ ∂T_2`, let `λ(η) ⊆ {a, b, c, d}` be the set of generators
   fixing `η`, and put `x_η(g) = λ(g^(-1) η)`. Then `g·x_η = x_(gη)`. Let `Y` be the orbit closure of
   `x_ξ` in `(2^{a,b,c,d})^G`. Then:
   - `λ(η) = {b, c, d}` iff `η = ξ`;
   - `x_ξ` is isolated in `Y`, with dense orbit `G x_ξ ≅ G/P`;
   - `Stab(x_ξ) = P`, which is infinite. It contains the rigid stabilizers of the subtrees `1^k 0`.

   So the homogeneous space `G/P` (the Schreier ray of `1^∞`) has a `G`-compactification with an
   isolated dense orbit. It is pinned by a pattern read off from the branch structure, not from a
   metric.
4. **Open.** Two things are open.
   - Is `Y` a subshift of finite type over `G`? Along each Schreier line the labels form a
     substitutive (Lysionok) sequence, which is not of finite type as a Z-subshift (recalled:
     Vorobets; Grigorchuk–Lenz–Nagnibeda). But `G`-rules can
     use the relations of `G`, so this does not decide the question.
   - Free orbits: pinning the identity needs distinguishing elements of `P`. Each finite set of
     boundary points has infinite pointwise stabilizer in a branch group, so no finite family of tips
     pins `1`. A free seed would need a hierarchical, level-by-level, finite-alphabet code of all tips,
     using `St_G(1) ↪ G × G`.

## Proof

**Item 1.**
- If `P` occurs in `y ∈ X` at `h`, then `h^(-1) y ∈ [P] ∩ X = {x}`, so `y = h x`.
- The occurrences of `P` in `hx` are the `h'` with `h'^(-1) h x = x`, i.e. the coset `h·Stab(x)`.
- The remainder consists of the configurations with no occurrence of `P`, which is `X_P`.
- For products, `P × P'` occurs at most once, exactly on the product orbit, and that orbit is dense
  in `X × X'`.

**Item 3.**
- **Wreath recursion.** `ψ(b) = (a, c)`, `ψ(c) = (a, d)`, `ψ(d) = (1, b)`, and `a` swaps. At
  `1^k 0 y`, the sections of `b, c, d` at `1^k` are `b, c, d` permuted cyclically. Exactly one of them
  is `d`, whose 0-section is `1`; the others have 0-section `a`. So exactly one of `b, c, d` fixes
  `1^k 0 y`, while all three fix `ξ`, and `a` fixes nothing.
- **Isolation.** Let `z ∈ Y` have `z(1) = {b, c, d}`. Then `z = lim g_n x_ξ = lim x_(g_n ξ)`. The
  cylinder is clopen, so eventually `λ(g_n ξ) = {b, c, d}`, i.e. `g_n ξ = ξ`, and `z = x_ξ`.
- **Stabilizer.** `P` fixes `x_ξ`. If `g ∉ P`, then `x_(gξ)` has the tip label at `g`, while `x_ξ` has
  it only on `P`. So `Stab(x_ξ) = P`.
- `P` contains every element supported in a subtree `1^k 0 T`, and `G` is branch, so `P` is infinite.

## Consequences

- **The seed exists; the free seed and finite type are the gap.** For the Grigorchuk envelope
  (`grigorchuk-envelope-emitter-reduces-to-ie-prime-for-grigorchuk`), the branch set is free
  `G`-orbits. Item 3 does not reach it: it seeds `G/P`, not `G`.
- **A parabolic envelope.** An emitter whose branch set is `G/P`, for instance from a splitting over
  the parabolic subgroup `P`, would take item 3 as its natural blow-up. Then (IE′) would reduce to
  finite type of `Y`. The obstacle is that `P` is not known to be finitely generated, and the usual
  finitely presented splittings need finitely generated edge groups.
- **Where the seed comes from.** Metric seeds pin a point with distance functions (hyperbolic groups).
  Branch seeds pin the tip of a Schreier ray by its fixed-generator label, which is a local
  signature of the self-similar structure. Branch seeds naturally pin cosets of parabolic
  subgroups, not points.

## Lesson for general BH

**(IE′) is a one-defect problem, and branch structure pins tips, not points.** An SFT
compactification is a one-defect SFT: some pattern occurs at most once in every configuration, and
the remainder is automatically an SFT. The Grigorchuk group supplies such a pattern from its branch
structure: the tip of the Schreier ray of `1^∞` is the only point fixed by `b, c, d`.

But the pinned object is a coset of the infinite parabolic subgroup, because finitely many boundary
points never have trivial common stabilizer in a branch group. Free orbits would need a hierarchical
code of tips at all levels.

Metric seeds cannot be ruled out by growth alone: finitely many cone types constrain geodesic
growth, not element growth. The live branch question is whether the tip subshift `Y` is of finite
type over `G`, together with a finitely generated parabolic splitting to put `G/P` at an emitter.
