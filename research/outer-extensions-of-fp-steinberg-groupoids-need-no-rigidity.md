---
rg: 2
id: outer-extensions-of-fp-steinberg-groupoids-need-no-rigidity
kind: claim
title: A finitely presented group acting by automorphisms on an ample groupoid with finitely presented Steinberg algebra gives a finitely presented, and under an outer-freeness condition central simple, crossed product with no rigidity hypothesis; but then the group's word problem is bounded by the algebra's, so no fixed groupoid hosts every decidable group
distinct_from:
  quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products: that gets a finitely presented crossed product over the trivial groupoid on X, where the diagonal LC(X) must be generated and made commutative by the group, which is quantum rigidity; this takes the diagonal from a groupoid whose algebra is already finitely presented, and the group costs nothing.
  no-fp-simple-algebra-hosts-every-decidable-algebra: that says no single fp simple algebra contains every decidable algebra; this is the group-of-automorphisms counterpart, with an explicit word-problem bound.
---

**ESTABLISHED** by the proof below (lane bh-invent-03, 2026-09-18; elementary lane proof, not reviewed; no priority
claimed).

## Setting

- `k` is a computable field.
- `ℋ` is a Hausdorff ample groupoid with compact unit space `X`, whose Steinberg algebra `A = A_k(ℋ)` is finitely
  presented. Examples are graph groupoids of finite graphs (Leavitt path algebras), finite higher-rank graphs
  (Kumjian–Pask algebras), and products of these.
- `Γ = ⟨S | R⟩` is a finitely presented group acting on `ℋ` by groupoid automorphisms `α_γ`.
- `ℋ ⋊ Γ` is the semidirect product groupoid, with arrows `(h, γ)`, `s(h, γ) = γ^{-1}(s(h))`, `r(h, γ) = r(h)`.
- **Outer topological freeness.** `Γ` acts *outer topologically freely* if no `γ ≠ 1` agrees, on a nonempty open
  subset of `X`, with the partial homeomorphism of a compact open bisection of `ℋ`.

## Statement

1. **No rigidity gate.** `A_k(ℋ ⋊ Γ) ≅ A ⋊_α Γ`, and this algebra is finitely presented.
2. **Central simplicity.** If `ℋ` is minimal and effective and `Γ` acts outer topologically freely, then `ℋ ⋊ Γ` is
   minimal and effective. So `A ⋊ Γ` is simple with centre `k`, and `γ ↦ u_γ` embeds `Γ`, hence every subgroup `G`
   of `Γ`, in its units.
   - With the K-gate and the Khanh import of `boone-higman-via-leavitt-units-of-rigid-topologically-free-sfts`
     (steps 4–6, applied to `B = A ⋊ Γ`), `G` then lies in a finitely presented simple group.
3. **Ceiling.** Suppose `Γ` is finitely generated, acts faithfully on `A`, and `A` has solvable word problem; the
   last holds, for example, if `A` is simple (`fp-simple-algebras-have-solvable-word-problem`).
   - Then `Γ` has solvable word problem, decidable on words of length `n` by one call to the word problem of `A`
     on inputs of length `≤ C^n`. Here `C` depends only on the images of the generators.
   - In particular, the subgroups `G` reachable in item 2 over a **fixed** `ℋ` all have word problem in one
     relativized exponential class. So no fixed `ℋ` hosts every decidable group.

## Proof

**1. The isomorphism and the presentation.**
- Compact open bisections of `ℋ ⋊ Γ` are the sets `B × {γ}`. Send `1_{B×γ}` to `1_B u_γ`. Then
  `(B×γ)(B'×γ') = B·α_γ(B') × γγ'` matches `1_B u_γ 1_{B'} u_{γ'} = 1_B 1_{α_γ(B')} u_{γγ'}`. So
  `A_k(ℋ ⋊ Γ) ≅ A ⋊_α Γ`, the skew group algebra.
- It is presented by:
  - the generators `a_1, …, a_p` and relators of `A`;
  - symbols `u_s`, `s ∈ S`, with `u_s u_{s^{-1}} = 1` and the relators `R`;
  - `u_s a_i u_s^{-1} = w_{s,i}`, where `w_{s,i}` is a fixed word representing `α_s(a_i)`.
- The pairs `(γ, a)` with `u_γ a u_γ^{-1} = α_γ(a)` form a set closed under sums and products in `a`, and under
  products in `γ`. So the finitely many relations above imply all of them.
- The presented algebra is therefore `A * k[Γ]` modulo the skew relations, which is `A ⋊ Γ`.

**2. Effectiveness and simplicity.**
- **Minimal.** `ℋ ⋊ Γ` is minimal because its orbits contain those of `ℋ`.
- **Effective.** An open bisection of `ℋ ⋊ Γ` lying in the isotropy has the form
  `{(h, γ) : h ∈ B, s(h) ∈ γ(O)}` with `T_B ∘ γ = id` on the open set `O`.
  - If `γ = 1`, then `B` lies in the isotropy of `ℋ`, so `B ⊆ X` since `ℋ` is effective.
  - If `γ ≠ 1`, then `γ = T_B^{-1}` on `O`, which outer topological freeness forbids.
  - So the interior of the isotropy is the unit space.
- **Simple with centre `k`.** Hausdorff minimal effective ample groupoids have simple Steinberg algebras, by the
  standard simplicity theorem (Brown–Clark–Farthing–Sims; Clark–Edie-Michell), recalled and not re-read.
  - The centre consists of class functions supported on the interior of the isotropy, so here of invariant
    functions in `LC(X, k)`. By minimality these are constants.
- **`Γ` embeds in the units.** The `u_γ` are linearly independent over `A`.

**3. Ceiling.**
- **The test.** `γ = s_1⋯s_n` is trivial iff `α_γ(a_i) = a_i` for every generator `a_i`. Compute `α_γ(a_i)` by
  substituting the words `w_{s,i}` `n` times. That gives words of length `≤ C^n`, with
  `C = max |w_{s,i}|`, which the word problem of `A` then compares with `a_i`.
- **Applies to the action on `ℋ`.** A faithful action on `ℋ` is faithful on `A`, because `A` contains `1_B` for every
  compact open bisection `B`.
- **So item 2 obeys the ceiling.** In item 2 the action on `X`, and so on `A`, is faithful: a `γ ≠ 1` acting
  trivially on `X` would agree with the unit bisection everywhere, contradicting outer topological freeness. ∎

## Lesson for general BH

Quantum rigidity (gate E2) is the price of generating and commuting the diagonal `LC(X)` with the input's own
group. A compressive groupoid with a finitely presented algebra pays that price once and for all: any finitely
presented group of outer automorphisms extends it for free (item 1).
- **Where the difficulty goes.** Item 3 shows the complexity must then sit in `ℋ` itself.
- **What the known cases show.** The compressive groupoids I know with a finitely presented algebra all have a
  word problem of bounded complexity. These are graph groupoids (Leavitt path algebras) and finite higher-rank
  graphs (Kumjian–Pask algebras); contracting Nekrashevych groupoids plausibly belong here too, not checked.
  Finite higher-rank graphs factorize uniquely, so every rectangle extends and their path languages carry no
  computation.
- **Conclusion.** "Rigidity" and "complexity" (the carrier principle) are **one gate**, not two. A universal host
  needs a groupoid that is both computationally universal and has a finitely presented Steinberg algebra. Splitting
  it into a rigid, cheap groupoid and a complex group of automorphisms cannot work. So:
  - **Constructions to stop.** Anything that puts the input in the acting group and takes rigidity from a fixed
    compressive factor. Folds, products with boundary shifts, and automorphic extensions all fall under this.
  - **Constructions to pursue.** Rigidity certificates for groupoids whose own language is complex. For example,
    SFTs over an fp overgroup that carries the complexity; by
    `steinberg-fp-is-a-kakutani-invariant`, these may be tested on any Kakutani model.
