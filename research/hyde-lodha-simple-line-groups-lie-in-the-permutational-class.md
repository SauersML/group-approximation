---
rg: 2
id: hyde-lodha-simple-line-groups-lie-in-the-permutational-class
kind: claim
title: The Hyde–Lodha finitely presented simple left-orderable groups Q_n are subgroups of Stein's circle groups T(1; Z[1/n(n+1)], ⟨n, n+1⟩), so they and all their subgroups lie in B_A
distinct_from:
  circle-pl-groups-act-with-type-a-on-breakpoint-orbits: that proves the type (A) action of Stein's circle groups; this identifies the Hyde–Lodha groups as subgroups of one of them.
  lodha-simple-circle-group-has-a-type-a-action: that is Lodha's circle group S, which contains torsion; this is the torsion-free, left-orderable family Q_n of Hyde–Lodha acting on the line.
requires:
  - circle-pl-groups-act-with-type-a-on-breakpoint-orbits
  - bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh
  - boone-higman-type-a-class-closed-under-finite-extensions
---

**ESTABLISHED** (lane proof, bh-major-product, 2026-09-18; elementary; not independently
reviewed; no priority claimed). It is conditional on Stein's finiteness theorem, which
`circle-pl-groups-act-with-type-a-on-breakpoint-orbits` cites without reading it.

**Source.** J. Hyde and Y. Lodha, *Finitely presented simple left-orderable groups in the
landscape of Richard Thompson's groups*, arXiv:2302.04805v3. The HTML rendering was read on
2026-09-18 through a text extraction, not from the TeX. The referee should re-read
Definition 1.2 at source. Quoted there, in the paper's right-action notation `x·f`:
- Definition 1.2: `Γ_n ≤ Homeo^+(R)` consists of the `f` such that
  1. "f is piecewise linear with breakpoints in ℤ[1/n(n+1)], and ℤ[1/n(n+1)]·f=ℤ[1/n(n+1)]";
  2. "f commutes with the translation t↦t+1";
  3. for `x ∉ ℤ[1/n(n+1)]`, "x·f′=n^i(n+1)^j", with `i − j` fixed by the number of integers
     that `f` moves `x` across.
- Theorem 1.3: "For each n≥2, the group Qn=[Γn,Γn] is a finitely presented (and type F∞)
  simple group of orientation-preserving homeomorphisms of ℝ."
- Proposition 1.4: "Γn,Qn embed in the group of piecewise linear orientation-preserving
  homeomorphisms of 𝐒¹=ℝ/ℤ."

## Statement

Let `n >= 2`, `A = Z[1/(n(n+1))]`, `P = ⟨n, n+1⟩ ≤ R_(>0)`, and let `T(1; A, P)` be the circle
group of `circle-pl-groups-act-with-type-a-on-breakpoint-orbits`. Then:
1. `Q_n` embeds in `T(1; A, P)`.
2. `T(1; A, P)` acts 2-transitively and with type (A) on `A/Z`. So `Q_n` and all its subgroups
   lie in `B_A`, and embed in finitely presented simple groups.
3. BFFHZ Question 3.4 holds for `Q_n`, by `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`.
   So do (JE) with every `B_A` group and (SQ), since `B_A` is closed under finite direct
   products.

## Proof

**Item 1.**
- Every `f ∈ Γ_n` commutes with `t ↦ t + 1`, so it induces `f̄ ∈ Homeo^+(R/Z)`, and `f ↦ f̄` is a
  homomorphism.
- Its kernel consists of lifts of the identity that commute with `t ↦ t + 1`, which are the
  integer translations. These commute with every element of `Γ_n`, so the kernel is central.
- `Q_n` is infinite and simple, so its centre is trivial and the map is injective on `Q_n`.
  Proposition 1.4 states this embedding too.
- `f̄` is piecewise linear with finitely many breakpoints on the compact circle, all in `A/Z`
  by condition 1. It maps `A/Z` onto `A/Z` by condition 1.
- Its slopes lie in `P` by condition 3. The breakpoints form a discrete set, so the slope on a
  piece is the derivative at any of the non-`A` points of that piece.
- So `f̄ ∈ T(1; A, P)`.

**Item 2.** This is instance 2 (Stein's groups) of `circle-pl-groups-act-with-type-a-on-breakpoint-orbits`,
with `n_1 = n`, `n_2 = n + 1`, so `A = Z[1/(n_1 n_2)]`. Then
`d = gcd(n_1 − 1, n_2 − 1) = gcd(n − 1, n) = 1`, so the action is 2-transitive. `B_A` is closed
under subgroups. ∎

## Lesson for general BH

Even the torsion-free, left-orderable finitely presented simple groups, the family built to
avoid Thompson's torsion, sit inside a Thompson-type actor with a 2-transitive breakpoint
action. The line action of `Q_n` has infinitely many pair orbits, because commuting with
`t ↦ t + 1` preserves the number of integer translates of one point that lie below the other. That invariant disappears once we pass
to the circle, where the Bieri–Strebel invariant `A/(IP·A)` is trivial.

Lesson: for any group of piecewise-defined maps, choose the compact model on which the
breakpoint set is a single orbit with trivial Bieri–Strebel invariant. That model is the
type (A) certificate.
