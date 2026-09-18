---
rg: 2
id: bs-conjugators-of-wandering-maps-have-invariant-compacta
kind: claim
title: If a homeomorphism a of a compact space acts properly and cocompactly on its wandering set, every b with b a b^-1 = a^k (|k| >= 2) has a nonempty compact invariant subset of that wandering set; so in Baumslag--Gersten actions a is never of finite Morse--Smale type
distinct_from:
  baumslag-gersten-equicontinuous-generator-acts-trivially: that kills equicontinuous images of the Baumslag--Gersten generator a; this kills the opposite regime, where a wanders off a finite non-wandering set with a compact fundamental domain (north--south and attractor--repeller maps).
  bg-in-isometric-brick-hosts-needs-unbounded-exponents: that constrains a inside groups of brick maps with isometric sections through exponent sums; this is a purely topological-dynamics statement about any compact metric space and any homeomorphisms.
  odometer-generators-carry-no-nonsolvable-baumslag-solitar: that is about odometer generators and non-solvable BS(m,n); this is about the solvable relation b a b^-1 = a^k with a wandering generator a.
---

**ESTABLISHED** by `bs-conjugator-invariant-compactum-proof` (lane proof, elementary;
not independently reviewed; no priority claimed).

## Setting

`X` is a compact metric space and `a, b ∈ Homeo(X)`. `Ω(a)` is the non-wandering set
and `W(a) = X \ Ω(a)` the (open) wandering set. Say `a` is **cocompactly wandering** if
`W(a) ≠ ∅` and `⟨a⟩` acts on `W(a)` properly (for compact `C ⊆ W(a)` only finitely many
`n` have `a^n C ∩ C ≠ ∅`) and cocompactly (some compact `D ⊆ W(a)` has
`W(a) = ⋃_n a^n D`).

Examples: north--south homeomorphisms of the Cantor set; loxodromic elements of a
uniform convergence action on a compactum without isolated points (off their two fixed
points); attractor--repeller elements of Thompson-type groups with no periodic clopen
part.

## Statement

1. **Invariant compactum.** If `a` is cocompactly wandering and `b a b^-1 = a^k` for some
   integer `k` with `|k| ≥ 2`, then `b` has a nonempty compact invariant set `K ⊆ W(a)`.
   In particular `b` has a minimal set inside the wandering set of `a`.
2. **Finite non-wandering sets.** If in addition `Ω(a)` is finite and `t a t^-1 = b` for
   some `t ∈ Homeo(X)`, then `W(a) = ∅`, i.e. `X = Ω(a)` is finite.
3. **Baumslag--Gersten-type groups.** Let `BG_k = ⟨a, t | b a b^-1 = a^k, b = t a t^-1⟩`
   (`k = 2` is the Baumslag--Gersten group). In any action of `BG_k` on a compact metric
   space by homeomorphisms in which `a` acts with infinite order, `a` is not cocompactly
   wandering with finite non-wandering set. So a host of `BG` whose infinite-order
   elements are all of finite Morse--Smale type (finite `Ω`, cocompactly wandering) does
   not exist; any host must give `a` an infinite non-wandering set or a wandering set
   without compact fundamental domain.

## Scope

- Part 1 needs no hypothesis on `Ω(a^k)`: `b(Ω(a)) = Ω(a^k) ⊆ Ω(a)` gives
  `b^-1(W(a)) ⊆ W(a)` automatically.
- Part 2 uses finiteness only to compare `|Ω(b)|` with `|Ω(a)|`. For infinite `Ω(a)`
  (e.g. an element of `V` with a periodic clopen part) Part 1 still holds but gives no
  contradiction, so this does not exclude `V`, `nV` or the landed `2V_τ` hosts; `V` is
  excluded for other reasons (undistorted cyclic subgroups).
- Nothing here bears on Higman's group `H4` directly: there the conjugator `a_(i+1)` of
  `a_i` is not required to be conjugate to `a_i`.
