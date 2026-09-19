---
rg: 2
id: faithful-heisenberg-actions-are-locally-free-at-every-scale
kind: claim
title: "Every faithful action of H_3(Z) on a set is locally free at every scale: for each R some point has no nontrivial stabilizer element in the word ball B(R)"
distinct_from:
  heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs: that bounds the centre's orbits under a growth hypothesis on a host graph; this is a purely group-theoretic statement about arbitrary faithful H_3-sets, with no geometry.
---

**Setting.** `H = H_3(Z) = ⟨a, b | [a,[a,b]], [b,[a,b]]⟩`, `c = [a,b]`,
`[x,y] = xyx^{-1}y^{-1}`. `B(R)` is the ball of radius `R` for the word length
`|·|_w` in `{a^{±1}, b^{±1}}`. `H` acts on a set `Ω` by a homomorphism
`ρ : H → Sym(Ω)`.

**Statement.** If `ρ` is injective, then for every `R ≥ 1` there is `p ∈ Ω`
with `Stab(p) ∩ B(R) = {1}`. Equivalently, `h ↦ ρ(h)p` is injective on
`B(R/2)`.

**Remarks.**
- Injectivity of `ρ` is equivalent to `ρ(c)` having infinite order. A
  nontrivial normal subgroup of a nilpotent group meets the centre `⟨c⟩`
  nontrivially.
- The point `p` depends on `R`. Stabilizers can be nontrivial at every point.
  Take `Ω = ⊔_{n≥1} H/K_n` with `K_n = ⟨a, c^n⟩`. It is faithful, since a
  normal subgroup inside `K_n` has its `a`-exponents divisible by `n`
  (conjugate by `b`). Yet `hah^{-1}` fixes `hK_n`.
- The statement fails for `Z^2 = ⟨x,y⟩` acting on `Z^2/⟨x⟩ ⊔ Z^2/⟨y⟩`.
  That action is faithful, but every point is fixed by `x` or by `y`. For
  `H`, the proof uses that conjugation shifts a non-central element along the
  centre by a nonzero linear form.

Route: `faithful-heisenberg-actions-are-locally-free-proof` (unreviewed).
