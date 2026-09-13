---
rg: 2
id: z2-odd-commutator-below-half-forces-commuting-towers
kind: claim
title: For a Z/2-action, dimension-one Rokhlin towers whose odd parts commute up to less than 1/2 already give commuting towers, a central odd unitary and strong approximate innerness of the dual; on O_2 the Barlak–Li question is this commutator bound for the dual action
distinct_from:
  bemsw-outer-z2-kirchberg-rokhlin-dimension-at-most-one: that imports that outer Z_2-actions on unital Kirchberg algebras have Rokhlin dimension at most 1 without commuting towers; this proves that a single commutator bound on the odd parts of such towers upgrades them to commuting towers.
  ghs-z2-commuting-rokhlin-dimension-one-dual-sai: that imports the characterization of commuting-tower dimension one by the circle and its consequence for the dual action; this adds the converse, the open 1/2-threshold for non-commuting towers, and the O_2 consequences.
  z2-o2-actions-anti-inner-and-o3-rokhlin-criterion: that proves 2[1] = 0 is equivalent to strong approximate innerness of the dual and, with contractible crossed product, to the Rokhlin property; this proves 2[1] = 0 forces the Rokhlin property for every outer Z/2-action on O_2, with no hypothesis on the crossed product.
---

**ESTABLISHED (derivation from Gardella–Hirshberg–Santiago and
Barlak–Enders–Matui–Szabó–Winter; unreviewed).**  Let `β : Z/2 ↷ D` act on a
separable unital C\*-algebra, `F = D_∞ ∩ D'` with the induced involution `β`,
and `β̂` the dual action on `D ⋊_β Z/2`.  A *tower system* in `F` is four
positive contractions `f_0, f_1, g_0, g_1 ∈ F` with
`β(f_0) = f_1`, `β(g_0) = g_1`, `f_0 f_1 = 0 = g_0 g_1` and
`f_0 + f_1 + g_0 + g_1 = 1`.  Its *odd parts* are `a = f_0 − f_1` and
`b = g_0 − g_1`.  Towers witnessing `dim_Rok(β) ≤ 1` along `ε_n → 0` give a tower
system in `F`, and `‖[a, b]‖` is the limsup of the commutators along the sequence.

1. **Threshold.**  If a tower system has `‖[a, b]‖ < 1/2`, then `x = a + ib` is
   invertible and `c = x|x|^(−1)` is a unitary in `F` with `β(c) = −c`.
2. **Duality.**  The following are equivalent:
   - `dim_Rok^c(β) ≤ 1` (commuting towers);
   - `F` contains a unitary `c` with `β(c) = −c`;
   - `F` contains a tower system with `[a, b] = 0`;
   - `F` contains a tower system with `‖[a, b]‖ < 1/2`;
   - `β̂` is strongly approximately inner.

   So at dimension one, commuting towers are an *open* condition on the odd
   parts of arbitrary towers.
3. **On `O_2`.**  Let `α : Z/2 ↷ O_2` be pointwise outer and
   `B = O_2 ⋊_α Z/2`.
   - (a) `α` is strongly approximately inner iff `dim_Rok^c(α̂) ≤ 1`, iff `F_∞(B)`
     contains a tower system for `α̂` with `‖[a, b]‖ < 1/2`.  Tower systems for `α̂`
     always exist (`bemsw-outer-z2-kirchberg-rokhlin-dimension-at-most-one`, since
     `B` is a unital Kirchberg algebra and `α̂` is outer).
   - (b) If `α̂` is strongly approximately inner, then `α` has the Rokhlin
     property, and so `O_2 ⋊_α Z/2 ≅ O_2`.  Equivalently, `2[1] = 0` in
     `K_0(F_∞(O_2)^α)` implies `[1] = 0` for every outer `α`, whatever its crossed
     product.
   - (c) Barlak–Li II, Remark 4.14(2), for outer actions, is equivalent to:
     for every outer `α`, some tower system for `α̂` has odd parts commuting up to
     less than `1/2`.
   - (d) With `O_2 ⋊_α Z/2 ≃_KK 0`, the dual is again an outer action on `O_2`, and
     detection at `2` for `α` is equivalent to the same bound for tower systems of
     `α` itself.

**Reading.**  `bemsw-outer-z2-kirchberg-rokhlin-dimension-at-most-one` gives
towers for every outer action and every dual.  The whole open question at
`p = 2` is one number: the infimum of `‖[a, b]‖` over tower systems.  It is either
`< 1/2`, and then it is `0`, or it is `≥ 1/2`.  The towers of
Barlak–Enders–Matui–Szabó–Winter come from one quasi-free copy of `O_∞`; the
question is whether some other tower system does better.

**Model tests.**
- *Irrational rotation* `A_θ`, `α(u) = −u`, `α(v) = v`
  (Hirshberg–Phillips, arXiv:1410.6581, Example 1.12): the odd central unitaries
  `u^(n_k)` give tower systems with `[a, b] = 0`, so `dim_Rok^c(α) ≤ 1`.  Here `D`
  does not absorb `M_(2^∞)`, and `α` is not Rokhlin.
- *Inner symmetry* `σ = Ad(s)` with `s = s*` a unitary in `O_2` (not outer): `β`
  is trivial on `F`, so `F` has no tower system (`f_1 = f_0 ⊥ f_0` forces
  `f_0 = 0`), and no odd unitary.  Items 1–2 hold vacuously; item 3 needs
  outerness.
- *Quasi-free action on `O_∞`.*  It has Rokhlin dimension `1`
  (Barlak–Enders–Matui–Szabó–Winter, Corollary 2.2) and no finite commuting-tower
  dimension (Hirshberg–Phillips, arXiv:1410.6581, abstract).  So every tower
  system for it has `‖[a, b]‖ ≥ 1/2`, consistent with item 2.
- *Threshold is not formal.*  Any tower system has `a² + b² ≥ 1/2`, with equality
  exactly where `|a| = |b| = 1/2`.  An odd isometry `s` with `ss* ≠ 1` has
  invertible `s*s` but not `ss*`, and is not of the form `a + ib` from towers.

No priority is claimed for the circle characterization of `dim_Rok^c ≤ 1` or for
the implication to strong approximate innerness of the dual: both are in
Gardella–Hirshberg–Santiago (Corollary 3.27 and the proof of Theorem 3.34).
The 1/2-threshold (item 1), the converse in item 2, and items 3(b)–(d) were not
found there or in the predecessor nodes.  This was a bounded check of those
sources only.

Proof: `z2-odd-commutator-below-half-forces-commuting-towers-proof`.
