---
rg: 2
id: zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner
kind: claim
title: An outer Z/p-action on O_2 has KK^G-trivial generator iff the generator is asymptotically inner by invariant unitaries; detection makes every outer Z/p-action on O_2 strongly approximately inner
distinct_from:
  zp-restriction-trivial-splits-cellular-plus-phantom: that proves detection is equivalent to triviality of the action element in KK^G; this translates that triviality into dynamics on O_2 through Gabe--Szabó uniqueness.
  izumi-rokhlin-approximately-representable-duality: that imports Izumi's duality and the step from strongly approximately inner to approximately representable; this supplies strong approximate innerness itself, from KK^G-triviality.
---

**ESTABLISHED (derivation from cited theorems).** Let `p` be prime,
`G = Z/p = ⟨ω⟩`, and `α : G ↷ O_2` pointwise outer. Write
`θ = [α_ω] ∈ KK^G((O_2, α), (O_2, α))`.

1. **Criterion.** `θ = 1` iff there is a norm-continuous unitary path `u_t` in
   `O_2` with `α_ω = lim_t Ad(u_t)` pointwise and
   `‖α_g(u_t) − u_t‖ → 0` for all `g`. In that case the path can be replaced,
   for large `t`, by a continuous path of unitaries in the fixed-point algebra
   `O_2^α`. So `α` is strongly approximately inner in Izumi's sense.
2. **Bootstrap actions.** If `(O_2, α) ∈ B^G`, then `θ = 1`. So `α` is
   strongly approximately inner, hence approximately representable, and `α̂`
   has the Rokhlin property.
3. **Under detection.** If
   `zp-restriction-and-crossed-product-detect-kk-g-contractibility` holds at
   `p`, then every outer `Z/p`-action on `O_2` is strongly approximately inner.
   Each is then approximately representable, with Rokhlin dual action.
4. **Converse.** Suppose every outer `Z/p`-action on `O_2` satisfies the
   criterion of item 1. Then detection holds at `p` for nuclear algebras. So
   `Det(nuclear)` at `p` is equivalent to: every outer `Z/p`-action on `O_2`
   is asymptotically inner by asymptotically invariant unitary paths.
5. **Phantom shape.** An outer `Z/p`-action on `O_2` that is not strongly
   approximately inner has `θ ≠ 1`. Then its summand `(1 − e)(O_2, α)` is a
   nonzero equivariant phantom, and the Meyer–Nadareishvili converse fails at
   `p`. Barlak–Li II, Remark 4.14(2), says it is not known whether all
   `Z_2`-actions on `O_2` are strongly approximately inner.

**Reading.** For outer actions on `O_2`, the known open question about strong
approximate innerness sits exactly one step below the phantom problem:
- a non-strongly-approximately-inner outer action is a phantom certificate;
- the asymptotic, invariant-path version of strong approximate innerness is
  equivalent to detection.

Proof: `zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner-proof`.
