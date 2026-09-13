---
rg: 2
id: outer-actions-on-o2-kk-g-contractible-iff-rokhlin
kind: claim
title: An outer finite group action on O_2 is KK^G-contractible iff it has the Rokhlin property, so detection at p is Rokhlin rigidity for O_2-actions with contractible crossed product
distinct_from:
  izumi-rokhlin-approximately-representable-duality: that imports the duality between the Rokhlin property and approximate representability; this proves that on O_2 the Rokhlin property is exactly KK^G-contractibility for outer actions.
  gardella-rokhlin-actions-preserve-uct: that is permanence of the UCT along Rokhlin actions; this identifies Rokhlin actions on O_2 with the zero object of KK^G.
  zp-detection-iff-bootstrap-sufficiency-and-kk-g-generation: that gives triangulated, bootstrap and stable-dynamical forms of detection; this gives the unital dynamical form, the Rokhlin property.
  zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner: that characterizes KK^G-triviality of the generator by invariant asymptotic innerness; this characterizes KK^G-contractibility of the whole action by the Rokhlin property.
---

**ESTABLISHED (derivation from Hirshberg--Winter, Szabó and Gabe--Szabó;
standard inputs flagged in the proof).**  Let `G` be a finite group.

1. **Rokhlin actions are contractible.**  Let `A` be a separable unital
   C\*-algebra with `A ≅ A ⊗ O_2`, and `α : G ↷ A` an action with the
   Rokhlin property.  Then `α` is cocycle conjugate to `α ⊗ id_(O_2)`, and
   `(A, α)` is KK^G-contractible.
2. **On `O_2` the converse holds.**  For a pointwise outer action
   `α : G ↷ O_2` the following are equivalent:
   - `(O_2, α) ≃_(KK^G) 0`;
   - `α` has the Rokhlin property;
   - `α` is conjugate to the model `id ⊗ μ_G` on `O_2 ⊗ M_(|G|^∞) ≅ O_2`, where
     `μ_G = ⊗_n Ad(λ_G)` is the infinite tensor power of the regular
     representation.
3. **Unital form of detection.**  Every nuclear `G`-algebra `D` with
   `Res D ≃_KK 0` is KK^G-equivalent to a pointwise outer action on unital
   `O_2`, whose crossed product is KK-equivalent to `D ⋊ G`.  So for
   `G = Z/p`, `zp-restriction-and-crossed-product-detect-kk-g-contractibility`
   is equivalent to **Rokhlin rigidity**: every pointwise outer
   `α : Z/p ↷ O_2` with `O_2 ⋊_α Z/p ≃_KK 0` has the Rokhlin property.
4. **The dual Rokhlin case.**  Let `G = Z/p` and let `α : G ↷ O_2` be outer
   with `O_2 ⋊_α G ≃_KK 0`.  If `α` is approximately representable, that is,
   `α̂` has the Rokhlin property, then `α` is KK^G-contractible, so by item 2
   `α` has the Rokhlin property.  With Izumi's Theorem 4.6 (as cited in
   `izumi-rokhlin-approximately-representable-duality`, item 3), detection
   holds for every outer strongly approximately inner `Z/p`-action on `O_2`.
   With item 3 this gives the converse of
   `outer-zp-actions-on-o2-strongly-approx-inner-via-detection`: if every outer
   `Z/p`-action on `O_2` is strongly approximately inner, detection holds at
   `p` (route `zp-detection-from-strong-approximate-innerness`).  So detection
   at `p` is equivalent to the open question of Barlak--Li II,
   Remark 4.14(2), for outer actions of order `p`.
5. **Finite Rokhlin dimension with commuting towers.**  Item 1 holds more
   generally.  Let `A` be separable, not necessarily unital, with
   `A ≅ A ⊗ O_2`, and let `α : G ↷ A` have finite Rokhlin dimension with
   commuting towers.  Then `α` is strongly cocycle conjugate to
   `α ⊗ id_(O_2)`, so it is KK^G-contractible.  So a pointwise outer action
   on `O_2` with finite commuting-tower Rokhlin dimension has the Rokhlin
   property, by item 2.  A phantom candidate in item 3 therefore has infinite
   commuting-tower Rokhlin dimension, and so does its dual when the dual is
   outer.  For `A = O_2` the conclusion was published earlier as Proposition 3.32 of
   Gardella--Hirshberg--Santiago, arXiv:1709.00222
   (`ghs-z2-commuting-rokhlin-dimension-one-dual-sai`).

This replaces the unverified Rokhlin sketch in the Attempts of the detection
claim.  That sketch invoked Izumi's uniqueness theorem.  The argument here
uses no uniqueness theorem for Rokhlin actions and no UCT.

**Model tests.**
* The trivial action on `O_2` is KK^G-contractible, since `τ` is a functor and
  `O_2 ≃_KK 0`.  It is not Rokhlin.  So outerness in item 2 cannot be dropped.
* The model `id ⊗ μ_G` is Rokhlin, pointwise outer and contractible.
* Illustration, inputs not re-read; nothing depends on it.  The quasi-free
  action `S_1 ↦ S_1`, `S_2 ↦ −S_2` of `Z/2` on `O_2` has KK^G-class the cone
  of `1 − [1 ⊕ χ] = −χ ∈ R(Z/2)`, by Pimsner's equivariant Toeplitz sequence.
  That element is a unit, so the action is contractible.  It is outer, so by
  item 2 it is conjugate to the Rokhlin model.

**What this changes for the phantom side.**  By item 3, a counterexample to
detection is exactly a pointwise outer `Z/p`-action on `O_2` whose crossed
product is `O_2` but which is not Rokhlin.  Failure of the Rokhlin property is
a dynamical, central-sequence property.  So such a witness can be certified
without any K-theoretic signature, which by
`bootstrap-zp-actions-realize-every-cyclotomic-k-module` cannot exist.  It
must lie outside `B^G`, because every bootstrap-class action with contractible
restriction and crossed product has zero Köhler invariant, hence is
contractible.

No priority is claimed.  Item 1 is close to folklore after Hirshberg--Winter
and Szabó.  Item 2 is a direct application of Gabe--Szabó's classification.
Its explicit statement was not found in the parts of those papers that were
read.

Proof: `outer-actions-on-o2-kk-g-contractible-iff-rokhlin-proof`.
