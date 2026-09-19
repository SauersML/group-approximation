---
rg: 2
id: leavitt-st20-t-free-holes-hold-via-kazhdan
kind: claim
title: The literal character, Haar-row and atomic-return holes of the Kazhdan-free Leavitt goal are theorems via property T
distinct_from:
  property-t-free-leavitt-full-mf-radical: that is the goal, which forbids property (T); this proves its literal equation and the literal statements of three of its holes by a proof tree that uses (T), so it settles no Kazhdan-free question and must not be routed into the goal or into those holes.
  binary-leavitt-steinberg-mf-characters-are-trivial: that is the open Kazhdan-free character-rigidity hole; this proves the same displayed sentence through (T), and records that its note on simplicity and the Steinberg kernel is obsolete.
  binary-leavitt-haar-row-profile-is-not-mf-character-restriction: that is the open Kazhdan-free Haar-row exclusion; this proves the same displayed sentence through (T).
  binary-leavitt-atomic-morita-return: that is the open Kazhdan-free decoder; this shows its literal statement holds vacuously in the accurate regime once full radical is known through (T).
  binary-leavitt-all-ranks-full-mf-radical: that proves full radical for R^x and every GL_n(R); this transports it to the Steinberg group St_20(R) and reads off the consequences for the frontier holes of the goal.
  leavitt-corner-host-is-the-simple-leavitt-unit-group: that identifies St_20(R) with the simple unit group and relates corner certificates to hyperlinearity; this uses the same identification only to import full MF radical and derive trivial MF characters, a presentation modulus, and hole vacuity.
  mf-root-transport-is-vacuous-on-leavitt-units: that records vacuity of MF root transport on R^x itself; this records vacuity and (T)-derivability of the St_20 hole statements of the Kazhdan-free goal.
  full-mf-radical-uniform-asymptotic-collapse: that is the general equivalence for countable groups in multiplicative-defect form; this is the specific St_20(R) instance in presentation-model form, with the frontier consequences.
artifacts:
  - research/leavitt-st20-t-free-holes-hold-via-kazhdan-proof.md
---

**ESTABLISHED.**  Let

```text
R=L_(F_2)(1,2),       Delta=St_20(R),       z=x_13(s_1t_1).
```

1. **Identification.**  The Steinberg map is an isomorphism
   `Delta ~= GL_20(R) = EL_20(R) ~= R^x`.  In particular `Delta` is simple
   and its Steinberg kernel is trivial.
2. **Full radical.**  `Rad_MF(Delta)=Delta`.  Every MF character of `Delta`
   (pointwise limit of normalized traces of operator-norm asymptotic unitary
   representations) is the trivial character `1`.
3. **Presentation modulus.**  For any presentation `<S | Rel>` of `Delta` with
   `S` finite and any fixed word `w_g` for each `g` in a finite set `F`, and
   every `epsilon>0`, there is `delta_0(epsilon)>0` such that every
   assignment `U` of unitaries in any `M_d(C)` to `S` with
   `sup_(r in Rel) ||r(U)-1||_op <= delta_0` satisfies
   `max_(g in F) ||w_g(U)-1||_op <= epsilon`.
4. **Consequences for the literal hole statements.**
   - The displayed sentence of `binary-leavitt-steinberg-mf-characters-are-trivial`
     is true.
   - The displayed sentence `(HRP1)` of
     `binary-leavitt-haar-row-profile-is-not-mf-character-restriction` is true:
     every MF character takes the value `1` on every root element.
   - The displayed sentence `(BLAMR)` of `binary-leavitt-atomic-morita-return`
     is true: in its "sufficiently accurate" regime `delta<delta_0(1/2)` the
     rounded mark is the identity, `p_U=0`, and the implication is vacuous;
     `eta(delta)=0` there and `eta(delta)=1` otherwise (take all four
     operators zero).

The proof tree passes through `elementary-group-property-t-over-free-algebras`,
so none of these consequences is a Kazhdan-free result.  The route
`property-t-free-leavitt-via-mf-character-triviality`, whose other two
prerequisites are established, would flip the flagship goal if the first
item of part 4 were linked to its hole.  That hole, like the other two, is
therefore ill-typed as written: its displayed sentence omits the "without
property (T)" clause that the goal imposes on the proof, so it is a theorem
while the methodological question it was meant to encode is still open.
Each should be restated with an explicit proof-method restriction, or
replaced by a statement that is not a consequence of full radical; see the
proof route for the classification.
