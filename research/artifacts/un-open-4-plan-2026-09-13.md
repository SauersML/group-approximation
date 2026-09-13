# un-open-4 plan: algebraic amenability as a groupoid-free source of rank models

Lane `un-open-4`, 2026-09-13. Open-ended lens: **beyond Steinberg algebras**.

## Target

Feed the UN root `kazhdan-elementary-approximation-type-mirrors-ring-type` from *general affine algebra
theory* rather than from groupoid dynamics, using Elek's algebraic amenability.

**T1 (main).** Let `k` be any field and `R` a simple unital affine `k`-algebra that is amenable in Elek's
sense (a Følner exhaustion by finite-dimensional subspaces). Then `R` has a **unital rank model** over `k`:
a unital embedding into a rank-metric ultraproduct `prod_omega M_(d_n)(k)`.

**T2 (source of amenability).** If `A` is a locally finite `k`-algebra and `Γ` is an amenable group acting
on `A`, then `A ⋊ Γ` is Elek-amenable. Hence every `LC(X,k) ⋊ Γ` with `Γ` amenable is amenable, for **every**
Cantor system `X`, with no minimality, entropy or tower hypothesis.

**T3 (corollary chain).** `Γ` amenable and `LC(X,k) ⋊ Γ` simple ⇒ rank model ⇒ (via the existing forward node
`rank-modelled-simple-rings-give-linear-sofic-projective-el`) the Kazhdan groups `EL_N` are linear sofic, and
over finite `k` weakly sofic.

## Why it matters

1. **It bypasses a Kaplansky-hard step.** `un-tarski` established
   `invariant-measure-gives-rank-function-in-char-zero` and left
   `invariant-measure-gives-rank-function-any-field` open, noting it contains Kaplansky stable finiteness in
   characteristic `p`. But the Kazhdan groups live *only* in characteristic `p`: EJZ needs `R` finitely
   generated as a ring, so `k` must be finite by Artin–Tate. T1+T2 give the rank model in **every**
   characteristic, because Følner subspaces are produced directly from amenability of `Γ` and local
   finiteness of `LC(X,k)`, never from a measure.
2. **It settles the char-`p` rank model for the `Z^d` family**, including Labbé's
   `LC(Ω_U, F_q) ⋊ Z^2`, the open row 7 of `un-calibration`. The node
   `rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group` names exactly this ring as its candidate and
   currently *assumes* the rank model; T2 supplies it unconditionally.
3. **It is groupoid-free.** T1 asks nothing about ample groupoids, type semigroups or invariant measures. It
   is a statement about affine algebras, so it extends the program past Steinberg algebras, which is this
   lane's lens.
4. **It locates a genuine break in the dichotomy.** Elek-amenability is *sufficient* for a rank model but is
   not the same condition as the measure side. Amenability is an algebra-level Følner property; the measure
   side is a groupoid property. Recording where they separate is part of the deliverable.

## Credit (not mine, verified verbatim before use)

- Elek, *The amenability of affine algebras*, arXiv:math/0203261: Definition of amenable affine algebra
  (Følner exhaustion), Proposition 4.1 (subexponential growth ⇒ amenable), Theorem 2 (Tarski alternative,
  **domains only**), Corollary (unique rank property).
- Elek, *On algebras that almost have finite dimensional representations*, arXiv:math/0311376: Definition of
  "almost has finite dimensional representations", Proposition (amenable ⇒ almost-fd; the compression
  construction), Theorem 2 (simple + almost-fd ⇒ stably finite), the rank radical `RR(A)`.

My contribution is the upgrade from Elek's *almost*-representations (which are not faithful, and are
inherited by any algebra surjecting onto the ring) to a **faithful** rank-metric embedding, using simplicity
to force the rank radical to vanish; plus T2 and the group-level consequences for the UN root.

## What this does NOT duplicate

- `un-converse` owns the converse rung `linear-sofic-el-groups-force-rank-model` and the forward node
  `rank-modelled-simple-rings-give-linear-sofic-projective-el`. I supply a new *source* of rank models and
  cite their forward node rather than reproving it.
- `un-tarski` owns the measure/paradox chain `algebraic-tarski-for-steinberg-algebras`. My route does not go
  through invariant measures and is not restricted to groupoid algebras.
- `un-measure` owns exact matricial models from residually finite actions (LEF). A rank model is strictly
  weaker than an exact matricial model; T2 applies where exact towers fail.
- `un-sofic-not-lef` hunts the measure side without towers using Ara–Claramunt continuous-factor techniques.
  Different mechanism; I will cite, not duplicate, and will message them if T2 lands their ring.
- `un-labbe-ring` owns the quantum-tiling question, i.e. whether the Labbé ring is *exactly* matricial. T2
  answers only the weaker rank-model question and leaves theirs untouched.

## Firewalls already known

- Elek's Tarski alternative (amenable ⟺ not paradoxical) is stated **only for algebras without zero
  divisors**. `LC(X,k) ⋊ Γ` has idempotents, so that equivalence must not be invoked here.
- Amenability is not necessary for a rank model, and exponential growth does not imply non-amenability
  (Elek: `k[Γ]` is amenable for every amenable `Γ`, including those of exponential growth). So T1 gives no
  converse and no dichotomy by itself.
- (F1) the matricial condition of `un-calibration` is over varying finite fields; a rank model over a fixed
  `k` is a different and weaker object. I state which is meant everywhere.
