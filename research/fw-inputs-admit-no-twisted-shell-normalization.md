---
rg: 2
id: fw-inputs-admit-no-twisted-shell-normalization
kind: claim
title: For an input with property FW, no action on N with infinite supports is normalized by the shift up to an endomorphism twist, so window zero fails for every genuine shell action
distinct_from:
  one-ended-shell-inputs-admit-no-shift-normalizing-enumeration: that excludes shift normalization for the regular action of a one-ended input; this excludes it for every action with infinite supports of an FW input, with any endomorphism as twist.
  accessible-shell-inputs-admit-no-shift-normalizing-enumeration: that is the regular-action statement for accessible inputs, by an end Euler measure; this is the genuine-action statement for FW inputs, by transfixing one commensurated set.
  eventually-periodic-genuine-shell-actions-give-fp-envelopes: that shows a finite-order twist forces eventual periodicity, hence a virtually abelian input; this shows that, for FW inputs, a twist of any order forces every element to act with finite support.
  genuine-action-shell-envelopes-generalize-the-regular-shell: that sets up the genuine-action shell and its gates; this rules out the window-zero case of those gates for FW inputs.
  fw-inputs-admit-no-twisted-normalizing-genuine-shell-action: that is the parallel result of lane bh-kazhdan-inputs, for any power s^m with m > 0 and any map phi, and for m < 0 with automorphisms, and it subsumes items 1 and 2 here at m = 1; this one states the conclusion as finite supports for every element, proves it by following the single forward ray, and adds the subgroup form of item 3.
artifacts:
  - research/artifacts/gq-referee-a-fw-inputs-admit-no-twisted-shell-normalization.md
---

**ESTABLISHED** by `fw-inputs-admit-no-twisted-shell-normalization-proof` (lane proof,
elementary; gq-referee-a PASS, proof-gap lens,
`research/artifacts/gq-referee-a-fw-inputs-admit-no-twisted-shell-normalization.md`, 07944799c,
nits applied; no novelty claimed for the ingredients). Items 1 and 2 overlap
`fw-inputs-admit-no-twisted-normalizing-genuine-shell-action`, landed independently by lane
bh-kazhdan-inputs (2a1326804).

## Statement

Let `P` be a group with **property FW**: every commensurated subset of every `P`-set is
transfixed. Property (T) implies FW. Let `ρ : P -> Sym(N)` be an action and
`s : n ↦ n+1`. Work in `NearSym(N)`.

1. **Twisted normalization forces finite supports.** Let `φ : P -> P` be an endomorphism
   with `s^-1 ρ_g s = ρ_(φ(g))` in `NearSym(N)` for every `g ∈ P`. Then every `ρ_g` has
   finite support.
2. **Window zero.** Suppose every `ρ_g`, `g ≠ 1`, has infinite support, and `P ≠ 1`.
   - (a) `s^-1 ρ(P) s` is not contained in `ρ(P)`.
   - (b) `s ρ(P) s^-1 ≠ ρ(P)`.
3. **Subgroups.** The same holds for every FW subgroup `H <= P` in place of `P`. Item 1
   needs no infiniteness. In particular, when the twist `φ` of `P` restricts to an
   endomorphism of a nontrivial FW subgroup `H`, every `ρ_h`, `h ∈ H`, has finite
   support. If all nonidentity elements of `P` have infinite support, this is
   impossible.

## Consequences for the shell route

In the genuine-action shell of `genuine-action-shell-envelopes-generalize-the-regular-shell`,
the window-zero case of the finite-window gate asks for `s^-ε ρ(P) s^ε <= ρ(P)`.
- By item 2(a), this fails for `ε = 1` for every FW input and every action with infinite
  supports. By item 2(b), it fails for `ε = -1` whenever the inclusion is an equality.
- The twisted-normalization mechanism asked for on the bh-shell-universal board, with a
  twist of infinite order and `R_ρ = P *_φ`, is therefore impossible for FW inputs. The
  eventually periodic mechanism reaches only virtually abelian inputs
  (`eventually-periodic-genuine-shell-actions-give-fp-envelopes`).
- So an FW input needs a window `N >= 1`, or a proper inclusion
  `s ρ(P) s^-1 < ρ(P)`, for any genuine shell action. The second case is not treated
  here.
- This applies to every Kazhdan input, among them `St_N(R_L)` for `N >= 3` (Ershov,
  Jaikin-Zapirain and Kassabov, through `steinberg-finite-presentation-and-kazhdan-theorem`)
  and `SL_n(Z)` for `n >= 3`.
- `GL_n(Q)` itself lacks FW (`sl-n-q-lacks-property-fw`), so the theorem does not bind
  inputs that avoid FW. Item 3 still binds any input with an infinite FW subgroup that
  the twist preserves.

## Scope

Nothing is claimed for windows `N >= 1`, or for a proper inclusion with `ε = -1`. The
regular-action results for one-ended and accessible inputs are not re-proved here: they
concern the regular action, which may fail FW. The two proofs use different mechanisms.
