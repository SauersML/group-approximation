---
rg: 2
id: piecewise-representative-boundary-hosts-are-fp-type-a
kind: claim
title: For a piecewise-representative action h of a finite-index subgroup of Out(F_n) on ∂F_n, the derived full group of the germ groupoid of ⟨[[F_n ⋉ ∂F_n]], h⟩ is finitely presented and lies in the permutational class B_A
distinct_from:
  out-free-acts-on-boundary-by-piecewise-representatives: that is the existence of the action; this is the finiteness of the host it produces.
  matui-purely-infinite-minimal-full-groups-have-simple-d: that gives simplicity of the derived full group for purely infinite minimal groupoids; this asks for finite presentation and a type (A) action for the particular groupoid built from h.
---

**OPEN** (stated by bh-outfn-2, 2026-09-18).

**Notation.**
- `h` is a (PR) action of a finite-index `Γ ≤ Out(F_n)` on `∂F_n`, as in
  `out-free-acts-on-boundary-by-piecewise-representatives`.
- `M = [[F_n ⋉ ∂F_n]]` and `H_h = ⟨M, h(Γ)⟩ = M ⋊ h(Γ)`. It is finitely presented, being
  fp-by-fp.
- `𝒢_h` is the groupoid of germs of `H_h`, and `D_h := D([[𝒢_h]])`.

**Claim.** `D_h` is finitely presented, and `D_h ∈ B_A`. For instance, its action on one
`𝒢_h`-orbit could have finitely many orbits on pairs and finitely generated stabilizers.

## What is known

- **Structure.** `𝒢_h` is ample, Hausdorff, effective, minimal and purely infinite. So `D_h`
  is simple (route `out-fn-bh-via-piecewise-representative-boundary-host`, step 2).
- **Calibration.** For `Γ = 1` this is Matui's theorem: `[[F_n ⋉ ∂F_n]]` is of type F_∞.
  Its action on an orbit is the Higman–Thompson-type action.
- **What is new.** The germs of `h(Γ)` are germs of automorphisms. Restricted to a cylinder
  and rescaled, they are again boundary maps of automorphisms, not smaller ones. So the
  groupoid is self-similar with non-contracting sections, as in twisted Brin–Thompson
  groups, not as in contracting Röver–Nekrashevych groups.
- **Suggested method.** A Stein–Farley complex of cylinder partitions, with `Γ` as a
  coefficient group acting on labels. Finite presentation should then reduce to finite
  presentation of `Γ` together with finitely many piece-relations, as in Zaremsky's
  criterion for twisted Brin–Thompson groups. Not attempted.
