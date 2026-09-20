---
rg: 2
id: padded-abstract-rn-perfect-decidable-nonrecursive-kernel
kind: claim
root: true
title: A direct padded abstract RN construction gives one perfect decidable finitely presented relatively simple group with a nonrecursive clopen-action kernel and a non-recursively-presentable simple quotient
distinct_from:
  some-a2-action-has-a-nonrecursive-kernel: that asserts only existence of an action with a nonrecursive kernel; this requires the same ambient group to be perfect, decidable, relatively simple, and a finite-index derived subgroup of a padded abstract RN group.
  fp-relatively-simple-pair-with-unsolvable-simple-quotient: that supplies a relatively simple witness using an additional abstract twisted Brin--Thompson construction; this demands a direct RN witness with decidable word problem and the stronger non-recursive-presentability obstruction.
  abstract-rover-nekrashevych-groups-are-finitely-presented: that proves the abstract table presentation for arbitrary finite recursion data; this combines padding, finite abelianization, direct relative simplicity and exact computability conclusions for one hard recursion.
artifacts:
  - research/artifacts/padded-abstract-rn-manuscript-integration-2026-09-20.md
---

## Statement

There exist a finite-rank free group `F`, a finite recursion over `F` with
nonrecursive tree kernel `N`, and padding `ψ_k` on an even alphabet of size
`D≥4`, such that, for `P=V_D(F,ψ_k)`, `E=P′`, and the boundary-action kernel
`M=ker(E→Homeo(C_D))`, all of the following hold simultaneously:

1. `P` is finitely presented with decidable word problem and finite
   abelianization. `E` is finite-index, finitely presented, decidable and
   perfect, and contains the faithful infinite finitely presented simple
   prefix subgroup `V_D`.
2. `M` is proper and contains every proper normal subgroup of `E`. Thus
   `E/M` is the unique nontrivial simple quotient of `E`; it is infinite,
   nonabelian, and contains `V_D`. Every nonidentity element of that prefix
   subgroup normally generates `E`.
3. `M≡_T N`; `M` is co-c.e., nonrecursive and not c.e. The finitely generated
   simple quotient `E/M` is not recursively presentable. `M` is not finitely
   normally generated, and `E` has no nontrivial recursively presented
   simple quotient.
4. The action on the proper nonempty clopen subsets of `C_D` is of type
   `[A₂]`, with kernel `M`: the group is finitely presented, point stabilizers
   are finitely generated, and there are finitely many orbits on ordered pairs.
5. There is no injective `j:E→H` with `H` finitely presented and `L◁H`
   finitely normally generated satisfying `j(E)∩L=j(M)`. This conclusion
   does not require relative simplicity of `(H,L)`.

## Submission status and dependencies

This is the strengthened claim of the **first user-supplied manuscript**,
integrated on 2026-09-20. The linked artifact is an edited reconstruction of
Sections 4–10, not a verbatim archival copy or a review certificate. The
new conditional synthesis route requires the unresolved structural theorem
`padded-abstract-rn-local-derived-normal-subgroup-theorem`, the existing
abstract RN finite-presentation theorem, and the explicitly repaired
Bartholdi–Mitrofanov input. It is not an unconditional proof submission and
is not Lean verified. No priority or novelty determination is asserted.

The new projection routes feed the older action-kernel and relative-simplicity
claims; their pre-existing derivations do not prove all the stronger
simultaneous properties required here. Full Boone–Higman remains a separate
problem.

## Attempts

The supplied proof pads the recursion with fixed letters carrying the entire
state, makes the abelianization finite by the nonsingular matrix
`(k−1)I+A`, then takes the derived subgroup. The proposed local-support double
commutator argument makes that subgroup relatively simple and perfect. Its
formal support calculus, local-derived generation and clopen stabilizer
generation are recorded in full in Sections 7 and 9 of the artifact and
await proof review in the explicit structural prerequisite. The reduction
`f↦[ι₁(f),v]` is a computable word reduction, not a homomorphism.
