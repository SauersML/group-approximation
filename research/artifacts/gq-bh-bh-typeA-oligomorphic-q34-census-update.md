# Update to the Question 3.4 census: circle groups and PL interval-exchange groups (09-18)

This updates §1 and §3 of `research/artifacts/q34-known-actors-coverage-2026-09-13.md`.
The target, `fp-simple-groups-embed-in-fp-simple-mif-groups` (BFFHZ Question 3.4), stays
OPEN. For a finitely presented simple `S`, Question 3.4 for `S` is equivalent to PBH for
`S` (`bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`). Each row below is settled by a
**type (A) action of the group itself**, which is also a positive instance of Zaremsky's
Question 5.13(i).

All new nodes are lane proofs, elementary, not reviewed, with no novelty claimed.

| Family (census §3) | Status now | Node | Inputs cited, not re-derived |
|---|---|---|---|
| Lodha's finitely presented simple circle group `S = ⟨T, s⟩` (arXiv:1710.06220) | **PBH; own type (A) action**, 2-transitive on `P^1(Q)` | `lodha-simple-circle-group-has-a-type-a-action` (1e64376ae) | Lodha's finite presentation, simplicity and standard forms (TeX read at source) |
| Stein's circle groups `T(l; Z[1/m], ⟨n_i⟩)` and all their subgroups | **PBH**; `d = gcd(n_i − 1)` pair orbits | `circle-pl-groups-act-with-type-a-on-breakpoint-orbits` (33f9eaf07) | Stein 1992 `F_∞` (not read) |
| Golden-ratio `T_τ` and its simple index-2 subgroup `T_xz` (Burillo–Nucinkis–Reeves) | **PBH; own type (A) action**, 2-transitive for `T_τ` | same node | Cleary: `F_τ` is `F_∞`; BNR l.101: `T_τ` is `F_∞` |
| Golden-ratio `V_τ` and its simple index-2 subgroup `V_xz` | **PBH; own type (A) action**, highly transitive for `V_τ` | `interval-exchange-pl-groups-act-with-type-a-on-breakpoints` (32ee40ce8) | BNR l.101: `V_τ` is `F_∞` |
| Stein's `V`-groups `V(l; Z[1/m], ⟨n_i⟩)` | **PBH** whenever finitely presented | same node | Stein's finiteness theorem (not read) |
| Rattaggi's simple lattices in products of trees (e.g. `Σ_0`, arXiv:math/0411546) | not settled | — | see below |
| BBMZ hyperbolic hosts | not checked | — | — |

## Mechanisms

- **Circle groups containing `T`.** A finitely presented `Γ ≤ Homeo^+(S^1)` that contains
  `T` (Thurston's `PSL_2(Z)` model) and preserves `P^1(Q)` is already 2-transitive on
  `P^1(Q)`. Its action is of type (A) exactly when `Stab_Γ(∞)` is finitely generated.
  For Lodha's `S`, the standard forms give `Stab(∞) = ⟨F, w_{σ,τ}⟩`, and `F` has at most
  8 orbits on the `w`-generators.
- **PL circle groups.** The pair orbits are the Bieri–Strebel orbits
  `A/(IP·A)` (Corollary A1). The stabilizer is the interval group `G([0,l];A,P)`, which
  needs a separate finite-generation input.
- **PL interval-exchange (`V`-type) groups.** The stabilizer of `0` is
  `⟨K_{δ_0} ≅ V, g, germ lifts⟩`: one contraction toward `0` sweeps a copy of the group
  over the whole kernel of the germ map. So finite generation of the stabilizer is
  automatic, and when `IP·A = A` the action is highly transitive.

## Rattaggi's lattices: the exact gap

For a torsion-free simple cocompact lattice `Γ < Aut(T_1) × Aut(T_2)`, the projection
`pr_1` is injective because `Γ` is simple, and `cd Γ ≤ 2`. So Le Boudec's argument in
BFFHZ Remark 3.5 goes through verbatim once
`H_1 = \overline{pr_1(Γ)}` is 2-transitive on `∂T_1`. The steps are: extreme proximality
from density, then topological freeness, since there is no `Z^3` in cohomological
dimension 2, then high transitivity by FLMMS22 Theorem B.

Rattaggi's `Σ_0` is the index-4 simple subgroup of an `(8,6)`-group `Σ`. The local
actions `P^{(1)}(Σ)` are 2-transitive (his use of the Burger–Mozes normal subgroup
theorem, `NSTspecial`, l.188–192 of `math/0411546`). The missing check is that the
closure of `pr_1(Σ_0)`, not only of `pr_1(Σ)`, is boundary-2-transitive. Finite-index
passage can shrink the local action. Two citations remain unread here: Burger–Mozes's
local-to-boundary 2-transitivity lemma and FLMMS22 Theorem B.

## Still open after this update

- Rattaggi's lattices (the check above).
- BBMZ hyperbolic hosts: plausibly covered by BFFHZ Remark 3.5, if they contain a
  Higman–Thompson commutator subgroup, but that is not checked.
- The general Question 3.4.
