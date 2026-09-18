---
rg: 2
id: sl3z-level-three-degree-two-failure-proof
kind: route
title: n^26 discrete classes against a bounded profinite count; a residually finite finite extension would inflate its class; the Z-extension inherits bounded centre orders
target: sl3z-level-three-fails-degree-two-goodness
requires:
  - sl3z-level-three-congruence-subgroup-has-b2-26
  - sl3z-finite-index-fd-projective-multiplier-is-finite
  - sl3z-finite-index-z-extension-centres-stay-bounded
  - bdhv-central-extension-property-t
  - elementary-groups-over-fg-rings-have-property-t
---

`Γ = Γ(3)`. All coefficient modules are trivial. `Γ^` is the profinite completion.

## 0. Standing facts

- **Abelianization.** `Γ` has (T), as in §2 of `sl3z-level-three-b2-euler-count-proof`, which
  applies `elementary-groups-over-fg-rings-have-property-t`. So `Γ^ab` is finite.
- **Finite presentation.** `Γ` has finite index in `SL_3(Z)`, so it is finitely presented.
- **Degree-one classes.** `H^1_cts(Γ^; Q/Z) = Hom(Γ, Q/Z)`.
  - A homomorphism `Γ -> Q/Z` has finitely generated torsion image, which is finite. So its
    kernel has finite index, and it extends continuously to `Γ^`.
  - Conversely, continuous homomorphisms `Γ^ -> Q/Z` restrict to `Γ`, and `Γ` is dense in `Γ^`.
  - This group is finite, of order `|Γ^ab|`.
- **Profinite multiplier.** `H^2_cts(Γ^; Q/Z)` is finite, by (SF1) of
  `sl3z-finite-index-fd-projective-multiplier-is-finite` at `K = Γ`.
- Hence `C_0 < ∞`.

## 1. Item 1: the count

- **Profinite side.** The sequence `0 -> Z/n -> Q/Z -n-> Q/Z -> 0` consists of discrete torsion
  modules. It gives an exact sequence in continuous cohomology of the profinite group `Γ^`
  (standard, e.g. Serre, *Galois Cohomology* I.2.2):

```text
H^1_cts(Γ^; Q/Z) -> H^2_cts(Γ^; Z/n) -> H^2_cts(Γ^; Q/Z).
```

  So `|H^2_cts(Γ^; Z/n)| <= C_0` for every `n`.
- **Discrete side.** By the integral forms of `sl3z-level-three-congruence-subgroup-has-b2-26`,
  `|H^2(Γ; Z/n)| >= n^26`.
- **Conclusion.** The cokernel of inflation has order at least `n^26 / C_0`.
- **Low degrees.** Degree one: both sides are `Hom(Γ, Z/n)`, and the argument above is the same.
  Degree two: inflation is injective for every group, which is recalled and not load-bearing for
  items 2--3.

## 2. Item 2: finite central extensions

Fix `n` with `n^26 > C_0`. By §1 there is an `α ∈ H^2(Γ; Z/n)` outside the image of inflation.

**Claim.** If `E_α` were residually finite, `α` would be inflated from a finite quotient of `Γ`,
hence from `Γ^`.

*Proof.*
- **A finite quotient.** `A = Z/n` is finite and `E_α` is residually finite. So there is a
  finite-index normal subgroup `N ⊴ E_α` with `N ∩ A = 1`.
- **Its extension.** Let `Q = Γ / π(N)`, a finite quotient of `Γ`, where `π : E_α -> Γ`. Then
  `1 -> A -> E_α / N -> Q -> 1` is exact, because `A ∩ N = 1` and `π(N)` is the image of `N`.
  It is central, and has class `β ∈ H^2(Q; A)`.
- **The comparison map.** Consider `φ : E_α -> (E_α/N) ×_Q Γ`, `e ↦ (eN, π(e))`.
  - It is injective: its kernel is `N ∩ ker π = N ∩ A = 1`.
  - It is surjective. The target is an extension of `Γ` by `A`, and `φ` is the identity on `A`
    and on the quotient `Γ`, so the five lemma applies.
- **Conclusion.** `E_α` is the pullback of `E_α / N` along `Γ -> Q`, so `α = inf^Q_Γ(β)`.
  - `inf^Q_Γ` factors through `H^2_cts(Γ^; A)`. □

So `E_α` is not residually finite. By `finite-central-extension-rf-iff-virtually-splits`,
equivalently, `α` restricts nontrivially to every finite-index subgroup. That equivalence is not
needed here.

The other properties:
- `E_α` is finitely presented, as an extension of finitely presented groups.
- `E_α^ab` is finite, since `A -> E_α^ab -> Γ^ab -> 0` is exact.
- So `E_α` has (T) by `bdhv-central-extension-property-t`, with `C = A` and `E_α / A = Γ`.

## 3. Item 3: the Z-extension

- **The class.** Pick `c ∈ H^2(Γ; Z)` with nonzero real image `c_R`. It exists, since the image
  of `H^2(Γ; Z)` in `H^2(Γ; R) ≅ R^26` is a full lattice (integral forms of the Betti node).
- **Evaluation.** Under universal coefficients `c_R ∈ Hom(H_2(Γ; Z), R)`, and it is the
  evaluation `x ↦ <c, x>`. So `<c, ·> : H_2(Γ; Z) -> Z` is nonzero, and its image `mZ` has
  finite index.
- **Finite abelianization.** The 5-term exact sequence of `1 -> Z -> K~ -> Γ -> 1`, with trivial
  action on the centre, reads

```text
H_2(Γ; Z) --(±<c,·>)--> Z --> H_1(K~; Z) --> H_1(Γ; Z) --> 0.
```

  So `H_1(K~)` is an extension of the finite `Γ^ab` by a quotient of `Z/m`, which is finite.
- **Bounded centre orders.** `sl3z-finite-index-z-extension-centres-stay-bounded` applies with
  `K = Γ`. By its item 4, the image of `z` in every finite quotient of `K~` has order `<= C`.
  - Put `M = C!`. Then `z^M` lies in the kernel of every homomorphism of `K~` to a finite group.
  - `z^M ≠ 1` because `z` has infinite order.
  - So `K~` is not residually finite.
- **Other properties.**
  - `K~` is torsion-free, as an extension of torsion-free `Γ` (§1 of the Betti proof) by `Z`.
  - It is finitely presented, as an extension of finitely presented groups.
  - It has (T), by item 5 of that node, or directly by `bdhv-central-extension-property-t`.
