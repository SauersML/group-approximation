# `GroupApproximation/AlgTop/` — integral singular cohomology foundation

Lane `found-cohomology-ring`, 2026-09-05. **This file is the API contract the
dependent lanes (`found-cpn-cohomology`, `found-chern-classes`,
`found-euler-class`, `found-ktheory-bott`) code against.** Signatures here are
final unless this file says otherwise; changes are announced by lane message.

## 0. What already exists (do not rebuild it)

`GroupApproximation/ThirdParty/HamSandwich/SphereOddDegree/AlgebraicTopology/`
already contains, **generic in a `CommRing R`** (only the *Leibniz rule* and
everything above it is `ZMod 2`-specific):

| Declaration | File | Layer |
|---|---|---|
| `singularCochainComplexFunctor (R) (M) : TopCatᵒᵖ ⥤ CochainComplex (ModuleCat R) ℕ` | `SingularCohomology` | 2 |
| `singularCohomologyFunctor (R) (M) (n) : TopCatᵒᵖ ⥤ ModuleCat R` | `SingularCohomology` | 2 |
| `tensorSigns_up_nat : (ComplexShape.up ℕ).TensorSigns` | `CupProductScaffolding` | 3 |
| `frontFace / backFace / frontSimplex / backSimplex` (+ naturality) | `AlexanderWhitney` | 4 |
| `singularCochainGroup R Z p`, `cochainEval`, `cochain_ext` | `CupProduct` | 5 |
| `cochainCup p q φ ψ`, `cochainOne`, `cochainCup_naturality` | `CupProduct` | 5 |
| `cochainPullback`, `cochainPullback_eval` | `CupProduct` | 5 |
| `frontFace_comp_δ_of_le/_gt`, `backFace_comp_δ_of_le/_gt`, `aw_endpoint_front/_back`, `awCastLeft`, `aw_degree_left_succ`, `aw_degree_right_succ` | `AlexanderWhitneyFaceMaps` | 6 |
| `cochainCoboundary`, `cochainCoboundary_eval`, `cochainCast`, `cochainCast_eval_awCastSimplex`, `cochainCast_eval_right`, `frontSimplex_faceSimplex_of_le/_endpoint`, `backSimplex_faceSimplex_of_le/_endpoint` | `AlexanderWhitneyChainMap` | 7 |
| `mvHomologyIso`, `mvHomologyIso_succ` (generic in `R`) | `MayerVietoris` | 12 |
| `subChainComplex R X S`, `subspaceHomologyIso`, small-chains quasi-iso | `SubChainSubspaceBridge`, `SmallChains*` | ≤11 |
| `Sphere n := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`, `upperOpens/lowerOpens` and their contractibility, `sphereBandHomotopyEquiv` | `Basic`, `SphereHomologyMVStep` | ≤13 |

The only genuinely `ZMod 2`-specific step in that stack is
`aw_cochain_leibniz_zmod2` (`AlexanderWhitneyChainMap` §5), which uses
`sum_split_char2` to kill the Koszul signs. **Everything below it is generic.**

Consequence: `AlgTop` imports the vendored tree at layer 7
(`…AlgebraicTopology.AlexanderWhitneyChainMap`) and at layer 13 for the sphere
work, and adds the *signed* theory on top. Layers 0–7 are the first modules the
port lanes `hamsandwich-port-A/B` bring green, so this dependency is at the
shallow end of the port.

## 1. Module list, in dependency order

```text
GroupApproximation/AlgTop/CochainLeibniz.lean      -- signed Leibniz (new math)
GroupApproximation/AlgTop/SingularCohomology.lean  -- H^n(X;R), classes, pullback
GroupApproximation/AlgTop/CupProduct.lean          -- ⌣ on H^*, unit, assoc, naturality
GroupApproximation/AlgTop/Spheres.lean             -- H^*(S^n;ℤ), generator, pairing
GroupApproximation/AlgTop/Kunneth.lean             -- free-case Künneth, ring iso
```

Namespace: `GroupApproximation.AlgTop`. Coefficients are a general
`(R : Type) [CommRing R]` throughout; `ℤ` specializations carry the suffix `ℤ`.

## 2. `CochainLeibniz.lean` — exact signatures

```lean
/-- Sign-aware splitting of a sum over `Fin (p+q+2)` into a front block matching
`A : Fin (p+2) → M`, a back block matching `B : Fin (q+2) → M`, whose two
endpoints cancel: `A (Fin.last (p+1)) = - B 0`. -/
theorem sum_split_signed {M : Type} [AddCommGroup M] (p q : ℕ)
    (L : Fin (p + q + 2) → M) (A : Fin (p + 2) → M) (B : Fin (q + 2) → M)
    (hle : ∀ k : Fin (p + q + 2), (hk : k.val ≤ p) → L k = A ⟨k.val, by omega⟩)
    (hgt : ∀ k : Fin (p + q + 2), (hk : p < k.val) →
      L k = B ⟨k.val - p, by have := k.isLt; omega⟩)
    (hend : A (Fin.last (p + 1)) = - B 0) :
    ∑ k, L k = (∑ i, A i) + ∑ j, B j

/-- **Alexander–Whitney cochain Leibniz identity, all coefficients.**
`δ(φ ⌣ ψ) = δφ ⌣ ψ + (-1)^p φ ⌣ δψ`. -/
theorem aw_cochain_leibniz (R : Type) [CommRing R] {X : TopCat.{0}} (p q : ℕ)
    (φ : singularCochainGroup R X p) (ψ : singularCochainGroup R X q) :
    cochainCoboundary R X (p + q) (cochainCup p q φ ψ)
      = cochainCast (aw_degree_left_succ p q)
            (cochainCup (p + 1) q (cochainCoboundary R X p φ) ψ)
        + ((-1 : R) ^ p) •
            cochainCast (aw_degree_right_succ p q)
              (cochainCup p (q + 1) φ (cochainCoboundary R X q ψ))
```

Proof: exactly the `aw_cochain_leibniz_zmod2` skeleton with
`sum_split_char2` replaced by `sum_split_signed`, the three sign bookkeeping
lemmas being `(-1)^k` on the front block, `(-1)^(p+j)` on the back block, and
`(-1)^(p+1) = -(-1)^p` at the endpoint.

Corollaries used by `CupProduct.lean`:

```lean
theorem cochainCup_isCocycle {φ ψ} (hφ : δφ = 0) (hψ : δψ = 0) : δ (φ ⌣ ψ) = 0
theorem cochainCup_coboundary_left  -- (δα) ⌣ ψ  is a coboundary, ψ a cocycle
theorem cochainCup_coboundary_right -- φ ⌣ (δβ)  is a coboundary, φ a cocycle
```

## 3. `SingularCohomology.lean` — exact signatures

```lean
/-- The singular cochain complex `C^•(X; R)` with coefficients in `R`. -/
noncomputable abbrev cochainCx (R : Type) [CommRing R] (X : TopCat.{0}) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  (singularCochainComplexFunctor R (ModuleCat.of R R)).obj (Opposite.op X)

/-- `Hⁿ(X; R)`. -/
noncomputable abbrev cohomology (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    ModuleCat.{0} R := (cochainCx R X).homology n

/-- `Hⁿ(X; ℤ)`. -/
noncomputable abbrev cohomologyℤ (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℤ :=
  cohomology ℤ X n

/-- `φ` is a cocycle. -/
def IsCocycle (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup R X n) : Prop := cochainCoboundary R X n φ = 0

/-- The cohomology class of a cocycle. -/
noncomputable def cocycleClass (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup R X n) (hφ : IsCocycle R X n φ) : cohomology R X n

theorem cocycleClass_congr  {φ φ'} (h : φ = φ') (hφ) (hφ') :
    cocycleClass R X n φ hφ = cocycleClass R X n φ' hφ'
theorem cocycleClass_surjective (a : cohomology R X n) :
    ∃ φ hφ, cocycleClass R X n φ hφ = a
theorem cocycleClass_add / cocycleClass_smul / cocycleClass_zero
/-- A coboundary is nullhomologous.  `h : m + 1 = n` transports the degree. -/
theorem cocycleClass_coboundary_zero (m : ℕ) (ψ : singularCochainGroup R X m)
    (h : m + 1 = n) (hφ) : cocycleClass R X n (cochainCast h (δ ψ)) hφ = 0

/-- A chosen cocycle representative of a class. -/
noncomputable def classRepr (R) [CommRing R] (X) (n) (a : cohomology R X n) :
    singularCochainGroup R X n
theorem classRepr_isCocycle (a) : IsCocycle R X n (classRepr R X n a)
theorem cocycleClass_classRepr (a) :
    cocycleClass R X n (classRepr R X n a) (classRepr_isCocycle R X n a) = a

/-- Pullback `f^* : Hⁿ(Y;R) ⟶ Hⁿ(X;R)`. -/
noncomputable def cohPullback (R : Type) [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) : cohomology R Y n ⟶ cohomology R X n

theorem cohPullback_cocycleClass (f) (n) (φ) (hφ) (hpb) :
    (cohPullback R f n).hom (cocycleClass R Y n φ hφ)
      = cocycleClass R X n (cochainPullback f n φ) hpb
theorem cohPullback_id (X) (n) : cohPullback R (𝟙 X) n = 𝟙 _
theorem cohPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n) :
    cohPullback R (f ≫ g) n = cohPullback R g n ≫ cohPullback R f n
/-- Homotopy invariance. -/
theorem cohPullback_eq_of_homotopy {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (n) :
    cohPullback R f n = cohPullback R g n
```

## 4. `CupProduct.lean` — exact signatures (**report these to dependent lanes**)

```lean
/-- The **cup product** `⌣ : Hᵖ(X;R) → H^q(X;R) → H^{p+q}(X;R)`. -/
noncomputable def cup {R : Type} [CommRing R] {X : TopCat.{0}} {p q : ℕ}
    (a : cohomology R X p) (b : cohomology R X q) : cohomology R X (p + q)

@[inherit_doc] infixl:70 " ⌣ " => cup

/-- Computation rule: the cup of two cocycle classes is the class of the
Alexander–Whitney cochain cup. -/
theorem cup_mk {p q} (φ ψ) (hφ hψ hcup) :
    cup (cocycleClass R X p φ hφ) (cocycleClass R X q ψ hψ)
      = cocycleClass R X (p + q) (cochainCup p q φ ψ) hcup

theorem cup_add_left / cup_add_right / cup_smul_left / cup_smul_right
/-- The unit `1 ∈ H⁰(X;R)`. -/
noncomputable def one (R : Type) [CommRing R] (X : TopCat.{0}) : cohomology R X 0
theorem one_cup (b : cohomology R X q) : cast (one R X ⌣ b) = b   -- degree `0 + q = q`
theorem cup_one (a : cohomology R X p) : cast (a ⌣ one R X) = a   -- degree `p + 0 = p`

/-- Strict associativity (the AW cup product is associative already on cochains). -/
theorem cup_assoc {p q r} (a b c) :
    cohCast (add_assoc p q r) ((a ⌣ b) ⌣ c) = a ⌣ (b ⌣ c)

/-- Naturality: `f^*(a ⌣ b) = f^* a ⌣ f^* b`. -/
theorem cohPullback_cup (f : X ⟶ Y) {p q} (a b) :
    (cohPullback R f (p + q)).hom (a ⌣ b)
      = (cohPullback R f p).hom a ⌣ (cohPullback R f q).hom b

/-- Degree transport for cohomology classes. -/
noncomputable def cohCast {m m' : ℕ} (h : m = m') : cohomology R X m ⟶ cohomology R X m'
```

`cohCast` is the eqToHom transport; every degree-arithmetic mismatch downstream
should be routed through it rather than through `Nat` rewriting inside a
dependent type.

**Graded-commutativity** `a ⌣ b = (-1)^{pq} (b ⌣ a)` is *not* in this module.
The AW diagonal is not cocommutative on the nose; the identity needs the
Eilenberg–Zilber / acyclic-models chain homotopy between `Δ` and `T ∘ Δ`. It is
scheduled as `AlgTop/CupCommutativity.lean` and is the one genuinely hard piece
of the ring structure. Lanes that need only *even-degree* classes (all of
`H^*(∏ CP^{d_j})`, `c_j(E)`, `ch_q`) never need it: even-degree classes commute
for free once the identity is available in that case, and the campaign's only
odd classes are `t ∈ H¹(S¹)` and `x ∈ H⁵(S⁵)`, which appear at most linearly.

## 5. `Spheres.lean` — exact signatures

```lean
abbrev Sph (n : ℕ) : TopCat.{0} := TopCat.of (Sphere n)   -- vendored `Sphere`

/-- `Hⁿ(Sⁿ; ℤ) ≅ ℤ` for `n ≥ 1`. -/
noncomputable def sphereTopCohomologyIso (n : ℕ) (hn : 1 ≤ n) :
    cohomologyℤ (Sph n) n ≅ ModuleCat.of ℤ ℤ
/-- The chosen generator of `Hⁿ(Sⁿ; ℤ)`. -/
noncomputable def sphereGen (n : ℕ) (hn : 1 ≤ n) : cohomologyℤ (Sph n) n
theorem sphereGen_generates (n) (hn) (a) : ∃ k : ℤ, a = k • sphereGen n hn
theorem sphereGen_ne_zero (n) (hn) : sphereGen n hn ≠ 0
/-- Vanishing off degrees `0` and `n`. -/
theorem sphere_cohomology_isZero (n k : ℕ) (hn : 1 ≤ n) (hk : k ≠ 0) (hkn : k ≠ n) :
    Limits.IsZero (cohomologyℤ (Sph n) k)
/-- The top-degree pairing `⟨·, [Sⁿ]⟩ : Hⁿ(Sⁿ;ℤ) → ℤ`, normalised so that the
chosen generator pairs to `1`. -/
noncomputable def spherePairing (n : ℕ) (hn : 1 ≤ n) : cohomologyℤ (Sph n) n →ₗ[ℤ] ℤ
theorem spherePairing_sphereGen (n) (hn) : spherePairing n hn (sphereGen n hn) = 1
/-- Suspension isomorphism `Hⁿ⁺¹(Sⁿ⁺¹;ℤ) ≅ Hⁿ(Sⁿ;ℤ)` (Mayer–Vietoris step). -/
noncomputable def sphereSuspensionIso (n : ℕ) (hn : 1 ≤ n) :
    cohomologyℤ (Sph (n + 1)) (n + 1) ≅ cohomologyℤ (Sph n) n
```

Route: the vendored `sphereTopHomology_step_MV` is the integral homology
statement; its ingredients (`mvHomologyIso_succ`, the band homotopy equivalence,
contractibility of the punctured hemispheres) are already generic in `R`. The
cohomology statement comes from the same MV sequence applied to the *dual*
complex, or by dualising with the Kronecker pairing over the free
(finitely-generated) integral homology of `Sⁿ`, which is where the `ℤ`
specialisation is genuinely used.

## 6. `Kunneth.lean` — exact signatures

Only the free case is needed and only the free case is built.

```lean
/-- `X` has free finitely generated integral cohomology, concentrated in
finitely many degrees.  A structure, not a `Prop`, because the downstream ring
isomorphism needs the chosen bases. -/
structure FreeCohomology (X : TopCat.{0}) where
  bound     : ℕ
  vanishing : ∀ k, bound < k → Limits.IsZero (cohomologyℤ X k)
  rank      : ℕ → ℕ
  basis     : ∀ k, Basis (Fin (rank k)) ℤ (cohomologyℤ X k)

/-- The external cross product `Hᵖ(X;ℤ) → H^q(Y;ℤ) → H^{p+q}(X × Y;ℤ)`,
`a × b = pr₁^* a ⌣ pr₂^* b`. -/
noncomputable def cross {X Y : TopCat.{0}} {p q : ℕ}
    (a : cohomologyℤ X p) (b : cohomologyℤ Y q) : cohomologyℤ (prod X Y) (p + q)

theorem cross_natural / cross_add_left / cross_add_right / cross_smul
/-- Multiplicativity of the cross product: `(a × b) ⌣ (a' × b') = ±(a⌣a') × (b⌣b')`. -/
theorem cross_cup (a a' b b') : …

/-- **Künneth, free case.**  For `X`, `Y` with free integral cohomology, the
cross product is an isomorphism
`⊕_{p+q=n} Hᵖ(X;ℤ) ⊗ H^q(Y;ℤ) ≅ Hⁿ(X × Y;ℤ)`, and the assembled map on the total
graded group is a ring isomorphism. -/
noncomputable def kunnethIso (hX : FreeCohomology X) (hY : FreeCohomology Y) (n : ℕ) :
    (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        (cohomologyℤ X pq.1.1 ⊗[ℤ] cohomologyℤ Y pq.1.2)) ≅ cohomologyℤ (prod X Y) n
theorem kunnethIso_cross : …          -- the iso is given by `cross` on pure tensors
theorem kunnethIso_mul : …            -- ring statement
```

## 7. Order of landing, and what the dependent lanes get when

1. `CochainLeibniz.lean` — the signed Leibniz rule. *No downstream lane blocks
   on it directly*, but nothing else can be built without it.
2. `SingularCohomology.lean` + `CupProduct.lean` — **this is the API that
   `found-cpn-cohomology`, `found-chern-classes` and `found-euler-class` code
   against.** Reported by lane message as soon as the signatures are committed,
   which is before they compile.
3. `Spheres.lean` — `found-euler-class` needs `spherePairing` and `sphereGen`.
4. `Kunneth.lean` — `found-cpn-cohomology` and `found-ktheory-bott`.

## 8. Traps recorded for this lane

* Degree arithmetic lives in a dependent type. `(p+1)+q` and `p+(q+1)` are
  *different* from `(p+q)+1` (the second is definitional, the first is not).
  Always transport with `cochainCast` / `cohCast`, never with `omega` inside a
  motive.
* `singularCochainGroup R Z p` is by `rfl` the hom-type
  `(C_p(Z) ⟶ ModuleCat.of R R)`; `cochain_ext` is the only extensionality
  principle that works, `ext` does not.
* The vendored files set `backward.defeqAttrib.useBackward` and
  `backward.isDefEq.respectTransparency`; any file that unfolds their
  definitions must set the same options or the definitional conversions fail.
* `TopCat.{0}` everywhere. `Sphere n` and the concrete `CP^d` of the LIX
  re-cut are `Type 0`, so this costs nothing and keeps the vendored
  universe-monomorphic API usable.
</content>
</invoke>
