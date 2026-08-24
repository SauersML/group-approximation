import GroupApproximation.Sofic.UniversalFactorization
import GroupApproximation.Sofic.NormMFResidualExactQuotient
import GroupApproximation.Sofic.LocalCentralQuotientLifting

/-!
# Radical automorphization: one forgotten relation propagates through every scale

A residual is a lower bound on what an approximation theory forgets, and it is
usually produced one element at a time.  This module records the mechanism that
turns a *local* forgotten relation into a forgotten relation at every scale.

Let `R : G →* G` be a **surjective endomorphism** whose kernel is already
invisible, `ker R ≤ Rad G`.  Section 42's universal factorization theorem then
says `Rad G = R⁻¹(Rad G)`; iterating that single identity gives

```text
ker (R^n) ≤ Rad G   for every n,        K_∞(R) := ⋃_n ker (R^n) ≤ Rad G.
```

Two things are worth separating out.

*The engine is not analytic.*  `stableKernel_le_of_comap_le` asks only for
`Rad.comap R ≤ Rad` — one inclusion of subgroups, no surjectivity, no target
class, no countability.  Everything analytic is packed into supplying that
inclusion, and `UniversalFactorization` supplies it for each of the four target
classes at once.  So the same proof runs for the MF radical, the
finite-dimensional unitary residual, the finite residual, and the all-fields
linear residual, which is what `stableKernel_le_coronaMFResidual` and its three
companions record.

*Maximality is the same lemma read backwards.*  "The descended map is
injective on `G ⧸ N`" says exactly `N.comap R ≤ N`, so
`stableKernel_le_of_injective_descent` is `stableKernel_le_of_comap_le` with the
radical replaced by `N`.  Hence `K_∞(R)` is contained in every quotient on which
`R` becomes injective, while on `G ⧸ K_∞(R)` itself the descended map is
bijective (`descendEquiv`).  The automorphization quotient is the largest
quotient through which `R` descends to an automorphism.

Combining the two directions with the exact-radical criterion of
`NormMFResidualExactQuotient` closes the loop: if the automorphization quotient
is operator MF then `Rad_MF G = K_∞(R)` exactly, with no residual slack
(`coronaMFResidual_eq_stableKernel`).

Nothing here constructs an `R`; that is the producing lane's job.  This module
is the propagation step alone.
-/

namespace GroupApproximation
namespace RadicalAutomorphization

open LocalCentralQuotientLifting MatricialStabilityRadical

universe u

variable {G : Type u} [Group G]

/-! ## Iterates of an endomorphism

`LocalCentralQuotientLifting.iterateEnd` is the bundled `n`-fold composite; the
two facts needed here are that iterates commute with the endomorphism and that
they inherit surjectivity. -/

/-- Applying `R` before the `n`-th iterate is the same as applying it after:
iterates of `R` commute with `R`. -/
theorem iterateEnd_apply_map (R : G →* G) (n : ℕ) (x : G) :
    iterateEnd R n (R x) = R (iterateEnd R n x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterateEnd_succ_apply, ih]

/-- Every iterate of a surjective endomorphism is surjective. -/
theorem surjective_iterateEnd (R : G →* G) (hR : Function.Surjective R) (n : ℕ) :
    Function.Surjective (iterateEnd R n) := by
  induction n with
  | zero => exact fun y => ⟨y, rfl⟩
  | succ n ih =>
      intro y
      obtain ⟨z, rfl⟩ := hR y
      obtain ⟨x, rfl⟩ := ih z
      exact ⟨x, rfl⟩

/-- The kernels of the iterates increase. -/
theorem monotone_ker_iterateEnd (R : G →* G) :
    Monotone fun n : ℕ => (iterateEnd R n).ker := by
  refine monotone_nat_of_le_succ fun n x hx => ?_
  have hx' : iterateEnd R n x = 1 := MonoidHom.mem_ker.mp hx
  exact MonoidHom.mem_ker.mpr (by rw [iterateEnd_succ_apply, hx', map_one])

/-! ## The stable kernel -/

/-- `K_∞(R) = ⋃_n ker (R^n)`, the stable kernel of an endomorphism. -/
def stableKernel (R : G →* G) : Subgroup G := ⨆ n : ℕ, (iterateEnd R n).ker

/-- Membership in the stable kernel is being killed by *some* iterate.  The
kernels increase, so the supremum is their union. -/
theorem mem_stableKernel_iff {R : G →* G} {x : G} :
    x ∈ stableKernel R ↔ ∃ n, iterateEnd R n x = 1 :=
  (Subgroup.mem_iSup_of_directed (monotone_ker_iterateEnd R).directed_le).trans
    (exists_congr fun _ => MonoidHom.mem_ker)

theorem ker_le_stableKernel (R : G →* G) : R.ker ≤ stableKernel R := by
  intro x hx
  exact mem_stableKernel_iff.mpr ⟨1, by
    rw [iterateEnd_succ_apply, iterateEnd_zero_apply]
    exact MonoidHom.mem_ker.mp hx⟩

/-- The stable kernel is normal: an element is killed at some finite stage, and
that stage's kernel is already normal. -/
instance stableKernel_normal (R : G →* G) : (stableKernel R).Normal := by
  constructor
  intro x hx g
  obtain ⟨m, hm⟩ := mem_stableKernel_iff.mp hx
  refine mem_stableKernel_iff.mpr ⟨m, ?_⟩
  rw [map_mul, map_mul, hm, mul_one, ← map_mul]
  simp

/-- `R` maps the stable kernel into itself, so it descends to the quotient. -/
theorem map_mem_stableKernel {R : G →* G} {x : G} (hx : x ∈ stableKernel R) :
    R x ∈ stableKernel R := by
  obtain ⟨n, hn⟩ := mem_stableKernel_iff.mp hx
  refine mem_stableKernel_iff.mpr ⟨n, ?_⟩
  rw [iterateEnd_apply_map, hn, map_one]

/-! ## The engine

One inclusion of subgroups is the whole hypothesis. -/

/-- Iterating a single containment.  If `R` pulls `Rad` back inside itself then
so does every iterate of `R`. -/
theorem comap_iterateEnd_le {Rad : Subgroup G} {R : G →* G}
    (h : Rad.comap R ≤ Rad) (n : ℕ) : Rad.comap (iterateEnd R n) ≤ Rad := by
  induction n with
  | zero => exact le_of_eq (Subgroup.comap_id Rad)
  | succ n ih =>
      have hstep : Rad.comap (iterateEnd R (n + 1))
          = (Rad.comap R).comap (iterateEnd R n) := by
        rw [Subgroup.comap_comap]
        rfl
      rw [hstep]
      exact le_trans (Subgroup.comap_mono h) ih

/-- Every iterate kernel is already inside `Rad`. -/
theorem ker_iterateEnd_le {Rad : Subgroup G} {R : G →* G}
    (h : Rad.comap R ≤ Rad) (n : ℕ) : (iterateEnd R n).ker ≤ Rad := by
  intro x hx
  refine comap_iterateEnd_le h n ?_
  rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
  exact Rad.one_mem

/-- **The automorphization principle, abstract form.**  A subgroup that `R`
pulls back inside itself already contains the whole stable kernel.  No
surjectivity, no target class, no countability: everything analytic lives in
the hypothesis `Rad.comap R ≤ Rad`. -/
theorem stableKernel_le_of_comap_le {Rad : Subgroup G} {R : G →* G}
    (h : Rad.comap R ≤ Rad) : stableKernel R ≤ Rad :=
  iSup_le fun n => ker_iterateEnd_le h n

/-- **Maximality**, which is the same lemma read backwards: `R` descends to an
injection on `G ⧸ N` exactly when `N.comap R ≤ N`, and then `N` already
contains `K_∞(R)`. -/
theorem stableKernel_le_of_injective_descent {N : Subgroup G} {R : G →* G}
    (h : ∀ x : G, R x ∈ N → x ∈ N) : stableKernel R ≤ N :=
  stableKernel_le_of_comap_le fun x hx => h x (Subgroup.mem_comap.mp hx)

/-! ## The four residuals

The hypothesis of the engine is exactly what Section 42's universal
factorization theorems produce, one per class of targets. -/

/-- Surjectivity plus an invisible kernel gives the engine's hypothesis for the
MF radical: this is `Rad_MF G = R⁻¹(Rad_MF G)`, read in one direction. -/
theorem coronaMFResidual_comap_le (R : G →* G) (hR : Function.Surjective R)
    (hker : R.ker ≤ coronaMFResidual G) :
    (coronaMFResidual G).comap R ≤ coronaMFResidual G :=
  (UniversalFactorization.coronaMFResidual_eq_comap R hR hker).ge

/-- **Radical automorphization for the MF radical.**  One invisible kernel of a
surjective self-map makes the whole stable kernel invisible. -/
theorem stableKernel_le_coronaMFResidual (R : G →* G)
    (hR : Function.Surjective R) (hker : R.ker ≤ coronaMFResidual G) :
    stableKernel R ≤ coronaMFResidual G :=
  stableKernel_le_of_comap_le (coronaMFResidual_comap_le R hR hker)

/-- The same statement for the finite-dimensional unitary residual. -/
theorem stableKernel_le_fdUnitaryResidual (R : G →* G)
    (hR : Function.Surjective R) (hker : R.ker ≤ fdUnitaryResidual G) :
    stableKernel R ≤ fdUnitaryResidual G :=
  stableKernel_le_of_comap_le
    (UniversalFactorization.fdUnitaryResidual_eq_comap R hR hker).ge

/-- The same statement for the finite residual. -/
theorem stableKernel_le_finiteResidual (R : G →* G)
    (hR : Function.Surjective R) (hker : R.ker ≤ finiteResidual G) :
    stableKernel R ≤ finiteResidual G :=
  stableKernel_le_of_comap_le
    (UniversalFactorization.finiteResidual_eq_comap R hR hker).ge

/-- The same statement for the all-fields linear residual. -/
theorem stableKernel_le_linearResidual (R : G →* G)
    (hR : Function.Surjective R) (hker : R.ker ≤ linearResidual G) :
    stableKernel R ≤ linearResidual G :=
  stableKernel_le_of_comap_le
    (UniversalFactorization.linearResidual_eq_comap R hR hker).ge

/-! ## Factorization through every scale -/

/-- Every corona representation factors through `R^n`, for every `n` at once:
the whole representation functor is blind to the finite stages of `R`. -/
theorem exists_factorization_through_iterateEnd (R : G →* G)
    (hR : Function.Surjective R) (hker : R.ker ≤ coronaMFResidual G)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : G →* NormMatrixCoronaUnitary X) (n : ℕ) :
    ∃ psi : G →* NormMatrixCoronaUnitary X, psi.comp (iterateEnd R n) = rho :=
  UniversalFactorization.exists_comp_eq (iterateEnd R n)
    (surjective_iterateEnd R hR n) rho
    (fun _ hx => MonoidHom.mem_ker.mpr
      (ker_iterateEnd_le (coronaMFResidual_comap_le R hR hker) n hx X hX rho))

/-! ## The automorphization quotient -/

/-- The endomorphism descended to `G ⧸ K_∞(R)`. -/
def descend (R : G →* G) : G ⧸ stableKernel R →* G ⧸ stableKernel R :=
  QuotientGroup.lift (stableKernel R)
    ((QuotientGroup.mk' (stableKernel R)).comp R)
    (fun x hx => by
      have h : R x ∈ stableKernel R := map_mem_stableKernel hx
      simpa [MonoidHom.mem_ker, QuotientGroup.eq_one_iff] using h)

@[simp] theorem descend_mk (R : G →* G) (x : G) :
    descend R (QuotientGroup.mk x) = QuotientGroup.mk (R x) := rfl

theorem descend_surjective (R : G →* G) (hR : Function.Surjective R) :
    Function.Surjective (descend R) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (stableKernel R) q
  obtain ⟨y, rfl⟩ := hR x
  exact ⟨QuotientGroup.mk y, rfl⟩

/-- Removing the stable kernel is exactly what makes `R` injective: if `R x`
dies at stage `n` then `x` dies at stage `n + 1`. -/
theorem descend_injective (R : G →* G) : Function.Injective (descend R) := by
  rw [← MonoidHom.ker_eq_bot_iff (descend R), eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (stableKernel R) q
  have hRx : R x ∈ stableKernel R := by
    have h := MonoidHom.mem_ker.mp hq
    rwa [QuotientGroup.mk'_apply, descend_mk, QuotientGroup.eq_one_iff] at h
  obtain ⟨n, hn⟩ := mem_stableKernel_iff.mp hRx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    mem_stableKernel_iff]
  exact ⟨n + 1, by rw [iterateEnd_succ_apply, ← iterateEnd_apply_map, hn]⟩

/-- **The automorphization quotient.**  On `G ⧸ K_∞(R)` the descended
endomorphism is an automorphism, and by `stableKernel_le_of_injective_descent`
this is the largest quotient on which that happens. -/
noncomputable def descendEquiv (R : G →* G) (hR : Function.Surjective R) :
    (G ⧸ stableKernel R) ≃* (G ⧸ stableKernel R) :=
  MulEquiv.ofBijective (descend R) ⟨descend_injective R, descend_surjective R hR⟩

/-! ## Exactness -/

/-- **The renormalization step, closed.**  If the automorphization quotient is
operator MF then the stable kernel is not merely a lower bound for the MF
radical but equal to it: the local forgotten relation `ker R` propagates to
every scale, and nothing else is forgotten. -/
theorem coronaMFResidual_eq_stableKernel [Countable G] (R : G →* G)
    (hR : Function.Surjective R) (hker : R.ker ≤ coronaMFResidual G)
    (hquot : IsOperatorMF (G ⧸ stableKernel R)) :
    coronaMFResidual G = stableKernel R :=
  coronaMFResidual_eq_of_le_and_quotient_isOperatorMF (stableKernel R)
    (stableKernel_le_coronaMFResidual R hR hker) hquot

end RadicalAutomorphization
end GroupApproximation
