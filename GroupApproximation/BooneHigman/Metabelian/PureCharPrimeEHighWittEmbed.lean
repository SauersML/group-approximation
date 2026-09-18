import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighArtinHasse
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittCoord
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# The invariant function-space criterion from a Witt embedding (bh-met-87c, part 7)

**Target.**  `EHighArtinHassePolyFunStatement` (`PureCharPrimeEHighArtinHasse.lean:55`).

**Not proved: the target itself.**  What is proved is `eHighArtinHassePolyFun_of_wittEmbed`, a
reduction to the gap `EHighArtinHasseWittEmbedStatement`.  The gap asks for three things:

* a field `L` with `ringChar L = p`;
* an injective additive `ι : M →+ W₂(L)ⁿ`, where `W₂(L)` is the explicit model
  `eHighWitt_W2 L p` (`L × L` with the length-two Witt addition);
* maps `act q : W₂(L)ⁿ → W₂(L)ⁿ` with `ι (q • m) = act q (ι m)`, each of which is
  weight-polynomial (`eHighWitt_IsWeightPoly`): every Witt coordinate of `act q x` is a
  polynomial in the Witt coordinates of `x`, of weighted degree `1` for an `x₀`-coordinate and
  `p` for an `x₁`-coordinate, where the `x₀`-coordinates have weight `1` and the
  `x₁`-coordinates have weight `p`.

Everything else is discharged here, with no further input:

* the space `V` of polynomials of weighted degree `≤ p` (`eHighWitt_polySpace`);
* its finite-dimensionality, its stability under translations (via the explicit carry
  polynomial) and under `act`, and point separation (`eHighWitt_W2_polyFun`);
* the restriction of `V` along `ι` (`eHighWitt_transport`).

**LOUD: strength of the gap.**  The gap is *not* strictly weaker in the logical sense.  Both it
and the target are true (see below), so they are trivially equivalent, and no direct derivation
of the gap from the target is known to us.  It is strictly smaller in *proof content*: it
contains no function space, no finite-dimensionality, no stability and no separation, and the
Witt-polynomial calculus for translations is proved here.  The map class is weaker than
`W₂(L)`-linearity:

* `act` need not be additive, nor a group action;
* it is only constrained on `ι(M)` through the compatibility identity;
* it only has to be weight-polynomial.

For a perfect `L` of characteristic `p`, every `W₂(L)`-matrix acts weight-polynomially.
Scalar multiplication is `(a₀, a₁) · (x₀, x₁) = (a₀ x₀, a₀ᵖ x₁ + a₁ x₀ᵖ)`, of weights `1` and `p`.
Summing the entries uses the carry, which is homogeneous of degree `p` in weight-`1` inputs.

**Non-Teichmüller units: harmless.**  A unit `(1, c)` acts by `(x₀, x₁) ↦ (x₀, x₁ + c x₀ᵖ)`.  This
is not `L`-linear in the Witt coordinates, but it is weight-polynomial, and that is all the
class requires.  This is why the class is stated via weighted polynomials and not via
`L`-linear maps.  No additive model exists: exponent `p²` never embeds into an
`F_p`-vector space.

**Truth (paper only).**  Write `R = (ℤ/p²)[Q]` and `A = R_P / P^k R_P`.

1. `M ↪ M_P`, because `M` is `P`-coprimary.  `A` is Artinian local with residue field
   `κ = Frac(R/P)`, and `M_P` is a finitely generated `A`-module.  `p ≠ 0` in `A`, since
   `p • m ≠ 0` for some `m`.
2. By the Cohen structure theorem there is a coefficient ring `C₀ = C(κ)/p² ⊆ A`, where `C(κ)`
   is the Cohen ring.  `A` is a finite `C₀`-module.
3. Let `x_j` be generators of `Q` for a cyclic decomposition, and `u_j` their images in `A`.
   Put `T = ⊗_j C₀[X]/(f_j)`, where `f_j = X^{n_j} - 1` for a torsion generator and `f_j` is a
   monic Cayley–Hamilton polynomial of `u_j` on `A` otherwise.  `T` is free and Artinian, and
   `T → A` factors through one local factor `T'`.  `T'` is projective, hence free over `C₀`.
   The `x_j` are units in `T'`, so `Q → T'ˣ`.
4. Coinduction: `M_P ↪ Hom_{C₀}(T', M_P) ↪ Hom_{C₀}(T', C₀^s) ≅ C₀^N`.  This is `T'`-linear,
   so it is `Q`-equivariant, and `Q` acts on `C₀^N` by `C₀`-matrices.  Here `M_P ↪ C₀^s`
   because every finitely generated `C₀`-module is a sum of copies of `C₀` and `κ ≅ pC₀`.
5. `C(κ)` is formally smooth over `ℤ_p`, so it has a local map to `W(κ^perf)`.  This map is an
   injection of DVRs with uniformizer `p`, so `C₀ ↪ W₂(L)` for `L = κ^perf`, and
   `C₀^N ↪ W₂(L)^N` componentwise.  The additive group of `W₂(L)` is `eHighWitt_W2 L p`, because
   the second coordinate of the model sum is the Witt polynomial `S₁`.
6. `Q` acts on `W₂(L)^N` through the extended `C₀`-matrices, which are weight-polynomial as
   explained above.

The heavy inputs are the Cohen structure theorem and Cohen rings, which Mathlib lacks, the
lift `C(κ) → W(κ^perf)`, and the identification of Witt multiplication in characteristic `p`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- The weighted polynomial space on `W₂(L)ⁿ` for a prime `p`: it is finite-dimensional,
translation-stable, stable under every weight-polynomial `act q`, and separating. -/
theorem eHighWitt_W2_polyFun {L Q : Type} [Field L] {p : ℕ} [Fact p.Prime] (n : ℕ)
    (act : Q → (Fin n → eHighWitt_W2 L p) → (Fin n → eHighWitt_W2 L p))
    (hact : ∀ q : Q, eHighWitt_IsWeightPoly (eHighWitt_wt p n) eHighWitt_coord (act q)) :
    ∃ V : Submodule L ((Fin n → eHighWitt_W2 L p) → L), FiniteDimensional L V ∧
      (∀ m : Fin n → eHighWitt_W2 L p, ∀ f ∈ V, (fun x => f (x + m)) ∈ V) ∧
      (∀ q : Q, ∀ f ∈ V, (fun x => f (act q x)) ∈ V) ∧
      (∀ m : Fin n → eHighWitt_W2 L p, m ≠ 0 → ∃ f ∈ V, f m ≠ f 0) := by
  have hw : ∀ v, eHighWitt_wt p n v ≠ 0 := by
    intro v
    cases v with
    | inl _ => exact Nat.one_ne_zero
    | inr _ => exact (Fact.out : p.Prime).ne_zero
  have hwd : ∀ v, eHighWitt_wt p n v ≤ p := by
    intro v
    cases v with
    | inl _ => exact (Fact.out : p.Prime).one_lt.le
    | inr _ => exact le_refl p
  exact eHighWitt_exists_polyFun_of_weightPoly (eHighWitt_wt p n) hw p hwd eHighWitt_coord
    eHighWitt_coord_injective act (fun m => eHighWitt_trans_isWeightPoly m) hact

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2_polyFun

/-- **Gap (bh-met-87c).**  `M` embeds additively and `Q`-equivariantly into `W₂(L)ⁿ`, for a
field `L` of characteristic `p`, with every `q` acting by a weight-polynomial map.  It is true on
paper (see the module docstring).  It is not strictly weaker than
`EHighArtinHassePolyFunStatement`, but it is strictly smaller in proof content. -/
def EHighArtinHasseWittEmbedStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Q : Type) [CommGroup Q], Group.FG Q →
    ∀ (M : Type) [AddCommGroup M] [Module (MonoidAlgebra (ZMod (p ^ 2)) Q) M],
      Module.Finite (MonoidAlgebra (ZMod (p ^ 2)) Q) M →
      ∀ (P : Ideal (MonoidAlgebra (ZMod (p ^ 2)) Q)) (k : ℕ),
        Primary.IsCoprimaryWith (MonoidAlgebra (ZMod (p ^ 2)) Q) M P k →
        ((p : ℕ) : MonoidAlgebra (ZMod (p ^ 2)) Q) ∈ P →
        2 ≤ k → (∃ m : M, p • m ≠ 0) → Infinite M →
      ∃ (L : Type) (_ : Field L), ringChar L = p ∧
        ∃ (n : ℕ) (ι : M →+ (Fin n → eHighWitt_W2 L p))
          (act : Q → (Fin n → eHighWitt_W2 L p) → (Fin n → eHighWitt_W2 L p)),
          Function.Injective ι ∧
          (∀ (q : Q) (m : M), ι (MonoidAlgebra.of (ZMod (p ^ 2)) Q q • m) = act q (ι m)) ∧
          ∀ q : Q, eHighWitt_IsWeightPoly (eHighWitt_wt p n) eHighWitt_coord (act q)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.EHighArtinHasseWittEmbedStatement

/-- **Endpoint (reduction).**  The invariant function-space criterion follows from a
weight-polynomial Witt embedding. -/
theorem eHighArtinHassePolyFun_of_wittEmbed (h : EHighArtinHasseWittEmbedStatement) :
    EHighArtinHassePolyFunStatement := by
  intro p hp Q _ hfg M _ _ hfin P k hM hpP hk hne hinf
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨L, hL, hchar, n, ι, act, hι, hcompat, hact⟩ :=
    h p Q hfg M hfin P k hM hpP hk hne hinf
  obtain ⟨V, hfd, htrans, hactV, hsep⟩ := eHighWitt_W2_polyFun n act hact
  exact ⟨L, hL, hchar, eHighWitt_transport ι hι
    (fun (q : Q) (m : M) => MonoidAlgebra.of (ZMod (p ^ 2)) Q q • m) act hcompat
    V hfd htrans hactV hsep⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighArtinHassePolyFun_of_wittEmbed

end GroupApproximation.BooneHigman.Metabelian.Coprimary
