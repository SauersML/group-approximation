/-- Conjugation by `Ψ q`, restricted to the translation algebra. -/
def eHighArtinHasse_conjB (act : Q → M → M)
    (hadd : ∀ q x y, act q (x + y) = act q x + act q y)
    (hmul : ∀ q r x, act (q * r) x = act q (act r x)) (hone : ∀ x, act 1 x = x)
    (V : Submodule L (M → L)) (htrans : ∀ m : M, ∀ f ∈ V, (fun x => f (x + m)) ∈ V)
    (hact : ∀ q : Q, ∀ f ∈ V, (fun x => f (act q x)) ∈ V) (q : Q) :
    eHighArtinHasse_alg V htrans →ₐ[L] eHighArtinHasse_alg V htrans :=
  eHighArtinHasse_restr _ (eHighArtinHasse_conj act hmul hone V hact q)
    (eHighArtinHasse_conj_mem act hadd hmul hone V htrans hact q)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighArtinHasse_conjB

theorem eHighArtinHasse_conjB_val (act : Q → M → M)
    (hadd : ∀ q x y, act q (x + y) = act q x + act q y)
    (hmul : ∀ q r x, act (q * r) x = act q (act r x)) (hone : ∀ x, act 1 x = x)
    (V : Submodule L (M → L)) (htrans : ∀ m : M, ∀ f ∈ V, (fun x => f (x + m)) ∈ V)
    (hact : ∀ q : Q, ∀ f ∈ V, (fun x => f (act q x)) ∈ V) (q : Q)
    (b : eHighArtinHasse_alg V htrans) :
    (eHighArtinHasse_conjB act hadd hmul hone V htrans hact q b : Module.End L V) =
      eHighArtinHasse_conj act hmul hone V hact q b :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighArtinHasse_conjB_val

theorem eHighArtinHasse_conjB_mul (act : Q → M → M)
    (hadd : ∀ q x y, act q (x + y) = act q x + act q y)
    (hmul : ∀ q r x, act (q * r) x = act q (act r x)) (hone : ∀ x, act 1 x = x)
    (V : Submodule L (M → L)) (htrans : ∀ m : M, ∀ f ∈ V, (fun x => f (x + m)) ∈ V)
    (hact : ∀ q : Q, ∀ f ∈ V, (fun x => f (act q x)) ∈ V) (q r : Q)
    (b : eHighArtinHasse_alg V htrans) :
    eHighArtinHasse_conjB act hadd hmul hone V htrans hact (q * r) b =
      eHighArtinHasse_conjB act hadd hmul hone V htrans hact q
        (eHighArtinHasse_conjB act hadd hmul hone V htrans hact r b) := by
  apply Subtype.ext
  rw [eHighArtinHasse_conjB_val, eHighArtinHasse_conjB_val, eHighArtinHasse_conjB_val]
  exact eHighArtinHasse_conj_mul act hmul hone V hact q r b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighArtinHasse_conjB_mul

theorem eHighArtinHasse_conjB_one (act : Q → M → M)
    (hadd : ∀ q x y, act q (x + y) = act q x + act q y)
    (hmul : ∀ q r x, act (q * r) x = act q (act r x)) (hone : ∀ x, act 1 x = x)
    (V : Submodule L (M → L)) (htrans : ∀ m : M, ∀ f ∈ V, (fun x => f (x + m)) ∈ V)
    (hact : ∀ q : Q, ∀ f ∈ V, (fun x => f (act q x)) ∈ V)
    (b : eHighArtinHasse_alg V htrans) :
    eHighArtinHasse_conjB act hadd hmul hone V htrans hact 1 b = b := by
  apply Subtype.ext
  rw [eHighArtinHasse_conjB_val]
  exact eHighArtinHasse_conj_one act hmul hone V hact b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighArtinHasse_conjB_one

/-- The action of `Q` on the translation algebra by conjugation. -/
def eHighArtinHasse_sigma (act : Q → M → M)
    (hadd : ∀ q x y, act q (x + y) = act q x + act q y)
    (hmul : ∀ q r x, act (q * r) x = act q (act r x)) (hone : ∀ x, act 1 x = x)
    (V : Submodule L (M → L)) (htrans : ∀ m : M, ∀ f ∈ V, (fun x => f (x + m)) ∈ V)
    (hact : ∀ q : Q, ∀ f ∈ V, (fun x => f (act q x)) ∈ V) :
    Q →* (eHighArtinHasse_alg V htrans ≃ₐ[L] eHighArtinHasse_alg V htrans) where
  toFun q := AlgEquiv.ofAlgHom (eHighArtinHasse_conjB act hadd hmul hone V htrans hact q)
    (eHighArtinHasse_conjB act hadd hmul hone V htrans hact q⁻¹)
    (AlgHom.ext fun b => by
      rw [AlgHom.comp_apply, AlgHom.id_apply, ← eHighArtinHasse_conjB_mul, mul_inv_cancel,
        eHighArtinHasse_conjB_one])
    (AlgHom.ext fun b => by
      rw [AlgHom.comp_apply, AlgHom.id_apply, ← eHighArtinHasse_conjB_mul, inv_mul_cancel,
        eHighArtinHasse_conjB_one])
  map_one' := AlgEquiv.ext fun b =>
    (eHighArtinHasse_conjB_one act hadd hmul hone V htrans hact b).trans (AlgEquiv.one_apply b).symm
  map_mul' q r := AlgEquiv.ext fun b =>
    (eHighArtinHasse_conjB_mul act hadd hmul hone V htrans hact q r b).trans
      (AlgEquiv.mul_apply _ _ b).symm
