# lx-additive — additivity and linearity of the reduced powers P^i (R9)

Lane of the LIX STRONGEST swarm (lead nonsofic-existence-39).  Clone spare1 (shared with lx-toppower).
Owns `CharClass/OddPAdditive*`, `OddPRotate*`, `OddPEval*`.

## Plan (lemma list, route settled before authoring)

Notation: `p` odd prime, `u, v ∈ C^q(X; F_p)` cocycles, `a := Pi.single q u`, `b := Pi.single q v` (graded),
`x = e_j ⊗ σ` the source generator of W-index `j`, simplex degree `pq − j`, `Δ = oddDiagApp p X (pq)`.

1. `OddPRotate` (tuple level, no diagonal):
   * rotated E5 `tupEval_tupT_rotate`: slot-concentrated φ (every slot in degree q), odd arity r:
     `tupEval φ (tupT x) = tupEval (φ ∘ (finRotate r).symm) x`.  On a basis tuple
     `tupT single t = (−1)^{rotExp} single (t ∘ finRotate r)`, the product reindexes by `Equiv.prod_comp`,
     and on the support every slot has degree q so `rotExp = q·(r−1)q` is even.  (No model test needed: the
     direction is forced by `tupRot t = t ∘ finRotate r`.)
   * iterate `tupEval_tupT_pow_rotate`: `tupEval φ (tupT^i x) = tupEval (φ ∘ ((finRotate r).symm ^ i)) x`.
   * expansion `tupEval_add_expand`: `tupEval (fun _ => a + b) x = Σ_{ε : Fin r → Bool} tupEval (slots ε) x`,
     `slots ε l := if ε l then a else b` (`Finset.prod_univ_sum` / `Fintype.prod_sum`, `Fintype.sum_bool`).
2. `OddPAdditiveWeight` (pure combinatorics, avoids orbit representatives):
   for non-constant ε, `c(ε) = #{l | ε l}` is a unit mod p, `w(ε) := if ε 0 then c(ε)⁻¹ else 0`, and
   `Σ_{i<p} w(ε ∘ (finRotate p)^i) = c(ε)⁻¹ · #{i | ε (i)} = 1`.  Hence for any `F`,
   `Σ_{ε mixed} F ε = Σ_{ε mixed} w ε • Σ_{i<p} F (ε ∘ ((finRotate p).symm)^i)`.
3. `OddPEvalDiag` (bridge, shared with lx-diag's R2): `oddEvalHom`, rotation through Δ5 + (1),
   `oddEvalHom_oddDiff_eq_zero` (Δ1 + E4'), simplicial-half bridge = δ of a cochain.
4. `OddPAdditive`: `Σ_{i<p} Δ(g^i • x) = Δ(N • x)`; `c_j • altCoeff j = N` with `c_j = grS^{p−2}` (j even) or
   `1` (j odd); `N • x = oddDiff (c_j • y) − c_j • S(σ)`, `y = e_{j+1} ⊗ σ`; so
   `oddD(u+v) = oddD u + oddD v + δΨ` with `Ψ(τ) = −(−1)^{j+1} Σ_{ε mixed} w ε · oddEvalHom (slots ε) (c_j • e_{j+1} ⊗ τ)`;
   then `redPow_add` by `redPow_mk`, `cocycleClassK_add`, `cocycleClassK_coboundary_zero`, `cohCast_add`;
   `redPow_smul` from `c^p = c`.

## GREEN
* `CharClass/OddPRotate` — probe 0912-102321-27045 (spare1 via SLURM acn74, base f29a035ec), BUILT, PROBE GREEN,
  2166 jobs; `tupEval_add_expand` depends on `[propext, Classical.choice, Quot.sound]`.  Landed 6c003072f
  (bytes identical to the compiled record).  Declarations: `tupEval_tupT_rotate`, `tupEval_tupT_pow_rotate`,
  `tupEval_add_expand`, `bif_concentrated`, `bif_comp`.

  Re-probe 0912-104508-45607 (acn112 slot 0): `OddPRotate` BUILT again with `tupEval_smul_const` added.

## AUTHORED, UNVERIFIED (landed)
* `CharClass/OddPAdditiveWeight` — `trueCount`, `mixedWeight`, `trueCount_comp`, `trueCount_ne_zero`,
  `finRotate_pow_apply_zero`, `sum_mixedWeight_rotate(_ite)`, `sum_weighted_rotate_eq_mixed`, `sum_eq_mixed_add_const`.
  First probe 0912-104508-45607 red only on two unused `[NeZero p]` binders, `Bool.true_ne_false`, missing AxiomGuard
  import (all fixed; the rest of the file elaborated).
* `CharClass/OddPAdditive` — `oddDiagApp_grGen_pow`, `oddEvalHom_grGen_pow`, `oddEvalHom_grNorm_smul`, `normCofactor`,
  `normCofactor_mul_altCoeff`, `oddDiff_castSucc_single`, `grNorm_smul_single`, `oddEvalHom_grNorm_smul_single`,
  `oddCochainCoboundary_add`, `oddEvalCochain(_eval)`, `slotsOf`, `gCoboundary_slotsOf`, `mixedPrimitive`,
  `oddEvalCochain_add_succ`, `oddEvalCochain_add_zero`, `oddEvalCochain_class_add`, `oddEvalCochain_smul`,
  `oddD_eq_oddEvalCochain`, `oddD_class_add`, `oddD_class_smul`, **`redPow_add`**, **`redPow_smul`**, **`redPowLin`**,
  `redPowLin_apply`, `redPow_zero`, `redPow_neg`.  Imports lx-diag's `OddPCochain`/`OddPCochainSum` and lx-redpow's
  `OddPRedPow`.  Probe waits for lx-diag's `OddPDiagonalSrc` fix (its closure).

## SPLIT
* none: R9 is fully authored; what remains is compile repair after lx-diag's diagonal is green.

## NEEDS
* lx-diag: `OddPDiagonalSrc` → `OddPDiagonal` → `OddPCochain` → `OddPCochainSum` compiled (probe group waits on it).

## TRAPS
(none yet)
