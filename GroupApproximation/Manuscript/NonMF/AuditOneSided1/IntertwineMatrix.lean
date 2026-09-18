import GroupApproximation.Leavitt.OneSidedCompressor
import GroupApproximation.Meta.AxiomGuard

/-!
# The intertwining identity, entry by entry

`non_mf_groups_exist.tex`, proof of Lemma `lem:ring-compression-cell`, lines 903--908:

> \[ u\,e_{ij}(a)=e_{ij}(sat)\,u: \]
> both sides differ from $u$ by one entry, $sa$ in position $(i,j)$, since on the
> right the increment $sat\cdot(s,\ldots,et^{j-1})$ from row $j$ of $u$ contributes
> $sa\,ts=sa$ in position $(i,j)$ and $sa\,te\,t^{j-1}=0$ in position $(i,4)$.

The endpoint states the whole claim for `1 ≤ i ≠ j ≤ 3` (the core indices
`coreIdx i`, `coreIdx j` of `EL₄(R)`) and every `a ∈ R`:
* the matrix of `u e_ij(a)` is `u + E_ij(sa)`;
* the matrix of `e_ij(sat) u` is `u + E_ij(sa)`;
* the two contributions of the right-hand increment, `sa·ts = sa` and
  `sa·te·t^k = 0`.

Proof route.
* The matrix identities are checked entry by entry over the explicit matrix
  `compressorMatrix` of `u` (`compressor_val`). The script is the one used for
  `OneSidedCompressor.compressor_mul_coreRoot`.
* The two scalar contributions are `ts = 1` and `te = 0`.
-/

namespace GroupApproximation.Manuscript.NonMF.AuditOneSided1

open GroupApproximation.OneSidedCompressor

variable {R : Type*} [Ring R]

/-- tex 903--908: for `1 ≤ i ≠ j ≤ 3` and `a ∈ R`, the matrices of both sides
of `u e_ij(a) = e_ij(sat) u` equal `u + E_ij(sa)`. The right-hand increment
contributes `sa·ts = sa` at `(i,j)` and `sa·te·t^k = 0` at `(i,4)`. -/
theorem manuscriptSentence_intertwineOneEntry (P : OneSidedInverse R)
    (i j : Fin 3) (hij : i ≠ j) (a : R) :
    ((((compressor P *
          elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a :
          elementaryGroup (Fin 4) R) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
          Matrix (Fin 4) (Fin 4) R) =
        compressorMatrix P + Matrix.single (coreIdx i) (coreIdx j) (P.s * a) ∧
      ((((elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij)
            (P.s * a * P.t) * compressor P :
          elementaryGroup (Fin 4) R) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
          Matrix (Fin 4) (Fin 4) R) =
        compressorMatrix P + Matrix.single (coreIdx i) (coreIdx j) (P.s * a)) ∧
      P.s * a * (P.t * P.s) = P.s * a ∧
      ∀ k : ℕ, P.s * a * (P.t * P.e * P.t ^ k) = 0 := by
  refine ⟨?_, ?_, by rw [P.t_mul_s, mul_one],
    fun k => by rw [P.t_mul_e, zero_mul, mul_zero]⟩
  all_goals
    ext r c
    fin_cases i <;> fin_cases j
    all_goals try simp at hij
    all_goals fin_cases r <;> fin_cases c
    all_goals
      simp [elementaryRoot, elementaryUnit, compressorMatrix, Matrix.mul_apply,
        Matrix.one_apply, Fin.sum_univ_succ, coreIdx, P.t_mul_s, mul_assoc]

#audit_axioms manuscriptSentence_intertwineOneEntry

end GroupApproximation.Manuscript.NonMF.AuditOneSided1
