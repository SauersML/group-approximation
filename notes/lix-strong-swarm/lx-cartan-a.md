# lx-cartan-a — signed slot permutations of the flat tensor power, the riffle, the block rotation

Owns `CharClass/OddPShuffle*`, `CharClass/OddPWDiagonal*`.  Clone lix-f.  Consumers: lx-cartan-b, lx-prodeval,
lx-compbreal (and lx-cartanvanish for σ_r).

## Design (agreed with lx-cartan-b, 2026-09-12 ~10:15)
ONE generic operator instead of a hand-built riffle: `tupPermAll K X r π` sends `single t` to
`(−1)^{permExp X π t} • single (t ∘ π)`, where `permExp X π t = Σ_{i<j, π j < π i} |t (π i)|·|t (π j)|`, summed over
the new positions whose sources are reordered.  Slot `i` of the new tuple holds old slot `π i`.  Convention:
`tupPermAll π * tupPermAll ρ = tupPermAll (ρ * π)`.  σ_r (t ↦ t ∘ π⁻¹) = `tupPermAll K X p (π⁻¹)`.

## GREEN (probe tags)
* **Probe 0912-110111-36369 (lix-f, acn112 slot 2, base b9399390e): PROBE GREEN, `BUILT
  GroupApproximation.CharClass.OddPShuffle`, 2164 jobs, no errors; every `#audit_axioms` line (tupPermAll_mul_tupDAll,
  tupPermAll_mul, tupTAll_eq_tupPermAll, tupPerm_tupD, tupRiffleAll_conj, tupRiffle_conj) passed the allowlist
  `[propext, Classical.choice, Quot.sound]`.**  Green record `lanes/lx-cartan-a.green.0912-110111-36369`; the bytes equal
  main at fd4a04e29 (landed with the Unverified label, bytes unchanged since, so a normal re-land is NOTHING TO LAND).
* Probe 0912-104044-26988 (lix-f, SLURM, base 0f7748100): everything elaborated except the spots below.
  `#audit_axioms` printed `[propext, Classical.choice, Quot.sound]` for `tupPermAll_mul_tupDAll`, `tupPermAll_mul`,
  `tupTAll_eq_tupPermAll`, `tupPerm_tupD`.  Not yet a green record: the probe failed on five errors (two unused
  binders in `permExp_one`, deprecated `Fin.lt_iff_val_lt_val`, omega in `blockRotEquiv.left_inv` and in
  `blockRotEquiv_mul_riffleEquiv`, where an `if` inside a condition hid the case facts); `tupRiffleAll_conj` and
  `tupRiffle_conj` carried `sorryAx` only by cascade from those.  All five fixed.

## AUTHORED, UNVERIFIED (on main)
* `CharClass/OddPShuffle.lean`: landed 5efa444bb (probe-1 bytes), re-landed with the five fixes (see landed.log).
  Declarations:
  * tuples: `permTup`, `permTup_apply`, `permTup_mul` (rfl), `permTup_one`, `permTup_update`, `tupPre_eq_sum_ite`,
    `tupPre_permTup`, `tupPre_perm_apply`, `perm_pre_pointwise`, `tupPre_perm_add`;
  * exponent: `sum_sum_ite_eq_left/_right`, `finRotate_val_eq_ite`, `permExp`, `permExp_one`, `permExp_update`,
    `permExp_mul` (ℕ cocycle with correction `2·Σ[i<j ∧ πj<πi ∧ ρπi<ρπj]`), `finRotate_reorders_iff`,
    `finRotate_castSucc_eq`, `permExp_finRotate_succ`, `rotExp_succ`, `rotExp_eq_permExp`;
  * full model: `tupPermAll`, `tupPermAll_single`, `tupPerm_sign`, `tupPermAll_tupDAll_single`,
    `tupPermAll_mul_tupDAll` (P1), `tupPermAll_mul` (P2), `tupPermAll_one`, `tupTAll_eq_tupPermAll` (P3);
  * degree k (P4): `permTup_tot`, `permTupIdx`, `permTupIdx_val`, `tupPerm`, `tupPerm_single`, `tupIncl_comp_tupPerm`,
    `tupPerm_tupD`, `tupPerm_mul`, `tupT_eq_tupPerm`;
  * instances: `riffleSrc/riffleTgt`, `riffleEquiv`, `riffleEquiv_val`, `blockRotSrc/blockRotTgt`, `blockRotEquiv`,
    `blockRotEquiv_val`, `blockRotEquiv_mul_riffleEquiv`, `tupRiffleAll`, `tupBlockRotAll`,
    `tupRiffleAll_mul_tupDAll`, `tupBlockRotAll_mul_tupDAll`, `tupRiffleAll_conj : R * B = tupTAll ^ 2 * R`,
    `tupRiffle`, `tupBlockRot`, `tupIncl_comp_tupRiffle`, `tupIncl_comp_tupBlockRot`, `tupRiffle_tupD`,
    `tupBlockRot_tupD`, `tupRiffle_conj`.

## NEEDS
* None.

## SPLIT (independent sub-tasks a helper could author; none is on my critical path)
* `CharClass/OddPShuffleSign.lean` (if a consumer needs the explicit riffle sign): `permExp_riffleEquiv (m) (t) :
  permExp X (riffleEquiv m) t = ∑ j : Fin m, |t (m+j)| · ∑ l with j < l < m, |t l|`, by the pointwise reorder test
  `i < i' ∧ riffleSrc i' < riffleSrc i ↔ (i odd, i' even, i/2 < i'/2)`.  Inputs: OddPShuffle.
* TAKEN by lx-redpow (coordinator, 09-12 ~11:10; lx-redpow owns the file, names checked clash-free against OddPShuffle
  at e0d8365e0; OddPShuffle will not add `tupPermAll_pow`, `tupPerm_one`, `tupPerm_pow`, `mulPerm*`, `finRotate_pow*`).
  `CharClass/OddPShufflePrimRoot.lean` (lx-cartanvanish's σ_r): `mulPerm (p r) (hr : Nat.Coprime r p) :
  Equiv.Perm (Fin p)`, `i ↦ r·i mod p`, and `finRotate p * mulPerm p r hr = mulPerm p r hr * finRotate p ^ r`
  (or the inverse form), then `tupTAll ^ r * tupPermAll (mulPerm ..) = tupPermAll (mulPerm ..) * tupTAll` from P2/P3.
  Inputs: OddPShuffle.

## TRAPS
* An `if` whose condition contains another `if` defeats `split_ifs <;> omega` (omega reads the hypothesis as an atom):
  `generalize` the inner value first, `split_ifs at` the naming hypothesis, then split the goal.
* `Fin.lt_iff_val_lt_val` is deprecated at the pin (`Fin.lt_def`), a hard error under warningAsError.
* `rw [if_neg (by omega)]` elaborates the tactic block against a metavariable condition; write `show ¬ … by omega`.
