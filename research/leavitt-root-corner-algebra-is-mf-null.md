---
rg: 2
id: leavitt-root-corner-algebra-is-mf-null
kind: claim
title: The negative-root spectral corner of the binary Leavitt Steinberg group algebra has no unital norm-corona representation
distinct_from:
  agent-leavitt-not-bcs-negative-root-corner: that asks for a unital map from the fixed no-CE BCS algebra into the corner, which by mf-null-corner-criterion-needs-faithful-ce-trace also forces Delta nonhyperlinear; this asks only that the corner itself be MF-null, is implied by that claim, and is not known to force nonhyperlinearity.
  property-t-free-leavitt-full-mf-radical: that is the full collapse Rad_MF(Delta)=Delta; this is a statement about one corner algebra, which implies the collapse by the MF-null corner criterion and normal generation.
---

**OPEN.**

**Setting.**
- `R = L_(F_2)(1,2)` and `Delta = St_20(R)`.
- `z = x_13(q)` with `q = s_1 t_1`, and `P_z = (1 - z)/2` in `C[Delta]`.

**Statement.** The unital star algebra `P_z C[Delta] P_z` is MF-null: it has no unital star homomorphism into any norm
matrix corona `Q_k`.

**Why it matters.**
- By `mf-null-corner-criterion-needs-faithful-ce-trace` (A), this gives `z in Rad_MF(Delta)`.
- `full-leavitt-idempotent-defect-saturation` then gives `Rad_MF(Delta) = Delta` without Property `(T)`.
- It is implied by `agent-leavitt-not-bcs-negative-root-corner` together with the no-CE property of `A(B_loop)`.

**Why it is not the same hole.**
- If `Delta` is hyperlinear, the corner carries a faithful CE trace.
- By the stripping part (C) of `mf-null-corner-criterion-needs-faithful-ce-trace`, no proof of this claim can then pass
  through a CE-null algebra in any nonzero corner.
- So the no-CE-corner family can prove this claim only by also proving `non-hyperlinear-group`.
- Any other proof must be an operator-norm-only rigidity: a finite set of corner elements whose star relations have no
  approximate norm solutions in matrices.
- K-zero rank arithmetic cannot supply that rigidity (`corona-k0-positive-arithmetic-is-real-lp-feasibility`).

**Finite form of a target.** Find a finite set `F` of elements `P_z g P_z`, with `g` in `Delta`, together with finitely
many star relations that hold among them in `C[Delta]`. The relations must have no approximate norm solution in any
matrix algebra, and the reason must not use `(T)`.

## Attempts

- **No-CE corner certificate (swarm-0917-w10-w10-ptm-pull, 2026-09-18). Dead as a class** for hyperlinear `Delta`, by
  part (C) of `mf-null-corner-criterion-needs-faithful-ce-trace`. Such a certificate forces `non-hyperlinear-group`.
- **Krein induction of the algebraic corner (swarm-0917-w20-w20-ptl-break, 2026-09-20). Reformulation plus two class
  obstructions; the hole stays OPEN.** See `root-corner-star-reps-are-definite-krein-modules` (ESTABLISHED, written
  proof).
  - **Reformulation.** A unital star map `P_z C[Delta] P_z -> Q_k` is exactly a `Delta`-module over `Q_k` with an
    invariant, possibly indefinite, `Q_k`-valued hermitian form whose `z`-odd part is free of rank one and positive.
    This hole is therefore the conjunction of two statements:
    - (R+): no unitary Hilbert-`Q_k`-module representation with a rank-one free odd part;
    - (R-): no indefinite one.
  - **Unitary rigidity only reaches part of (R+).** The Property (T) theorem proves (R+) only for finitely generated
    projective modules. It says nothing about countably generated modules or about (R-).
  - **Correction.** So this hole is not known to follow from (T), and the sentence "This is the role Property (T)
    plays" in the criterion node is a heuristic.
  - **Class obstruction: unitarize first.** Positivity `rho(P x* Q x P) >= 0` fails for general involution corners.
    For example, for `D_inf` the corner is `C[T]` and `T -> t` with `|t| > 1` is non-positive.
  - **Class obstruction: finite models.** `P_z C[Delta] P_z` has no nonzero finite-dimensional representation, star
    or not. The proof is a finite-codimension fixed space in the induced module together with Malcev and simplicity.
    So no exact finite model can refute or witness the hole.
  - **What a proof must do.** A Kazhdan-free proof must control indefinite asymptotic representations of `Delta`.
    (Withdrawn by the next entry.)
- **Calibration of the Krein split (swarm-0917-w21-w21-ptl-follow, 2026-09-20). The split is not a decomposition, and
  the hole stays OPEN as a T-free statement.** See `krein-corner-modules-unitarize-on-the-root-centralizer`
  (ESTABLISHED, written proof).
  - **Odd-part unitarization.** In every definite-corner Krein module over any unital C*-algebra, of any signature,
    `C_Delta(z)` preserves the rank-one odd line `xi D` and acts on it by a unitary representation
    `u(h) = rho(P_z h P_z)` with `u(z) = -1`. This is Step 1 of `leavitt-mf-null-root-corner-is-equivalent-to-the-goal-proof`,
    written on modules.
  - **Consequence via (T).** `M_18`, a copy of `Delta` inside `C_Delta(z)`, is killed by `Rad_MF(Delta) = Delta`, and
    the Steinberg commutator chain then kills `z`. So (R+), including countably generated modules, and (R-) both hold
    via (T). The earlier entry's "not known to follow from (T)" is false, and the equivalence node's "Property (T)
    corollary" stands: the Statement above, which has no T-free clause, is a theorem.
  - **Class obstruction withdrawn.** "Unitarize first" does not die at positivity. A complete proof in that class
    unitarizes only on the centralizer, where it is automatic. The `D_inf` witness has centralizer `<z>`.
  - **What a proof must do.** (R+) and (R-) both follow from the single unitary statement `z in Rad_MF(C_Delta(z))`,
    which is T-freely equivalent to the goal. So the T-free content of this hole is exactly the goal, and no control of
    indefinite representations is needed.
