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
