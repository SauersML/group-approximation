---
rg: 2
id: fix-boone-higman-linear-char-zero-b-tri-domain-type
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.BTri.DomainType: automatically included section variable(s) unused in theorem GroupAppr"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainType.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: fix-bh-b (reassigned 09-19 by the coordinator; the file was fix-bh-a's).

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainType.lean:45:8: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.BTri.coe_pU`:
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainType.lean:54:8: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.BTri.coe_unitsMap`:
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainType.lean:147:2: Tactic `simp` failed with a nested error:
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainType.lean:149:14: 'GroupApproximation.BooneHigmanLinear.BTri.pval_mul' depends on axioms outside the classical allowlist: [sorryAx]
```

**Repair landed, unprobed.** fix-bh-b's commit that edits this node also fixes the file. It makes six fixes and changes no statement:
- `omit [IsDomain A] in` for coe_pU and coe_unitsMap. With IsDomain included, coe_pU could not fire in the IsDomain-free Lattices section, which is why the simp in smul_latOf reported it as unused.
- pval_mul: `exact mul_mul_mul_comm _ _ _ _` replaces the AC `simp only [mul_comm, mul_left_comm, mul_assoc]`, which hit the heartbeat limit.
- latOf_le_of_eq_mul: a `show` beta-reduces the goal `(fun j i => h i j) j` before `rw [hcol]`.
- exists_eq_mul_of_latOf_le: `Pi.smul_apply` and `Algebra.smul_def` run as two separate simps. Together, `Algebra.smul_def` fired first at the function level, which left `ring` with a stuck Pi application.
- smul_latOf: `ext v i` picked `LinearMap.pi_ext'`, which produced single-component goals. It is now `LinearMap.ext fun v => funext fun i => _`, with the scalar side rewritten explicitly (`map_pow (algebraMap A B)`) so that `map_pow` no longer splits `Matrix.scalar`.
- `section Type` is renamed `section VertexType`, because `Type` is a keyword and both `section Type` and `end Type` failed to parse.

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.BTri.DomainType` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
