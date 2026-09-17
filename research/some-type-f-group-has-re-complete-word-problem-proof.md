---
rg: 2
id: some-type-f-group-has-re-complete-word-problem-proof
kind: route
title: "Proof: the Novikov--Boone chain already runs on the universal function; compose with s-m-n and the type F structure"
target: some-type-f-group-has-re-complete-word-problem
requires:
  - boone-final-group-is-of-type-f
  - boone-final-group-finitely-presented
  - boone-commutator-criterion-for-halting
  - modular-machine-with-noncomputable-halting
---

## 1. The machine is universal, not merely undecidable

Fix `n` (say `n = 0`). Trace the Lean chain behind
[[modular-machine-with-noncomputable-halting]]:

* `Computability.exists_toPartrec_universal_code n` gives a `ToPartrec` code `c`
  with `(c.eval [m]).Dom <-> ((Denumerable.ofNat Nat.Partrec.Code m).eval n).Dom`
  for every `m`: `c` runs the `m`-th partial recursive code on the fixed input `n`.
* `tm0_halting_not_computablePred n` and
  `exists_modularMachine_halting_not_computablePred n` take exactly this `c`,
  compile it through Mathlib's `PartrecToTM2`, `TM2to1`, `TM1to0` into a Post--Turing
  machine, restrict it to its finite support, and read it as a modular machine
  `M = (D.toQuad M_1).toModular`, with configuration map
  `f(m) = encCfg (initQCfg (trInit K'.main (trList [m])))`. The intermediate fact
  `hkey` together with `tm0_eval_dom_iff c [m]` is, for this `M` and `f`,

      M.Halts (f m)  <->  (c.eval [m]).Dom  <->  phi_m(n) halts,

  where `phi_m` is the partial recursive function with code `ofNat m`. (`hkey` is
  proved for the given `c` without using the non-computability hypothesis.)

**Computability of `f` (by inspection, not machine-checked).** `trList [m]` is the
list of binary-digit symbols of `m` with a terminator (`PartrecToTM2.trNat`,
defined by recursion on the binary expansion); `trInit` reverses it and tags it
with the main stack (`TM2to1.trInit`); `initQCfg` places it on the tape with the
default state; `encCfg` reads the two stacks of the resulting configuration as
base-`M.size` numerals through a fixed finite table (`TMData.ofFintype`
numbers the finite alphabet and state set). Each is a primitive recursive
function of `m`, so `f` is computable. (The Lean statements only assert
non-computability *along* `f`; the computability of `f`, needed for any genuine
word-problem statement including Novikov--Boone itself, is this remark.)

## 2. The halting set along `f` is m-complete

Let `A_n = {e : phi_e(n) halts}` and `K = {e : phi_e(e) halts}`, for the numbering
`e -> Denumerable.ofNat Nat.Partrec.Code e`, an acceptable numbering (it has a
universal function, `Nat.Partrec.Code.eval_part`, and s-m-n,
`Nat.Partrec.Code.smn`/`curry`). `K` is r.e.-complete under many-one reductions.
By s-m-n there is a total computable `g` with `phi_{g(e)}(x) = phi_e(e)` for all
`x`; then `e in K <-> g(e) in A_n`. So `K <=_m A_n`, and by Section 1,
`A_n <=_m H_M` via `f`.

## 3. The word problem of `G_M`

Let `G_M` be the final group of `M`. For `(a,b) in N x N` put
`u = x^a y^b` and `t(a,b) = u^{-1} t u` (from `x^{-1} t(a,b) x = t(a+1,b)`,
`y^{-1} t(a,b) y = t(a,b+1)` and `xy = yx`), and

    W(a,b) = k^{-1} t(a,b) k t(a,b)^{-1},

a word over the finite generating set `t, x, y, r_1..r_n, k` depending
computably on `(a,b)`. By [[boone-commutator-criterion-for-halting]]
(`conj_k_finalTw_eq_iff`), `W(a,b) = 1` in `G_M` iff `M.Halts (a,b)`. Hence

    e in K  <->  W(f(g(e))) = 1  in G_M,

and `e -> W(f(g(e)))` is computable: `K <=_m WP(G_M)`.

`G_M` is finitely presented ([[boone-final-group-finitely-presented]]), so its word
problem is r.e. (enumerate all products of conjugates of relators and freely
reduce). An r.e. set to which `K` many-one reduces is r.e.-complete. Changing the
finite generating set changes the word problem only up to computable
substitution, so completeness does not depend on the presentation.

## 4. Type F

By [[boone-final-group-is-of-type-f]], `G_M` has a finite `K(G_M,1)`, so it is of
type `F` and of type `F_m` for every `m`.

## Conclusion

`G_M` is a group of type `F` with r.e.-complete word problem. In particular the
claim `some-type-fm-level-has-no-complete-word-problem` fails at every finite level
`m >= 3`.
