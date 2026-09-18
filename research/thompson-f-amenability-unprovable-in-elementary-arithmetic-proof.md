---
rg: 2
id: thompson-f-amenability-unprovable-in-elementary-arithmetic-proof
kind: route
title: Absorb the Π1 axioms into the search, extract an elementary witness bound from the proof, and contradict Moore's tower
target: thompson-f-amenability-unprovable-in-elementary-arithmetic
requires:
  - thompson-f-folner-function-exceeds-every-tower
  - ea-provably-recursive-functions-are-kalmar-elementary
---

Notation is as in the target: `R_Γ`, `g_Γ`, `Føl_Γ`, `c >= C`, and `T = IΔ0 + Exp + Th_Π1(N)`.
`exp_0(x) = x` and `exp_(p+1)(x) = 2^(exp_p(x))`.

**Step 0 (R_Γ is elementary).** Represent `g ∈ F` by its reduced tree-pair diagram, coded as
a number. Composition, reduction and equality of tree pairs take time polynomial in the code
length, so the map `(a, γ) ↦ code of A_a γ` and the count `Σ_γ |A_a γ △ A_a|` are polynomial
time in `a`. The comparison with `c^(-n)|A_a|`, done as
`c^n Σ_γ |A_a γ △ A_a| < |A_a|`, uses one exponential. So `R_Γ` is Kalmár elementary, and
`g_Γ = µa R_Γ` is a partial recursive function. It is total iff `F` is amenable, by Følner's
criterion in Moore's form (arXiv:0905.1118v7, §1, quoted with the imported theorem): `F` is
amenable iff every `1/m`-Følner set exists, and `c^(-n) -> 0`.

**Step 1 (if F is not amenable).** Then `Føl_Γ` is false in `N`. Every axiom of `T` is true
in `N`, so `T ⊬ Føl_Γ`.

**Step 2 (absorbing the Π1 axioms).** Assume `F` is amenable and `T ⊢ Føl_Γ`. A proof uses
finitely many true Π1 axioms. Their conjunction is equivalent in `IΔ0` to one true Π1
sentence `π = ∀z δ(z)` with `δ` in Δ0. So `IΔ0 + Exp ⊢ π → g_Γ↓`. Define

```text
R'(n, a)  :⟺  R_Γ(n, a)  ∨  ∃z <= a ¬δ(z),        g'(n) := µa R'(n, a).
```

`R'` is elementary. Argue in `IΔ0 + Exp`:
- if `π`, then `g_Γ(n)` converges to some `a_0` with `R_Γ(n, a_0)`, so the search for `R'`
  stops at or before `a_0`;
- if `¬π`, some `z` has `¬δ(z)`, and the search for `R'` stops at or before `z`.

So `IΔ0 + Exp ⊢ g'↓`. This uses only the routine arithmetization of µ-search over an
elementary predicate. A search with a witness `a_0` has a computation record bounded by an
exp-term in `(n, a_0)`, whose existence follows by Δ0-induction on `a <= a_0`, which is
standard in `IΔ0 + Exp`. Since `δ` holds everywhere in `N`, `R' = R_Γ` on `N`, and `g' = g_Γ`.

**Step 3 (witness extraction).** By `ea-provably-recursive-functions-are-kalmar-elementary`
(Henk–Pakhomov, verbatim: "The provably recursive functions of I∆0+Exp are exactly the Kalmar
elementary functions"), `g_Γ = g'` is Kalmár elementary. By the bounding lemma of the same
node, there is `k` with `g_Γ(n) <= exp_(k+1)(n)` for all `n >= 2`.

**Step 4 (contradiction with Moore).** Let `A_n = A_(g_Γ(n))`. It is a `c^(-n)`-Følner set, hence
`C^(-n)`-Følner since `c >= C`. By `thompson-f-folner-function-exceeds-every-tower` (Moore,
Theorem 1.1, verbatim there), `|A_n| >= exp_n(0)`. The coding gives
`|A_n| <= g_Γ(n) <= exp_(k+1)(n)`.

Now put `j = n - k - 1`. Then `exp_n(0) = exp_(k+1)(exp_j(0))`, and `exp_j(0) >= 2^j` for
`j >= 4` (16 >= 16, and `2^(2^j) >= 2^(j+1)` inductively). For `j` large, `2^j > j + k + 1 = n`.
Since `exp_(k+1)` is strictly increasing, `exp_n(0) > exp_(k+1)(n)` for all large `n`, a
contradiction. So `T ⊬ Føl_Γ`.

**Step 5 (robustness).**
- If `IΔ0 + Exp ⊢ τ → Føl_Γ` and `T ⊢ τ`, then `T ⊢ Føl_Γ`, contradicting Steps 1–4.
- `∀m ∃A (A is 1/m-Følner)` is such a `τ`, instantiating `m = c^n` (Exp gives `c^n`).
- `EA` has the same arithmetic theorems as `IΔ0 + Exp`, by the conservativity quoted in the
  imported node. ∎

**Calibration (the proof uses nothing about F beyond Moore's bound).** Steps 0–3 apply to any
finitely generated group with an elementary Følner predicate. Step 4 needs only a Følner
function that is not elementary-bounded. So the Brieussel–Zheng group `Δ_U` with
`U(n) = exp_n(0)` from `decidable-amenable-groups-have-no-recursive-folner-bound` has a true,
`T`-unprovable Følner sentence. Its word problem is decidable, and elementarity of its
predicate is not needed for Step 3, whose import covers every recursive function. So the
theorem is a statement about proof strength, not evidence of non-amenability.
