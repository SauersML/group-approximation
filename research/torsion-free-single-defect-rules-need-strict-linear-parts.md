---
rg: 2
id: torsion-free-single-defect-rules-need-strict-linear-parts
kind: claim
title: Over a torsion-free group an affine rule with one moved entry on at least three symbols is injective only if its linear part is already a strict linear automaton
distinct_from:
  affine-plus-defect-rule-is-injective-on-some-group: that asks for one injective single-defect affine rule over any group; this shows that on torsion-free groups such a rule yields nothing beyond a linear strict automaton, so a nonlinear answer there needs torsion.
  constant-background-kills-unit-linear-defect-rules: that uses a constant background and fails when a memory translate hides in M ∪ N^-1; this chooses the background by a capacity matching controlled by Kemperman's inequality, has no exceptional translates, and needs no finite inverse support.
  avoidable-patches-of-affine-rules-inherit-linear-injectivity: that transfers injectivity to the linear part; this adds non-surjectivity of the linear part on torsion-free groups.
artifacts:
  - experiments/single-defect-kemperman-2026-09-17/witness_window.py
  - experiments/single-defect-kemperman-2026-09-17/output.txt
---

**ESTABLISHED 2026-09-19** by `torsion-free-single-defect-rules-need-strict-linear-parts-proof`.

**Theorem.** Let `G` be a torsion-free group, let `q >= 3`, and let `M ⊂ G` be finite and nonempty.
Consider the rule

```text
mu(x) = sum_(m in M) c_m x_m + c + t [ x|_M = p ],     c_m, t in F_q^*,  c in F_q,  p in F_q^M.
```

Write `L = sum_m c_m m` for its linear part, acting by `(Lx)(g) = sum_m c_m x(gm)`. If the
automaton of `mu` on `F_q^G` is injective, then the linear automaton `L` is injective and not
surjective. So `G` already carries a linear strict automaton over `F_q`.

**(b) Arbitrary groups.** The same conclusion holds for any group `G` when two conditions hold.
- `q >= 2|M| + 1`.
- `M` has trivial left stabiliser: no `g != e` has `gM = M`. Equivalently, `M` is not a union of right
  cosets of a nontrivial finite subgroup.

**Consequence.** On a torsion-free group, the architecture `affine-plus-defect-rule-is-injective-on-some-group`
never gives more than a linear counterexample to Gottschalk. The unit case, which that node singles out
as its only nonlinear branch, is empty. This holds whatever the units of `F_q[G]` are.

- **Invariant.** The obstruction is Kemperman's doubling `|Gamma M \ M| >= |Gamma|`
  (`kemperman-torsion-free-product-sets-grow`).
- **Where it dies.** It dies at the step that looks for a background around a correction witness. Every
  unit-linear rule on a torsion-free host admits a one-defect correction witness `x, x + t L^-1 delta_e`.
- **Why `q >= 3`.** Each free coordinate must dodge two forbidden values per translate it serves, and
  `q - 1 >= 2` is exactly the Hall capacity that Kemperman's bound pays for.

**Boundary.** The proof uses torsion-freeness only through Kemperman's inequality, and uses `q >= 3` twice:
in the avoidable-patch lemma and in the matching capacity. A nonlinear injective single-defect rule
therefore needs one of three things.
- A host with torsion and a small field, `3 <= q <= 2|M|`, where finite subgroups keep
  `|Gamma M \ M|` below `2|Gamma|/(q-1)`.
- A memory that is a union of right cosets of a nontrivial finite subgroup. Then a translate `gM = M` can carry an
  event that no background avoids (see the sanity check).
- The alphabet `F_2`.

**Sanity check.** `witness_window.py` checks Steps 4-5 of the proof on finite windows.
- On `Z^2` with `q = 3`, it solves the capacity matching for 200 random memories, patterns and fields `w`.
- On `Z/2 x Z`, with `M` a coset of the torsion subgroup, it exhibits the unavoidable event.
- On `Z/3 x Z/3 x Z`, with `q = 2|M| + 1` and `M` of trivial stabiliser, it checks part (b) on 200 windows.

**Relation to the unit conjecture.** Where the unit conjecture holds for `F_q[G]`, a unit linear part is a
monomial, `|M| = 1`, and the conclusion is elementary. The theorem is new content exactly on torsion-free
groups with nontrivial units in `F_q[G]`, `q >= 3`, for example unit-conjecture counterexamples of Gardam
type in odd characteristic. This note uses no claim about which such groups exist. The proof never looks at
the unit, so it covers every one of them at once.
