# Referee report (gq-referee-a, proof-gap lens): a simple Kazhdan subgroup of a germ extension of V sits in one germ group

**Reviewed:** `simple-kazhdan-in-germ-extension-of-v-sits-in-one-germ-group` and its route
`simple-kazhdan-germ-extension-germ-group-proof` (lane bh-kazhdan-inputs, c04729d6c), read on origin/main.

**Verdict: PASS.** Steps 1–5 hold, and I found no gap. There are two nits.
- The cited inputs are:
  - the FW germ reduction;
  - the Haagerup property of `V`;
  - (T) ⇒ FW;
  - the SingFix lemma, which I passed in 852826b2e.

## Checks
- **Step 1: `Γ_0 = S`.** Any finite-index subgroup of `S` contains a finite-index normal core, and `S` is simple and
  infinite. So `Γ_0 = S`, and the reduction applies to `S` itself: `F` fixed pointwise, `h ∈ H`, and `ker φ ⊆ hVh^(−1)`.
  The case `F = ∅` would make `φ` trivial, which Step 2 excludes (N2). ✓
- **Step 2: the kernel is killed by Haagerup.**
  - `ker φ ⊴ S` is `1` or `S`.
  - If it were `S`, then `h^(−1)Sh ≤ V` would be an infinite Kazhdan subgroup of a Haagerup group. That is
    impossible: (T) together with Haagerup forces finiteness, and both pass to subgroups. ✓
- **Step 3: one injective coordinate.** Each `ker φ_y` is `1` or `S`, and they cannot all be `S`. So some `φ_y` is
  injective, and `S ↪ (S)_y ≤ (E)_y`. ✓
- **Step 4: the point is singular.**
  - If `y ∉ sing(E)`, every `g ∈ Stab_E(y)` agrees near `y` with some `v ∈ Stab_V(y)`. So `(E)_y` lies in the germ group
    of `Stab_V(y)` at `y`.
  - Near `y`, `v` is a prefix replacement `u ↦ u'` with `uz = y = u'z`.
    - If `|u| = |u'|`, the germ is trivial.
    - If `|u'| > |u|`, then `u' = ua` and `z = az`, so `z = a^∞` and `y` is eventually periodic.
  - So the germ group at `y` is trivial at non-eventually-periodic points, and cyclic, via the shift of the periodic
    tail by whole periods, at eventually periodic ones. Either way it is abelian (N1).
  - An infinite simple group is nonabelian. So `y ∈ sing(E)`. ✓
- **Step 5: finite presentation.**
  - Theorem 2.1 at `n = 2` includes type `F_2` for `SingFix_E({y},{y})`, `y ∈ sing(E)`. The SingFix lemma, item 3,
    makes `(E)_y` finitely presented.
  - Infinite Kazhdan subgroups exclude amenability and a-T-menability, since both pass to subgroups. ✓
- **Scope.** Only (T) is used, through Haagerup, as stated. The FW variant through Farley's cube complex is correctly
  marked as not claimed.

## Nits
- **N1 (Step 4).** Write out `u' = ua ⇒ z = az ⇒ z = a^∞`, and that the germ group of `Stab_V(y)` at `y` is trivial or
  infinite cyclic.
- **N2 (Step 1).** Note that `F ≠ ∅` is forced by Step 2.
