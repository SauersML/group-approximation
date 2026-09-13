---
rg: 2
id: unit-case-two-patch-collisions-from-peelable-windows
kind: claim
title: In the unit case the class II seed collides whenever the window hypergraph of the inverse support can be deleted
distinct_from:
  unit-case-pair-distinct-two-patch-rules-are-not-injective: that is the full unit-case claim for class II; this proves a collision only when a finite window hypergraph can be deleted, and leaves 2-cores open.
  constant-background-kills-unit-linear-defect-rules: that uses a constant background and a single defect entry; this has two patches using every symbol and fixes the background site by site.
  pair-distinct-ternary-rules-pre-injective-on-free-memory: that excludes finite collisions over free memory, where no inverse exists; this builds finite collisions from a right inverse.
artifacts:
  - research/artifacts/pair-distinct-two-patch-unit-case-2026-09-12.md
---

**OPEN.** There is a candidate proof on paper, with no verdict yet. Verification was requested from
w7-vf-nonlinear. The `-proof` route will be added once an independent re-derivation passes.

**Setting.** Let `H = <a, b>` with `1, a, b` distinct, and `M = {1, a, b}`. The seed is

```text
mu'(y) = y_1 + y_a - y_b + [y = (0,1,0)] - [y = (1,2,2)]      over F_3,
tau(x)(g) = mu'(x(g), x(ga), x(gb)).
```

Suppose `1 + a - b` has a right inverse `w` in `F_3[H]` with support `N`.

**Claim.**
- **The hypergraph.** Its vertices are the sites outside `M`, with one edge `hM \ M` for each `h` in
  `W = (MN)^-1 \ {1}`.
- **Deletion.** Delete edges repeatedly, either by an unused vertex lying in no other remaining edge, or by an
  unused vertex outside `N^-1`.
- **Conclusion.** If every edge can be deleted, `tau` has two configurations differing on `N^-1` with the same
  image. So `tau` is not injective.

**Consequence.** If the seed is injective over `H`, then `W` contains a nonempty 2-core `C`: every site of
`CM \ M` lies in at least two windows of `C`. Such a pair `(C, M)` has unique products only inside `M`, so `H` is
not a unique-product group.

**Proof sketch** (artifact §§1–2).
- **Witness.** `d = -K delta_1` satisfies `L d = -delta_1`. Put `x'|_M = p` and `x = x' - d`.
- **Windows.** Windows missing `N^-1` agree in both configurations.
- **One site fixes its window.** At most one value is bad in each configuration, because `p` and `q` differ at
  every address.
- **Free breakers.** A site outside `N^-1` breaks its window permanently with the symbol neither patch uses.
- **Order.** Resetting sites in reverse deletion order fixes every window.

**Calibration.** Hand collisions on Z/4 and Z/5 test the conventions (artifact §3). They do not test the
deletion step, since finite groups carry 2-cores.

## Attempts

- **Constant background** (Proposition 5, `distinct-symbol-patch-collision-2026-09-12.md`). It leaves every
  window meeting `M ∪ N^-1` at one address. That is superseded by the site-by-site background here.
- **Local lemma.** A random background has failure probability up to `4/27` per window, with dependency degree
  `6`. The Shearer bound needs about `0.067`, so it fails.
- **Where it stops.** It is not known whether a right inverse can have `W` with a 2-core resisting deletion.
  The `q`-witness and multi-defect targets are unused. The other 29 class II rules are not treated.
