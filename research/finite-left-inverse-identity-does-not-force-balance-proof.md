---
rg: 2
id: finite-left-inverse-identity-does-not-force-balance-proof
kind: route
title: Mark one child by a data track, copy the parent into the unmarked children, and decode from an unmarked child
target: finite-left-inverse-identity-does-not-force-balance
requires: []
artifacts:
  - research/artifacts/gk-vf-positive-b-verification-2026-09-12.md
  - research/artifacts/injective-balance-needs-inf-and-nonlocal-2026-09-12.md
---

This is Section 1.3 of `research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`.

- **Locality and equivariance.** `kappa(x)(v)` reads `x_0` on `{v, v'}` and `x_1` at `p(v)`. Parent, sibling and symbols are all
  preserved by `Aut(T, xi)`.
- **Decoder.**
  - The two children of `u` are never both marked. Marking one needs the other's `x_0` to be `0`, and marking the other needs it
    to be `1`.
  - Track 0 of the output is `x_0`, so the decoder at `u` can pick an unmarked child and return its `z`, which equals `x_1(u)`.
    If neither child is marked, it returns `min(z(c), z(c'))`.
  - The rule is symmetric in the two children, so it is equivariant, and it inverts `kappa` on every input.
  - So the left-inverse identity holds for every pattern on the decoder window.
- **Site law.** `v`, `v'` and `p(v)` are distinct, and the tracks are independent, so

      P(kappa(x)(v) = (1,0)) = q^-2 + (q^-1 - q^-2) q^-1 = 2q^-2 - q^-3 > q^-2 .

**Correction 2026-09-12 (w4-vf-positive-b).**

- **What the first version did:** it quoted `strict-automata-give-injective-ca-with-skewed-site-marginals` for the tree.
- **Why that fails:** that theorem is about groups acting on themselves, and it does not apply to the vertex set of a tree.
- **The over-claim:** the route also claimed an automaton over a group, which would be a Gottschalk counterexample.
- **Now:** the direct construction above replaces it.

**Verification.** `w4-vf-positive-b` failed the first version (wrong setting, over-claimed statement) and passes this version.
Details are in Section 1 of its verification artifact.
