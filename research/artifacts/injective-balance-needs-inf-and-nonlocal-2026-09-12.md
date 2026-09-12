# Balance of an injective rule: the entropy proof is exactly INF, and the finite identity is not enough

Lane `w3-bal-prove`, 2026-09-12. Supports
`finite-left-inverse-identity-does-not-force-balance` and enriches the Attempts of
`every-injective-ca-has-uniform-single-site-output-law` and
`injective-ca-images-have-full-single-site-entropy`.

Setup. `G` a group, `A` a finite alphabet, `tau` a cellular automaton with memory `M ni e` and
local rule `mu : A^M -> A`. Write `lambda` for the uniform product measure on `A^G` and
`p(a) = |mu^{-1}(a)| / |A|^{|M|}` for the single-site output law, so `mu` is **balanced**
(`p` uniform, `H(p) = log|A|`) iff `nu = tau_* lambda` has uniform one-site marginal at `e`.
Goal-relevant fact (already on main): over all alphabets, `tau injective => mu balanced` for `G`
is equivalent to surjunctivity of `G`.

## 1. The conjugacy-entropy proof factors through INF, and the h_fin slack is unusable

The standard proof that `tau injective => mu balanced` is three lines:

1. `tau` is a measure conjugacy from `(A^G, lambda)` onto `(Y, nu)`, `Y = tau(A^G)`.
2. Rokhlin entropy is a measure-conjugacy invariant, so
   `h^{Rok}_nu(Y) = h^{Rok}_lambda(A^G)`.
3. Rokhlin entropy is bounded by any generating partition, in particular the one-site partition:
   `h^{Rok}_nu(Y) <= H_nu(text{site } e) = H(p) <= log|A|`.

Chaining, `h^{Rok}_lambda(A^G) <= H(p) <= log|A|`. **So `H(p) = log|A|` (balance) follows the moment
`h^{Rok}_lambda(A^G) = log|A|`, which is exactly INF**
(`bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`), and conversely this is the only lower
bound the argument ever produces for `H(p)`.

Steps 1-3 hold over every group: conjugacy invariance and the partition bound are the content of
`rokhlin-entropy-is-the-largest-partition-bounded-invariant`. The one and only nonamenable-sensitive
input is `h^{Rok}_lambda(A^G) = log|A|`.

The h_fin slack does not help this argument. We know
`h^{Rok} <= h_fin <= log|A|` (`injective-ca-images-have-full-single-site-entropy`), so
`h_fin = log|A|` is a priori weaker than INF. But the conjugacy argument lower-bounds `H(p)` only by
`h^{Rok}_lambda`, never by `h_fin`: the quantity it transports across the conjugacy is the entropy
*rate*, not the finite-radius invariant. **To beat INF one must lower-bound the one-site entropy of
the specific image measure `nu` directly, not through the entropy rate of the conjugate system.** No
such direct bound is known; equivalently, whether `h_fin = h^{Rok}` on Bernoulli shifts is open, and
a positive answer would collapse the slack and make balance exactly INF-hard.

Where finite models enter, concretely. Estimating `H(p)` by counting the window map
`tau_F^+ : A^{FM} -> A^F` factorises into the per-site contributions of `mu` only up to the overlap
among the translates `gM`, `g in F`; the error is a boundary term of size `|FM setminus F|`. The
factorised count gives `H(p) = log|A|` exactly when `|FM setminus F|/|F| -> 0`, i.e. along a Folner
sequence. For `R^x`, Thompson `V` and every nonamenable host there is no Folner sequence and the
boundary is a constant fraction of the bulk, so the window count never factorises. This is the same
wall as step 3's dependence on INF, seen combinatorially.

## 2. The finite left-inverse identity does not force balance

**Correction 2026-09-12 (w4-vf-positive-b).** Details are in Section 1 of
`research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`.

- **The error.** The argument below treats the end-fixing tree as a group `Gamma` with configurations
  `B^Gamma`, and quotes the group theorem `strict-automata-give-injective-ca-with-skewed-site-marginals` for
  it. Neither step is right:
  - the tree automaton lives on the vertex set of `T`, a homogeneous space of `Aut(T, xi)`;
  - an unbalanced injective automaton on `B^Gamma` for a group `Gamma` would be a Gottschalk counterexample.
- **The correct witness.** A direct tree construction: a data track marks one child, and the unmarked
  children copy the parent. It shows only that `(*)`, read on an abstract incidence pattern, does not force
  balance.
- **The conclusion that does not follow.** The tree pattern fails right cancellation of reads, which every
  group window has. So "any proof must import a nonlocal input" does not follow. On group windows the question
  is equivalent to the goal.

Injectivity of `tau` yields, by Curtis-Hedlund-Lyndon for the inverse (valid over every group), a
finite decoder memory `E` and rule `rho` with

```text
rho( ( mu(w|_{eta M}) )_{eta in E} ) = w(e)   for every w in A^{EM}.      (*)
```

`(*)` is a genuine finite identity: the full shift puts no constraint on the window `EM`, so it
quantifies over all patterns. It uses only the coincidence pattern of `EM subset G`, so it is
group-independent data.

**`(*)` does not imply balance.** Take `Gamma` the end-fixing tree automorphism group, which carries
a strict (injective, non-surjective) automaton `tau_0`
(`end-fixing-tree-symmetries-carry-strict-automata`). By
`strict-automata-give-injective-ca-with-skewed-site-marginals`, `tau_0` produces an injective
automaton `kappa` over the same `Gamma` whose one-site output law is non-uniform, i.e. `kappa`'s rule
is **not balanced**. Being injective, `kappa` satisfies `(*)` for some finite `E`. So `(*)` holds and
balance fails simultaneously.

Consequence. A proof of `injective => balanced` cannot be a finite/local counting argument from `(*)`
alone; the coincidence pattern of the window carries the group's modularity, and over a nonunimodular
window `(*)` coexists with non-balance. Any proof must import a nonlocal input — unimodularity plus a
soficity/amenability substitute — which is precisely the INF ingredient isolated in Section 1.

## 3. Net

**Correction 2026-09-12 (w4-vf-positive-b).** The finite-identity method is refuted only off groups, on the
tree's vertex set. On group windows it is equivalent to the goal. See the correction at the start of
Section 2.

Balance of injective rules is not a front below INF for the entropy method: the conjugacy proof is
exactly INF, and the finite-identity method is refuted outright by the tree's amplified automaton. The
only opening left is a direct one-site-entropy bound on the image measure `nu` that avoids the entropy
rate; that is the content of `injective-ca-images-have-full-single-site-entropy` and remains open.
