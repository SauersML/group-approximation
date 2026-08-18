---
rg: 2
id: lamp-coordinate-collision-obstruction
kind: claim
title: Identifying two lamp coordinates costs a full unit of second moment, so 2-norm targets buy nothing
distinct_from:
  finite-quotient-blindness: that is a group-theoretic statement about the image of Gamma being normal in every finite quotient of G; this is a trace computation on the lamp algebra that does not mention Gamma, normality, or any quotient of G, and it applies to any coordinate identification however obtained.
  coordinate-action-not-sofic: that refutes injective equivariant charts of finite windows for approximate actions, with a density-(1-epsilon) deleted set; this is an exact second-moment identity with no window, no epsilon and no deleted set, and it says why weakening the target from operator norm to normalized 2-norm does not rescue a coordinate model.
  exact-models-cannot-separate-marked-pair: that is about labels at the marked PAIR under an exact finite action of G, and its mechanism is expansion; this is about the LAMP algebra over an arbitrary finite coordinate set, its mechanism is one moment, and it needs no action at all.
  block-monomial-coordinate-collapse: that says block-monomial fiber models collapse to permutation models, a structure theorem about a class of models; this prices one identification inside any such collapsed model.
artifacts:
  - research/artifacts/hyperlinear-q34-literature-2026-08-18.md
---

Let `Y` be a set and let `L = ⊕_Y F_2` be the binary lamp group with its
canonical trace, so the canonical unitaries `u_y ∈ L(L)` satisfy `u_y² = 1`,
`τ(u_y) = 0`, and `τ(u_x u_y) = 0` for `x ≠ y`.  The same identities hold for
the coordinate functions of the Bernoulli algebra `L^∞({−1,1}^Y)`.

**Claim.**  Suppose a finite-dimensional model of a window `W ⊆ Y` is built
by a *coordinate map*: a map `p : W → Y'` into a finite coordinate set, with
`u_y` represented by the lamp at `p(y)` (equivalently, any model that factors
through the lamp algebra of a finite coordinate set along a map of index
sets).  If `p(x) = p(y)` for some `x ≠ y` in `W`, then the model's value of
the second moment is

```text
τ_model(u_x u_y) = τ(v²) = 1,     while     τ(u_x u_y) = 0,
```

an error of `1` — the maximum possible — in the normalized trace, hence in
normalized Hilbert--Schmidt distance at that pair.  Therefore **any**
coordinate-identifying architecture must be injective on every tested finite
window, even when the target is only tracial/`2`-norm convergence and not
operator-norm or MF convergence.

**Where it bites.**  The finite-quotient constructions in the current
strong-convergence literature — in particular the generalized Bernoulli
theorem of [GKM26] `arXiv:2607.29571`, whose proof chooses finite quotients
`L/H_n` so that the quotient map is injective on each tested coordinate
window — are coordinate constructions in this sense.  The natural hope that
their separability hypothesis is an artifact of aiming at MF, and could be
dropped when only Connes embeddability is wanted, is false for the binary
lamp: the hypothesis is doing exactly the work this claim prices.  A model
of the Kun--Thom lamps that survives must be quantum and non-coordinate, not
merely measured in a weaker norm.

## Scope

This is a statement about models whose mechanism is a map of index sets.  It
is **not** an obstruction to arbitrary matrix microstates: nothing forbids
finite-dimensional unitaries that satisfy the lamp relations without arising
from any finite coordinate set, and
`vertex-supported-symplectic-completion` builds exactly such families for
`S_min` with exact traces.  It also says nothing about the group action; it
is a statement about the base algebra alone.
