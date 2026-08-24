---
rg: 2
id: orbit-transport-gauge-needs-a-closed-label-set
kind: claim
title: Transporting the regular action along near-orbits solves the gauge system exactly, but only for closed label sets
distinct_from:
  hypergraph-near-perfect-schreier-packing: that asks for coupled partial bijections whose shared permutation copies must be synchronized across relations; this shows that transporting one regular action along disjoint near-orbits makes every tested relation hold exactly on the packed region, so the coupling disappears and a single uncoupled packing remains, and then shows the price is closure of the label set.
  spherical-short-holonomies-admit-local-gauge: that is the open geometric-locality claim itself; this analyses the one natural constructive attack on it, computes the correction radius it achieves, and proves the attack is unavailable for non-closed tables.
  regular-cayley-prototype-components-have-fixed-size: that classifies closed components of a translated consistency graph on a regular orbit; this constructs corrections on a spherical cloud and identifies the Folner obstruction to running the construction on a finite chunk.
  spherical-one-shared-map-relation-extension: that attaches one relation meeting the existing system in a single label; this builds all labels at once out of one regular block and needs no relation-by-relation attachment.
  regular-character-markovization: that produces doubly stochastic matrices on an auxiliary state space with hidden variables allowed; this produces literal permutations of the given cloud within a fixed geometric radius of the given shadow maps.
artifacts:
  - research/artifacts/pdf-gluing-calculus-integration-2026-08-23.md
---

**ESTABLISHED.**  Fix a finite label set `A`, a cloud `x_1,...,x_N` on
`S^(d-1)`, unitaries `{U_a}_(a in A)` and tight shadow matchings `sigma_a` at
radius `rho`, and suppose the tested products have pointwise defect at most
`zeta` in the sense of `(SRC2)`.  For an index `i` write

```text
O_i={sigma_a(i):a in A}                                 (OTC1)
```

for its **near-orbit**.  Say `B subset [N]` is a *packing* if the `O_b`,
`b in B`, are pairwise disjoint and each has exactly `|A|` elements.

## 1. What the construction gives

Assume `A` is closed under left multiplication by the tested labels, i.e.
`sA subset A` for every tested `s`.  Given a packing `B`, define on the packed
region

```text
tau_s(sigma_a(b)) := sigma_(sa)(b),   a in A, b in B.    (OTC2)
```

This is well defined and bijective on `union_(b in B) O_b`, because `a |-> sa`
permutes `A` and the blocks are disjoint.  Then:

1. **Every tested relation holds exactly.**  For `gh=k`,
   `tau_g tau_h(sigma_a(b))=sigma_(gha)(b)=sigma_(ka)(b)=tau_k(sigma_a(b))`.
   No approximation and no synchronization between shared copies is involved:
   the block carries the regular action verbatim.

2. **The induced correction is geometrically local.**  Put
   `c_s=sigma_s^(-1)tau_s`.  For `j=sigma_a(b)` the two indices
   `sigma_s sigma_a(b)` and `sigma_(sa)(b)` are `(3 rho+zeta)`-close as points
   by `spherical-relation-defect-pairs-small-chord`, and `sigma_s^(-1)` shadows
   `U_s^(-1)` at radius `rho`, so

   ```text
   ||x_j-x_(c_s(j))||<=5 rho+zeta.                       (OTC3)
   ```

   This is the geometric locality required by
   `spherical-short-holonomies-admit-local-gauge`, with an explicit constant
   and no exceptional set beyond the ones already charged.

3. **Blocks have full size.**  By
   `trace-separation-sphere-distance-concentration` the points `U_a x_b` for
   distinct `a` are separated by a fixed gap on `1-o(1)` of `b`, so
   `|O_b|=|A|` once `rho` is below half that gap.

Consequently, for a closed label set the entire gauge system reduces to one
packing problem, with the coupled-Schreier difficulty removed.

## 2. The packing is not free

`H={O_i:i in [N]}` is `|A|`-uniform and `|A|`-regular, and assigning weight
`1/|A|` to every edge is a **perfect fractional matching**.  But the degree is
the fixed constant `|A|`, not a growing quantity, so nibble/Frankl-Rodl
integrality arguments do not apply as stated; bounded-degree fractionally
perfect hypergraphs need not have near-perfect matchings.  The indicated
attack is to replace the single matching `sigma_a` by the full radius-`rho`
candidate neighbourhood, which restores growing degree and small codegree and
brings `spherical-near-perfect-local-package` and
`spherical-candidate-hypergraph-quasirandom` into range.

## 3. Why it does not reach the open claim

Step `(OTC2)` needs `sa in A` whenever `a in A` and `s` is tested.  Two
weakenings are available and both fail for a general table.

- **Exact closure.**  If `A` is the element set of a finite group, the
  construction applies and the gauge claim holds for that table, subject only
  to the packing.  This is the degenerate case: the table is already realized
  by permutations.
- **Almost invariance.**  Allowing partial bijections — legitimate by
  `partial-schreier-completion-preserves-sofic-loss` — it suffices that

  ```text
  |A cap s^(-1)A|>=(1-eps)|A|   for every tested s.      (OTC4)
  ```

  But requiring `(OTC4)` for a subset `A` of every finite tested chunk of an
  ambient group `Gamma`, for every `eps>0`, is exactly the Folner criterion.
  It therefore holds for all chunks precisely when `Gamma` is amenable, in
  which case `Gamma` was already sofic and the construction proves nothing new.

Hence orbit transport is **circular** as an attack on the general claim: the
data it needs to start is the partial-action data whose existence is the
conclusion.

## 4. What this rules out and what it protects

- Any attack that builds the corrected maps by declaring near-orbits and
  transporting the regular action is disposed of by section 3, whatever
  packing technology it uses.
- No counterexample to `spherical-short-holonomies-admit-local-gauge` can be
  produced from a closed table or from an amenable ambient group: sections 1
  and 2 give the corrections there, up to the packing, at radius `5 rho+zeta`.
  A refutation must live on a non-amenable chunk.
- Together with
  `spherical-displacement-length-is-not-conjugation-invariant`, the two natural
  imported strategies for that node — cohomological trivialization via a metric
  cone, and constructive orbit transport — are both closed. The surviving
  content is metric and non-amenable: propagate a correction across boundedly
  many relations of a non-closed chunk, paying `2 rho` per shadow conjugation,
  without an invariant block to transport.
