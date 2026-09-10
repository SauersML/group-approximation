---
rg: 2
id: fpbs-cut-burnside-network-target
kind: claim
title: Construct vanishing fractional-cut repair budgets for odd Burnside Bernoulli seeds
---

**OPEN.** In the actual Bernoulli action of a sufficiently large odd-exponent B(2,n), construct low-cost seeds and measurable networks satisfying (8.1). The seeds in Section 7 are available, but no sufficient global cut capacities are proved for them. Finite corridor examples are not an ambient-action construction. This is a class-specific target, not universal Fixed Price.

## Attempts

* **Fit the constructed seeds to the network criterion.**
  `fpbs-cut-low-cost-seeds` gives, inside the target Bernoulli action of any
  countable nonamenable group, nested ergodic subrelations `S_t` with
  `C(S_t)=1+t`, nonhyperfinite on every positive-measure restriction and with
  `relC(S_t;S_s)=t-s`. `fpbs-cut-measurable-repair` and
  `fpbs-cut-network-reliability` then convert fractional load and global cut
  capacity into repair. **Where it dies:** Section 7 of
  `research/artifacts/fpbs/cut-repair.md` gives a literal capacity obstruction
  inside the `F_2` treeing that produces the seeds. Remove a missing `V`-edge,
  partition the certificate representatives across the two resulting sides,
  and every crossing edge-path must use that edge's selection label, so the
  load constraint forces `kappa<=1`. Beating this needs genuine alternate
  ambient paths, not renamed paths in the tree.
* **Argue that torsion cycles supply the capacity.** The transparent
  direct-edge target is `kappa/log v -> infinity` on almost every root with
  `log(1/epsilon)=o(kappa)`. **Where it dies:** Section 8 states that mere
  existence of torsion cycles is not asserted to imply large global capacity,
  and that this is the unproved step. Counting `n` disjoint torsion cycles is
  not a capacity that diverges at a fixed exponent, a point Section 7 of
  `research/artifacts/fpbs/docs/fixed-price-burnside-explicit-bound.md`
  repeats.
* **Read the finite corridor model as the ambient construction.**
  `fpbs-cut-corridor-separation` shows cut-based repair succeeds on finite
  corridors where every whole-path overlap certificate fails, which is a
  genuine separation from the previous criterion. **Where it dies:** a finite
  corridor is not a measurable network in the ambient action, and Section 8
  explicitly does not assert that the seeds realize it.
* **Take existence of low-cost seeds as evidence.** **Dead as an inference:**
  Section 7 notes that the same seed construction works for `Gamma=F_2`, whose
  Bernoulli action has cost two, and there restoring `S_1` from `S_t` costs
  exactly `1-t`. Existence of nowhere-hyperfinite seeds of cost near one
  therefore carries no information about fixed price one by itself.
