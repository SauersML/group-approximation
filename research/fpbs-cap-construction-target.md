---
rg: 2
id: fpbs-cap-construction-target
kind: claim
title: Construct low-cost Burnside Bernoulli subrelations with vanishing adaptive overlap penalties
root: true
---

**OPEN.** Construct actual S_m, paths, weights and q-values in the target Bernoulli action satisfying (2.5). The adaptive theorem only completes such witnesses. The hyperfinite barrier refutes the small-average-defect hyperfinite shortcut, not this capacity target and not fixed price one.

## Attempts

* **Reuse the fixed-connector construction.** The previous sufficient
  criterion asked for small average defects along fixed disjoint torsion
  connectors, which is `fpbs-burnside-low-cost-averaged-connector-target`.
  **Where it dies for that target, and why this one exists:**
  `fpbs-cap-hyperfinite-barrier` and `fpbs-cap-robust-barrier` bar every
  hyperfinite implementation of it. Route (B) of Section 7 of
  `research/artifacts/fpbs/connector-capacity.md` replaces fixed connectors by
  adaptive candidate path families with root-dependent weights and arbitrary
  overlaps, which need not make any deterministic connector nearly always
  available, so the mean-defect obstruction does not by itself apply. That is
  the whole reason this target is stated separately, and it is not evidence
  that the target is reachable.
* **Complete a witness with the adaptive theorem.** `fpbs-cap-adaptive-repair`
  gives an explicit relative-cost bound from overlapping path certificates,
  derandomizing finite point labels and applying a second-moment success
  inequality, and `fpbs-cap-completion-criterion` joins the generator repairs
  and applies Bernoulli maximality. **Where it dies:** those theorems only
  complete a witness. The actual `S_m`, candidate paths, weights and
  `q`-values satisfying (2.5) inside the target Bernoulli action are not
  constructed, and Section 7 says so.
* **Take the seeds off the shelf.** `fpbs-cut-low-cost-seeds` supplies
  ergodic, nowhere-hyperfinite subrelations of cost `1+t` in the target
  action. **Where it dies:** they carry no overlap-penalty estimate, and
  inside the `F_2` treeing they come with a capacity obstruction of their own
  (Section 7 of `research/artifacts/fpbs/cut-repair.md`), so a construction
  must supply genuine alternate ambient paths rather than rename paths in the
  tree.
* **Infer it from the divergent torsion counts.**
  `fpbs-cap-variable-order` shows torsion return families with divergent
  weighted counts have zero relative cost, and `fpbs-short-disjoint-torsion-detours`
  produces exponentially many short disjoint detours from subgroup expansion.
  **Where it dies:** these are statements about the group and about relative
  cost given the families; they do not exhibit the measurable selection inside
  a specific Bernoulli action, which is what (2.5) quantifies over.
