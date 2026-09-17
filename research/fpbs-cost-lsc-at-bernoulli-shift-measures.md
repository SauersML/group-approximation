---
rg: 2
id: fpbs-cost-lsc-at-bernoulli-shift-measures
kind: claim
title: Cost is lower semicontinuous at the uniform Bernoulli measure along essentially free ergodic shift measures of every infinite finitely generated group
distinct_from:
  fpbs-fixed-price-iff-cost-lsc-at-bernoulli: that is the drafted equivalence (OPEN pending a full referee pass) of this statement with fixed price for finitely generated groups; this is the open statement itself.
  semicontinuous-invariants-blind-above-rokhlin-supremum: that constrains invariants that are already semicontinuous; this asks whether cost is.
  fpbs-free-action-cost-at-least-bernoulli-cost: that is the direct lower bound C(a) >= C(b) for every free action; this is the equivalent topological statement at the point lambda^G, whose failures have a single-action normal form and which admits no window-local proof.
---

**OPEN.** Let `G` be an infinite finitely generated group and `L` a finite set with `|L| >= 2`
and uniform measure `lambda`. If `nu_n` are essentially free ergodic `G`-invariant measures on
`L^G` with `nu_n -> lambda^G` weak*, then `liminf_n C(nu_n) >= C(lambda^G)`.

**Scope label.** By `fpbs-fixed-price-iff-cost-lsc-at-bernoulli`, this statement for all such
`G` is equivalent to fixed price for all infinite finitely generated groups. It is a
restatement, not a weakening. What is new is its location: one point of one compact space, a
quantitative race form, and a drafted obstruction to window-local proofs. The equivalence,
the race form and the obstruction are OPEN pending a full referee pass (the vote of lens 1 was lost;
lenses 2 and 3 returned *survives*).

## Attempts

- **Race form (drafted content, pending a full referee pass).** A failure is one free ergodic finite-alphabet action
  `nu_0` with `C(nu_0) <= C(b) - eta`, together with Seward models `nu_n -> lambda^G`. Every
  certificate of `nu_n` cheaper than `C(b) - eta/2` must satisfy
  `(M + |S|) TV_W(nu_n, lambda^G) >= eta/2`
  (`fpbs-clopen-certificate-cost-transfer`, item 3). So cheap certificates must need windows that
  grow faster than the models converge. A lower bound on the window size of cheap certificates
  for near-Bernoulli free measures, in terms of the total-variation distance, would prove the
  claim. No such bound is known.
- **Window-local lower bounds are dead.** `fpbs-window-local-cost-lower-bounds-fail-at-bernoulli`
  gives measures `nu_R -> lambda^G` that are iid and free on `B_R`, ergodic, aperiodic, with cost 1.
  For `F_r` the jump is at least `r - 1`. Any argument that deduces a cost lower bound from
  finitely many window statistics, ergodicity, aperiodicity and freeness on a ball fails. Freeness
  of every `nu_n` has to enter globally. Candidate global inputs:
  - the `L2` Betti bound, which gives `C(nu) >= 1 + beta_1^(2)(G)` for free `nu`, the right bound
    exactly when `C(b) = 1 + beta_1^(2)(G)`, and that is again an open fixed-price statement;
  - the Abert–Weiss weak containment `lambda^G ≺ nu_n` with monotonicity of cost, which gives the
    opposite inequality.
- **Where the dominant route and this one meet.** The cycle-tail compactness and correlated
  reuse flags of `fpbs-bernoulli-cycle-tail-compactness` and `fpbs-correlated-reuse-flags-removable`
  control certificates of `lambda^G` itself. Here the certificates that must be controlled belong
  to the models `nu_n`. Their cycle tails are unrestricted, since the models are isomorphic to a
  possibly cheap action. Transporting a certificate of `nu_n` to `lambda^G` costs the race term.
  So compactness at `lambda^G` does not by itself give lower semicontinuity.
- **Spark, not verified.** Seward (arXiv:1311.0738, abstract only; the text was not read) states
  that for nonamenable `G` every p.m.p. action is a factor of a Bernoulli shift over a finite base
  of size depending on `G`. If this holds as stated, it would fix one alphabet size in the claim for
  nonamenable `G`. It needs a verbatim import before it is used.
