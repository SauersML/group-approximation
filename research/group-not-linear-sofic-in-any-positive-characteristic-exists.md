---
rg: 2
id: group-not-linear-sofic-in-any-positive-characteristic-exists
kind: claim
title: Some countable group is not linear sofic over any field of positive characteristic
distinct_from:
  non-linear-sofic-group: that asks for failure over one field; this asks for failure over F_p for every prime p, possibly with a group that is complex-linear sofic.
  non-finite-field-linear-sofic-group-exists: that also forbids models in large characteristic; this allows them, so it is the fixed-characteristic component only.
  non-large-characteristic-linear-sofic-group-exists: that is the large-characteristic component of the root; this is the fixed-characteristic component.
  linear-sofic-group-algebra-is-stably-finite: that gives stable finiteness from linear soficity over one field; this is the existence of a group escaping every positive characteristic, for which non-stable-finiteness of every F_p[G] is one sufficient certificate.
---

**OPEN.** Some countable `G` is not `F_p`-linear sofic for any prime `p`.
- Equivalently, for every prime `p` some `G_p` is not `F_p`-linear sofic. The free product of the `G_p` is a single
  witness, and it can be taken two-generator simple.
- Definitions are on `root-splits-into-large-and-fixed-characteristic-witnesses`.

**Role.** This is component (b) of the characteristic split. The root holds iff this holds together with
`non-large-characteristic-linear-sofic-group-exists`. Given a witness `H` of that component, only the primes in the
finite set `S(H)` are needed here.

**Sufficient certificates.**
- **Direct finiteness, prime by prime.** For each `p`, find `G_p` and a one-sided invertible matrix pair over `F_p[G_p]`
  (`linear-sofic-group-algebra-is-stably-finite`). Formal strict pairs also work
  (`formalizable-strict-pairs-certify-non-linear-soficity`).
- **Asymmetry with component (a).**
  - In characteristic `0`, group algebras are stably finite (Kaplansky), and every `C[G]` carries a separating
    Sylvester rank function.
  - No such theorem is known in characteristic `p`. So algebraic certificates are available here and only here.

## Attempts

- **2026-09-17, `sw-070`: size obstruction for algebraic certificates (landed as
  `bounded-char-p-certificates-transfer-to-characteristic-zero`).**
  - For each `(k, m)`, a computable `p_K(k, m)` bounds the primes at which any group has a pair `ab = 1 != ba` in
    `M_k(F_p[G])` with supports of size at most `m`.
  - The proof fixes the coincidence pattern by pigeonhole, passes to the ultraproduct group over the ultraproduct field,
    which has characteristic `0`, and applies Kaplansky.
  - So the direct-finiteness certificates above must grow with `p`, and no fixed integral or Leavitt-type design
    serves infinitely many primes.
  - Similarly, a `C`-linear sofic witness must fail on tables whose size tends to infinity with `p`.
  - Settles nothing about existence.
- **2026-09-17, `sw-070`: central `Z/p` permanence in its own characteristic (open, not landed as a claim).**
  - Target statement: for a central extension `1 -> Z/p -> E -> Q -> 1` with `Q` in `L_p`, `E` is in `L_p` iff the
    central mark avoids `Rad_rk,p(E)`.
  - Since `zeta_p = 1` in characteristic `p`, the mark must act unipotently rather than as a scalar. A sufficient
    input is a rank-approximate "infinitesimal projective representation" over `F_p[t]/(t^2)` with multiplier `1 + tc`.
  - That would give `E_3` in `L_3`, a new class at the prime left open by
    `deligne-cover-linear-soficity-is-rank-projective-approximation`.
  - **Dead sub-approaches.**
    - *Cup products and Weyl tricks with finite coefficients.* They reach only classes inflated from finite quotients.
      These die on non-residually-finite covers such as Deligne's.
    - *Skew products on `X x Z/p`.* Diagonal monomial models need the lifted cocycle to be Hamming-close to
      coboundaries on a sofic approximation. That condition is independent of the characteristic, so it gives nothing
      new at `p`.
    - *Trace obstruction.* `n <c, c'>` constrains only exact representations and is invisible to rank-approximate ones.
  - **Live route.**
    - Over `O = Z_p[zeta_p]` one has `O/(p) = F_p[pi]/(pi^(p-1))` and `zeta_p = 1 + pi` mod `pi^2`.
    - `p`-integral complex models with `z -> zeta_p` reduce to `F_p`-models. The mark then has separation at least
      `1 - 1/e`, and the defect is controlled by rank over the fraction field.
    - This needs integral models and fails at `p = 2`.
