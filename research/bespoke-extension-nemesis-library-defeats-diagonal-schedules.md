---
rg: 2
id: bespoke-extension-nemesis-library-defeats-diagonal-schedules
kind: claim
title: A pre-enumerated library of extension nemeses defeats every diagonal defect schedule
artifacts:
  - research/artifacts/meta-recursive-qca-audit-2026-08-22.md
distinct_from:
  canonical-profile-collapse-compactness: that equates already known collapse with a finite local certificate; this gives a constructive decomposition of collapse into approximation-specific extension obstructions sharing one exact infinite model.
  post-candidate-nemesis-has-a-finality-dilemma: that rules out appending a nemesis after seeing a finite tuple; this repairs finality by enumerating all nemeses before any candidate is tested.
  finite-trace-profile-net-is-dimension-free: that compactifies scalar word-moment profiles; this uses existential extension profiles, which can distinguish embeddings having the same canonical scalar word law.
---

**ESTABLISHED.**  Let `Gamma_0` be a finitely generated recursively presented
base group with rational mark `p`.  Fix `alpha>0`, and let `K_alpha` be the
compact space of complete tracial types of canonical matrix-ultraproduct
representations of `Gamma_0` satisfying `||p||_2>=alpha`.

For each `i` let `E_i` be a finite extension gadget: finitely many auxiliary
unitaries and finitely many group-word relations over `Gamma_0`.  Let
`C_i subset K_alpha` consist of the base types admitting an exact extension
through `E_i` in a tracial matrix ultraproduct.  Then `C_i` is closed.

Suppose

```text
for every x in K_alpha, some i satisfies x notin C_i.  (BEN1)
```

Then finitely many gadgets already cover all separated types:

```text
C_(i_1) intersect ... intersect C_(i_r)=empty.         (BEN2)
```

Consequently the recursively presented group obtained by adjoining **all**
`E_i` has no canonical matrix microstate sequence retaining mark norm
`alpha`.  This conclusion is independent of every relation between matrix
dimension and defect rate.

## Proof

The space of bounded tracial types is compact.  Matrix-ultraproduct
realizability is closed under another ultralimit (flatten the iterated matrix
ultraproduct), so `K_alpha` is compact.  For fixed `E_i`, take the compact
type space in the base and auxiliary variables cut out by its exact
relations.  Its projection to the base coordinates is compact, hence closed;
this is `C_i`.

By `(BEN1)`, the open sets `K_alpha\C_i` cover `K_alpha`; compactness gives a
finite subcover, proving `(BEN2)`.  If a canonical microstate sequence for
the group containing every `E_i` retained the mark, its ultraproduct would
give one base type in `K_alpha` extending every gadget, contradicting
`(BEN2)`.

All challenges are present before the approximator is chosen, so there is no
moving-presentation error.  Each fixed gadget's defect vanishes before the
ultraproduct is taken, so there is no candidate-dependent threshold crossing.

## What the approximation fingerprint actually is

Every canonical microstate sequence has the same scalar group-word law:

```text
tr(w(U_n))->tau_(Gamma_0)(w)                for every fixed word w.
```

Thus scalar moments cannot fingerprint which clever approximation is being
used.  The relevant fingerprint is its **existential extension profile**:
the set of finite auxiliary relation systems it can solve compatibly with
the represented base tuple.  Relative commutants, multiplicity reservoirs,
Julia returns and transporter equations all live in this extension profile.
The theorem says a bespoke attack on that richer fingerprint is rigorous if
it is robust (`C_i` closed), exhaustive `(BEN1)`, and pre-enumerated.
