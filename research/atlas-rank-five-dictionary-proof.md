---
rg: 2
id: atlas-rank-five-dictionary-proof
kind: route
title: Parent-suffix factorization, root-subgroup commutators, and the shared-leaf hinge
target: atlas-rank-five-dictionary
requires: [atlas-charts-overlap-trivially]
---

# Parent-suffix factorization, root-subgroup commutators, and the shared-leaf hinge

The construction and its exact verification are executable:
`experiments/atlas_relator_rank5_dictionary.py` builds each of the 100
words and checks it against `1 + E_k b E_l^*` by exact binary Leavitt
arithmetic (no floats); the full derivation with the recipe table is
`research/artifacts/atlas-rank5-dictionary-2026-08-15.md`.

The two structural inputs, in prose:

1. **Parent-suffix identity.**  Each rank-five leaf factors through its
   rank-three parent, `E_k = γ_{p(k)} s_k`, so
   `E_k b E_l^* = γ_{p(k)}(s_k b s_l^*)γ_{p(l)}^*` reduces every rank-five
   root element to a rank-three root element with a longer ring
   coefficient.  Since coefficients multiply through the commutator
   calculus `[U_{ik}(a), U_{kj}(b)] = U_{ij}(ab)` (a Steinberg relation,
   valid in `E₃(L)` for three distinct indices), the thirty explicit
   rank-three generators — the twenty chart transvections plus the ten
   recorded identity-(7) words — generate every needed coefficient in at
   most two commutator layers.  Nonvanishing of `c = s_k b s_l^*` is a
   letter-pattern check: products of the form
   `[unstarred][letter][starred]` never meet the defining annihilations
   `e^*f = f^*e = 0` of `L`.
2. **Same-parent pairs route through the shared leaf.**  For
   `p(k) = p(l)` the parent-suffix identity yields a coefficient inside
   one chart block where the rank-three indices coincide, so instead
   `x_kl(b) = [x_{k5}(b), x_{5l}(1)]` — legitimate because index 5 is the
   leaf `γ₃` shared by both charts (`atlas-charts-overlap-trivially`
   computed the overlap and identified this leaf as the unique common
   structure), and both factors fall under case 1.

Verification protocol: positive controls on known rank-three identities;
the anti-homomorphism trap of the right-coset action
(`(p·q)(i) = p(q(i))` — each value must be inverted) was caught by a
control and is recorded in the artifact so it is not rediscovered as a
bug.  All 100 verifications pass exactly.
