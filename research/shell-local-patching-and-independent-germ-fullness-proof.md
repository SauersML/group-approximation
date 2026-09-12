---
rg: 2
id: shell-local-patching-and-independent-germ-fullness-proof
kind: route
title: Match a finite local patching at all singularities and absorb the remaining prefix homeomorphism
target: shell-envelopes-are-full-cantor-groups
requires:
  - shell-cantor-embeddings-are-finite-germ-extensions
  - full-binary-cantor-groups-have-copy-stabilizers
  - decidable-inputs-have-computable-non-fp-shell-envelopes
artifacts:
  - research/artifacts/boone-higman-full-cantor-clopen-action-2026-09-08.md
---

Let f be a homeomorphism locally agreeing with E=E_nu. Compactness
gives a finite clopen partition on whose pieces f agrees with
specified E elements. Its singular set F relative to V is thus
finite and contained in Omega. Also f preserves every V orbit,
since all its local representatives do. If F is empty, fullness
of V already gives f in V.

Choose v in V taking f(q) to q for every q in F, using high
transitivity on Omega. Then h=v*f fixes F, and each germ of h
at q is an E isotropy germ. The single-singularity realization
theorem supplies a representative a_q in E agreeing with h
near q and singular at most at q.

Correct a_q to be identity near every other point of F. It
already fixes q. Near the finitely many a_q(y), y in F minus
{q}, the map a_q^-1 is a prefix map. Extend those prefix maps
and the identity on a sufficiently small cone about q to one
element v_q in V. The source and target cones can be chosen
disjoint and their complements nonempty, so binary prefix
interpolation applies. Then v_q*a_q has the desired germ at q,
is identity near F minus {q}, and is singular at most at q.

Multiply these corrected representatives over F. The resulting
e in E fixes F and has exactly the prescribed germ of h at
each point there, with singularities contained in F. Consequently
e^-1*h is locally V everywhere. Fullness of V puts this remainder
in V, so h and f belong to E. This proves fullness without
assuming that the input or its envelope is finitely presented.

The copy-stabilizer theorem now applies to E. When P is finitely
generated, so is E, giving the claimed finite-generation consequences.
The required computable non-finitely-presented examples demonstrate
that fullness and these consequences do not close the presentation gap.
