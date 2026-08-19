---
rg: 2
id: mf-not-closed-under-integer-extensions
kind: claim
title: MF fails for extensions of LEF groups by the integers
distinct_from:
  mf-extension-nonclosure: That claim uses the locally finite lamp kernel and the residually finite quotient `V`; this one shrinks the quotient to `Z` and strengthens the kernel from locally finite to LEF, which is what kills the operator-norm analogue of the Elek--Szabo permanence theorem.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

There is a short exact sequence

```text
1 -> ClLamp(X) semidirect T -> W -> Z -> 1
```

whose kernel is LEF (hence sofic and MF) and whose quotient is `Z`, while `W`
is not MF.  So MF is not preserved by extensions with amenable quotient: the
operator-norm analogue of the Elek--Szabo theorem for soficity is false.

A second witness one level up, using `literal-telescope-core-lef`: the
telescope core `E_T = N_E semidirect T` of the literal group is LEF, and
`E = E_T semidirect Z` is not MF.  So the failure is not an artefact of the
Clifford witness; it happens for the literal presented group itself.

Consequence for the frontier: no permanence theorem about `Z`-extensions can
decide `commuting-lamp-quotient-mf` or `literal-mark-quotient-mf`.  All four
groups `E`, `W`, `E/<w>`, `W/<zeta>` are `Z`-extensions of LEF cores; the
first two are not MF and the last two are open, and they differ from their
non-MF partners only by the central mark.  In particular "the core is MF, so
only the stable letter is left" is not a partial proof of anything — the
stable-letter step is the entire difficulty, and it is where the two known
negative answers live.
