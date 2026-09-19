---
rg: 2
id: exact-second-level-non-mf-switch-unconditional-proof
kind: route
title: Compile FIN and INF by an explicit ray of fixed non-MF marked groups
target: mf-recognition-recursive-presentations-is-second-level-complete
requires:
  - literal-central-mark-corona-invisible
---

# Exact second-level non-MF switch: unconditional proof

## Scope

This note proves a zero-literature-input second-level completeness theorem for
a uniform, code-indexed family of countably presented groups.  This route by
itself does **not** compile those presentations to finite presentations; the
separate Mikhailova benign compiler and tensor-synchronized rope now perform
that later step.

The only non-computability input is the already established literal non-MF
seed: a fixed finitely presented group `E` with a fixed nontrivial element `w`
that is killed by every operator-norm matrix-corona representation.

## 1. The canonical second-level sets

For a partial-recursive program code `c`, let

```text
D_c = { n | c halts on n }.
```

Define `INF(c)` to mean that `D_c` is infinite and `FIN(c)` to mean that it is
finite.

`INF` is `Π⁰₂`: it is equivalent to

```text
for every bound b, there exist n > b and a stage s
such that the step-indexed evaluator halts on n by s.
```

The matrix is a computable Boolean predicate.

To prove hardness without citing an index-set theorem, let

```text
p(a) iff for every n, q(a,n),
```

where `q` is recursively enumerable.  Compile a partial program `P_a` that,
on input `k`, sequentially runs the semideciders for

```text
q(a,0), q(a,1), ..., q(a,k)
```

and halts exactly when all of them halt.  Finite iteration preserves partial
recursiveness.  A universal program code exists for the two-argument runner,
and the constructive `s-m-n` operator specializes it at `a`; hence
`a ↦ code(P_a)` is computable.  Its domain obeys

```text
k ∈ D_{P_a} iff q(a,n) for every n ≤ k.
```

Therefore `D_{P_a}` is infinite iff `p(a)`.  This proves `INF` is
`Π⁰₂`-complete.  Complementation proves `FIN` is `Σ⁰₂`-complete.

## 2. A primitive-recursive event stream

For each code `c`, emit an event for input `n` exactly at its least halting
stage `s`.  Encode the event address as the natural pairing `⟨n,s⟩`.  The
Boolean predicate

```text
firstHaltsAt(c,n,s) :=
  evaln(s,c,n).isSome && !evaln(s-1,c,n).isSome
```

is primitive recursive.  Monotonicity of the step-indexed evaluator proves
that one input has at most one first-halting stage; least-stage selection
proves that every halting input has exactly one.

It follows that:

1. if `D_c` is finite, the event-address set is finite and has a last cut;
2. if `D_c` is infinite, the event-address set is unbounded.

No enumeration theorem is used.

## 3. The exact `E/1` ray switch

At every vertex `j ∈ ℕ`, place one copy `E_j` of `E`.  For each generator `g`
of `E`:

- if there is no event at `j`, impose `g_j = g_{j+1}`;
- if there is an event at `j`, impose `g_j = 1`.

Include the fixed finite relator packet of `E` in every copy.  Call the
resulting presented group `S_c`.

If events are unbounded, then for any `j` a later event kills its vertex, and
the intervening bridge relations propagate this equality backwards.  Thus
every named generator is trivial and `S_c` is the trivial group.

If the event set is finite, choose the cut `J` immediately after its last
event.  Every vertex below `J` is killed.  Every vertex at or above `J` is
identified with vertex `J`.  The map from `E` to the `J`th copy and the map
collapsing the ray back to `E` are inverse homomorphisms.  Hence

```text
S_c is isomorphic to E.
```

This is an explicit generatorwise proof, not an embedding theorem.

## 4. The fixed marked query

For any target group `G`, define

```text
SURV(G) := there exists f : E → G with f(w) ≠ 1,
KILL(G) := for every f : E → G, f(w) = 1.
```

On the switch family:

```text
KILL(S_c) iff INF(c),
SURV(S_c) iff FIN(c).
```

The forward implications use the two exact switch branches.  Conversely,
`SURV` and `KILL` are logical complements, while every set of natural numbers
is either finite or infinite.

Therefore the predicate `c ↦ KILL(S_c)` is `Π⁰₂`-complete and
`c ↦ SURV(S_c)` is `Σ⁰₂`-complete under computable many-one reductions.

## 5. The non-MF consequence

Assume `SURV(G)`, witnessed by `f : E → G` with `f(w) ≠ 1`.  MF-invisibility
is functorial under arbitrary group homomorphisms, so `f(w)` is MF-invisible
in `G`.  Since it is nontrivial, `G` cannot be operator-MF.  Thus every
positive `SURV` instance in the switch family is non-MF.

The non-MF seed is used here as the engine of the consequence, not counted as
a new contribution.

## 6. Formal dependency audit

The Lean proof uses:

- the step-indexed partial-recursive evaluator and its monotonicity;
- finite partial-recursive iteration, universal coding, and `Code.curry`;
- elementary finite-set and pairing facts;
- free groups and presented groups;
- the already proved fixed non-MF mark and its functoriality.

It introduces no axiom, `sorry`, opaque compiler, Chiodo theorem, Higman
embedding theorem, or literature-supplied completeness theorem.

No finite-presentation hardness claim follows from this note alone.  The later
route first passes through the residually finite bidirectional bridge, then
uses the Mikhailova fiber-product benign compiler and tensor-synchronized rope.
Those constructions preserve the two branches without altering this exact ray
calculation.
