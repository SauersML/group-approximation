---
rg: 2
id: locally-finite-codense-stabilizer-kazhdan-packet-is-sofic
kind: claim
title: A Kazhdan actor with a locally finite nonseparable stabilizer passes every actor-side gate of the character-energy interface, yet its packet base is sofic
distinct_from:
  sofic-chart-quotient-forces-character-energy-floor: that proves no decoder exists once the coordinate action is sofic and the seed-visible gap holds; this proves the hypothesis is realized at a Kazhdan actor with aperiodic seed and nonseparable stabilizer, so passing the actor-side gates never forces nonsoficity.
  amenable-edge-actor-packets-have-hyperlinear-base: that kills actors splitting over amenable edges by Bass--Serre permanence; this actor has property (T), hence (FA), and is killed instead by local finiteness of the point stabilizer.
  finite-bi-index-kazhdan-stabilizer-is-nonseparable: that shows finite-rank infinite actions need nonseparable stabilizers; this shows nonseparability together with a Kazhdan actor and aperiodic seed still permits a sofic action.
  sl3-codense-coset-lamp-recursive-host: that realizes the exact actor-side profile with the finitely generated Kazhdan stabilizer SL_3(Z); this realizes the same profile with a locally finite stabilizer, where Gao--Kunnawalkam Elayavalli--Patchell Theorem 2.14 applies.
  function-field-rank-one-vertex-action-is-sofic: that asks whether a co-dense infinitely generated nonamenable stabilizer gives a sofic action; this uses an abelian locally finite stabilizer, where soficity is a theorem.
  fp-sofic-kazhdan-group-not-residually-finite: that asks for a non-residually-finite sofic Kazhdan group, which the finite-stabilizer version of this construction would need; this avoids it by letting the stabilizer be infinite and locally finite inside a residually finite actor.
---

**ESTABLISHED** by route `locally-finite-codense-stabilizer-kazhdan-packet-proof`.

## Statement

**(LF0) General form.** Let `A` be a finitely generated sofic group, `C <= A` a locally finite subgroup, and
`a in A - C` with

```text
a in  intersect_(N normal in A, [A:N]<infinity)  N C.                (LF1)
```

Put `X=A/C`, `x=C`, `M=direct_sum_X F_2` and `m_0=delta_x+delta_(ax)`. Then:

1. **(aperiodic seed)** every character `chi in M^` with `chi(m_0)=-1` has infinite `A`-orbit, so
   `(ICA1)` of `infinite-character-actor-kills-fd-mark` holds, and every exact finite-dimensional
   unitary representation of the marked packet `P(M rtimes A, m_0)` kills `J`;
2. **(sofic base)** `M rtimes A = F_2 wr_X A` is sofic, so `P(M rtimes A, m_0)` is hyperlinear
   and `J` survives in tracial matrix microstates with negative mass `1/2`. (The packet itself is
   also sofic by permanence of soficity under amalgamation over finite subgroups; that literature
   input is not imported and nothing below uses it.)
3. **(Kazhdan gap)** if `A` has property (T), the seed-visible Schreier gap `(ISC1)` holds with one
   `gamma>0`. Then no dimension-independent modulus bounds `(ISC2)` or `(IWE6)` by word defect, for
   this packet. The same holds for the augmentation submodule `M_0` in place of `M`.

**(LF2) Explicit Kazhdan instance.** Let `A=EL_3(F_2[t])`, and let `lambda:F_2[t]->F_2` be the
linear functional

```text
lambda(t^k) = 1  if k is a power of 2 (k=1,2,4,8,...),   0 otherwise.   (LF3)
```

Put `V=ker lambda`, `C=e_12(V)` and `a=e_12(t)`. Then `A` is finitely generated, residually finite
(hence sofic) and Kazhdan. `C` is an infinite elementary abelian 2-group, so it is locally finite,
and `a notin C`. `(LF1)` holds, and `C` is not separable in `A`. So `(LF0)` applies with `(ISC1)`.

## What this kills

Before this node, the surviving permutation-module hosts of the interface were described by two
gates (see the amenable-edge entry under `## Attempts` of
`infinite-character-actor-word-energy-interface`). The **actor-side gate** asks for a Kazhdan or
(FA) actor, an aperiodic seed `(ICA1)`, the uniform gap `(ISC1)`, exact finite-dimensional
invisibility of `J`, and a co-dense or nonseparable stabilizer. The **action-side gate** asks for a
nonsofic coordinate action. The explicit instance `(LF2)` passes every actor-side gate and fails
the action-side gate. So the two gates are **logically independent**, and the class of arguments
below dies.

> **Killed class.** Any argument that derives mark collapse in microstates, `(ISC2)`, `(IWE6)`,
> `J in Rad_hyp`, or nonsoficity of `A curvearrowright A/C`, and that uses only the following
> about the host: property (T) or (FA) of a finitely generated residually finite actor; `(ICA1)`
> or the profinite condition `(LF1)`; the Schreier gap `(ISC1)`; nonseparability of `C`;
> finite-dimensional invisibility of `J`; recursive presentability of the lamp group.

**Invariant:** local finiteness of the point stabilizer, through Theorem 2.14 of
Gao--Kunnawalkam Elayavalli--Patchell. **Step where every member dies:** the passage from the
exact aperiodicity statement `(ICA1)`, which constrains only exact finite quotients through
`(LF1)`, to a quantitative statement about approximate models. Sofic charts of a locally finite
stabilizer are not quotient actions, so `(LF1)` gives them no constraint.

**Survivors.** A successful host must use a property of `C` that fails for locally finite groups.
The `SL_3(Z) < SL_3(Z[1/2])` and Andre--Guirardel stabilizers are not locally finite, so they
survive. Amenable non-locally-finite stabilizers are not killed here either: Theorem 2.14 does not
cover them, and `amenable-action-of-a-sofic-group-need-not-be-sofic` shows their actions can be
nonsofic.

**Why a finite stabilizer is not enough.** With `C` finite, `(LF1)` needs `a` in the profinite
closure of a finite subgroup, so `A` cannot be residually finite. A sofic instance would answer
`fp-sofic-kazhdan-group-not-residually-finite` in its finitely generated form, and Deligne covers
are not known to be sofic. Letting `C` be infinite and locally finite inside a residually finite
linear actor sidesteps that open problem.

**Scope remark (not load-bearing).** The same proof works for `EL_3(F_2[t,1/t])`, with `lambda`
extended by `(LF3)` on all `t^k`, `k in Z`. That actor is also Kazhdan and is expected to be
finitely presented (rank theorem of Bux--Köhl--Witzel, not imported here). The lamp group is never
finitely presented, because `C` is not finitely generated. So this node does not exclude an
argument that uses finite presentation of the whole packet in an essential way. For permutation
packets that needs finitely generated stabilizers, which are then infinite and not locally finite.
