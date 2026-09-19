---
rg: 2
id: thompson-f-co-amenable-hosts-have-no-free-or-kazhdan-subgroups
kind: claim
title: Class kill for the host route to non-amenability of F - every group containing Thompson's F co-amenably has no non-abelian free subgroup, no non-amenable torsion subgroup and no infinite Kazhdan subgroup, and every non-amenable quotient of it is again such a host
distinct_from:
  thompson-f-is-not-co-amenable-in-its-known-nonamenable-hosts: that lists four named overgroups and kills each by a dynamical witness (a fixed point on the boundary, or a hyperfinite Lebesgue orbit relation); this names no host, assumes only co-amenability, and kills every host whose non-amenability is certified by a free, torsion or Kazhdan subgroup, including hosts nobody has written down.
  co-amenable-hosts-inherit-the-relative-schreier-gate: that is the general transfer lemma for an arbitrary co-amenable pair H <= G; this instantiates it at H = F, using that F has no free subgroups, is torsion-free, is a-T-menable and has only abelian proper quotients, and draws the consequences for Zaremsky Problem 2.1.
  thompson-f-has-no-free-subgroups: that is the classical Brin-Squier fact about F itself; this says the same absence is forced on every co-amenable overgroup of F, which is a statement about groups that need not be piecewise linear or act on the line at all.
  every-f-free-subgroup-of-thompson-f-is-amenable: that is an open statement about subgroups of F with no copy of F; this is an established statement about subgroups of overgroups of F.
  f-has-a-co-amenable-subgroup-neither-ea-nor-containing-f: that asks for a co-amenable subgroup inside F; this constrains groups in which F itself is co-amenable.
  simple-kazhdan-groups-have-no-proper-co-amenable-subgroups: that assumes property (T) for the ambient group; item 3 here forbids infinite Kazhdan subgroups of the host, which may be far from normal and of infinite index, and assumes nothing about the host.
artifacts:
  - research/co-amenable-hosts-inherit-the-relative-schreier-gate.md
  - research/co-amenable-hosts-relative-schreier-gate-proof.md
---

**ESTABLISHED.** Call a group `G` a **host** for Thompson's group `F` if `F ≤ G` and `F` is
co-amenable in `G`. The route to `thompson-f-is-not-amenable` known as "exhibit `F` as a
co-amenable subgroup of a group already known to be non-amenable" needs a *non-amenable* host,
because a host is amenable exactly when `F` is. Then:

1. **No free subgroup.** A host contains no non-abelian free subgroup.
2. **No non-amenable torsion subgroup.** Every torsion subgroup of a host is amenable.
3. **No infinite Kazhdan subgroup.** Every subgroup of a host with property (T) is finite.
4. **Quotient closure.** If `G` is a host and `π : G ↠ Q` with `Q` non-amenable, then `π` is
   injective on `F` and `Q` is again a host. So a host cannot be simplified by passing to a
   quotient.
5. **The residual gate.** If `G` is a non-amenable host and `Λ ≤ G` is non-amenable, then either
   some `Λ ∩ gFg^{-1}` is non-amenable — in which case `F` already contains a non-amenable
   subgroup and no host is needed — or all of them are amenable, none of them is co-amenable in
   `Λ`, and yet the Cheeger constants of the Schreier graphs `Sch(Λ, Λ ∩ g_nFg_n^{-1})` tend to `0`
   along some sequence `g_n`.

**Which certificates this kills, and at which step.** A host route must come with a *proof* that
the host is non-amenable. Every standard certificate class dies, at the single step "restrict the
invariant mean on `G/F` to the subgroup carrying the certificate":

| Certificate for non-amenability of `G` | Killed by | Named examples excluded as hosts |
|---|---|---|
| a non-abelian free subgroup (von Neumann) | item 1 | `V` (explicit ping-pong in the route), `T` (it contains `PSL_2(Z)`), `nV`, any host containing either |
| a Tits alternative in a known class | item 1 | finitely generated non-amenable linear groups (Tits), non-elementary hyperbolic and relatively hyperbolic groups, acylindrically hyperbolic groups (Osin), mapping class groups, `Out(F_n)`, groups acting properly cocompactly on `CAT(0)` cube complexes (Sageev-Wise), subgroups of `Homeo_+(S^1)` with no invariant probability measure (Margulis) |
| a non-amenable torsion subgroup | item 2 | free Burnside groups `B(m,n)`, Ol'shanskii's Tarski monsters, Nekrashevych's simple torsion groups |
| property (T), or a Kazhdan subgroup with a spectral gap | item 3 | any host with an infinite Kazhdan subgroup |
| a non-amenable quotient | item 4 | any host whose non-amenability is inherited from a quotient: the quotient is a smaller host and the problem is unchanged |
| a compact `G`-space with no invariant measure on which `F` has one | `thompson-f-is-not-co-amenable-in-its-known-nonamenable-hosts` item 1-2 | circle and Cantor hosts where `F` fixes a point |
| a non-hyperfinite orbit relation on a space where `R_F` is hyperfinite | the same node, items 3-4, through `co-amenable-subgroups-transfer-hyperfinite-orbit-relations` | the Lodha-Moore group, Monod's `H(A)` |

**The invariant.** The obstruction is the `F`-relative Schreier-Cheeger constant of the certificate
subgroup: for `Λ ≤ G` with finite generating set `S`,
`κ_F(Λ) = inf { h(Sch(Λ, L, S)) : L ≤ Λ isomorphic to a subgroup of F }`. A host admits no `Λ` with
`κ_F(Λ) > 0` (`co-amenable-hosts-inherit-the-relative-schreier-gate`, item 1). For a free group of
rank `2` over cyclic subgroups, `κ_F ≥ 2`; for a torsion group over the trivial subgroup, `κ_F` is
the Cheeger constant of its own Cayley graph; for a Kazhdan group over its infinite-index
subgroups, `κ_F` is bounded below by the Kazhdan constant.

**What a surviving host must be.** Putting items 1-5 together with the two dynamical mechanisms of
`thompson-f-is-not-co-amenable-in-its-known-nonamenable-hosts`, a host that still proves anything
must be a non-amenable group with no non-abelian free subgroup — a counterexample to the von
Neumann-Day problem — that is not detected by torsion, by property (T), by any Tits alternative, by
a boundary action on which `F` has an invariant measure, or by a measured orbit relation on which
`R_F` is hyperfinite; and moreover every non-amenable subgroup of it must be cut by the conjugates
of `F` into amenable pieces whose Schreier graphs degenerate. Among the known counterexamples to
the von Neumann-Day problem, the torsion ones (Adian, Ol'shanskii, Nekrashevych) contain no copy of
the torsion-free `F` at all, and the two that are known to contain `F` — the Lodha-Moore group and
Monod's `H(A)` — were already killed by the measured mechanism. So no host in the current
literature survives, and a new one must be produced together with a non-amenability proof of a kind
that has never been used.

**Honest scope.** This does **not** show that `F` is co-amenable in no non-amenable group, and it
cannot: if `F` is non-amenable then `F ≤ F × Z` is a co-amenable inclusion into a non-amenable
group. The content is that any such host is useless as a *certificate*, because every way we
currently know of proving a group non-amenable is blocked.

Proof route: `thompson-f-co-amenable-host-gate-proof`.

## Attempts

- 2026-09-18, lane `e2-w2-f-coamenable-host` (paradigm/decomposition, family `host-geometry`).
  First tried to extend the hyperfinite transfer lemma to all one-dimensional hosts. That dies:
  a free group acting on `[0,1]` through a planar embedding of its Gromov boundary has an invariant
  measure (`δ_0`) and topologically amenable, hence hyperfinite, orbit relations for every
  quasi-invariant measure, so neither dynamical mechanism sees its non-amenability. The
  combinatorial restriction argument recorded above kills it instead, and kills the whole class.
