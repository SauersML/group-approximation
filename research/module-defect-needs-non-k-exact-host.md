---
rg: 2
id: module-defect-needs-non-k-exact-host
kind: claim
title: A module K-defect forces the host to fail Baum--Connes with coefficients, which is strictly stronger than non-exactness; Haagerup non-exact groups cannot host one
distinct_from:
  some-nonexact-group-has-a-k-inexact-module-triple: that is the open existence of the defect; this is an established necessary condition on the host G and a pruning of the candidate list.
  k-inexact-module-triple-refutes-trivial-coefficient-bc: that turns a defect into a trivial-coefficient counterexample downstream; this constrains the host upstream, before any triple is chosen.
  amenable-kernel-bc-transfer-and-ktop-half-exactness: that imports the transfer theorem and half-exactness; this deduces from half-exactness the necessary host condition and applies Higson--Kasparov to prune the Haagerup non-exact groups.
---

**ESTABLISHED** by `module-defect-needs-non-k-exact-host-proof`.

**Definitions.** For a countable discrete group `G`:
- `G` *satisfies Baum--Connes with coefficients* if the assembly map
  `mu_(G,B) : K^top_*(G; B) -> K_*(B ⋊_r G)` is an isomorphism for every separable
  `G`-C*-algebra `B`.
- `G` is *K-exact* if for every short exact sequence `0 -> I -> A -> A/I -> 0` of `G`-algebras
  and each `j`, the sequence `K_j(I ⋊_r G) -> K_j(A ⋊_r G) -> K_j((A/I) ⋊_r G)` is exact at the
  middle.

**Theorem.**
1. If `G` satisfies Baum--Connes with coefficients, then `G` is K-exact.
2. Hence, for any module triple `(V, W)` (setting of
   `k-inexact-module-triple-refutes-trivial-coefficient-bc`), a middle K-theory defect of
   `K_j(C_0(U) ⋊_r G) -> K_j(C(X) ⋊_r G) -> K_j(C(Z) ⋊_r G)` implies that **`G` fails Baum--Connes
   with coefficients**. In particular `G` is non-exact, but non-exactness is not enough.
3. **The gap is real.** Osajda's groups acting properly on CAT(0) cubical complexes without
   property A (`osajda-monster-hosts-for-bc-module-route`, item (3): arXiv:1406.5015, Theorem 6.3)
   are non-exact yet a-T-menable. By Higson--Kasparov (ibid. item (5)) they satisfy Baum--Connes
   with **every** coefficient, so by (1) they are K-exact and **cannot host a module defect**.

So the entry ticket for the module route is not non-exactness but the strictly rarer failure of
Baum--Connes with coefficients. Among known finitely generated groups this failure is produced
only by a **coarsely embedded expander**: Gromov monsters, Osajda's isometric-expander groups,
and the residually finite non-exact groups built over an expanding family
(`osajda-monster-hosts-for-bc-module-route`, items (1),(2),(4)). The remaining a-T-menable
non-exact groups are pruned.

**Consequences.**
- The module route does not *create* a Baum--Connes failure. It can only *internalise* a
  coefficient failure the host already has, moving it from a coefficient `B` to the group
  `V ⋊ G` with trivial coefficients. The host must already be a coefficient-counterexample group.
- The known coefficient failures of the monsters are realised at **boundary** coefficients with
  no invariant measure -- `l^inf(G)`, `C(βG)`, the uniform Roe algebra -- where the expander's
  ghost lives. The module route asks for the failure to persist at the far smaller coefficient
  `C(V^)`, which carries the **invariant Haar probability measure of full support** and no proper
  open orbit (`module-dual-actions-have-no-wandering-open-sets`). So the sharp open crux of
  `some-nonexact-group-has-a-k-inexact-module-triple` is:

  > Does the Baum--Connes-with-coefficients failure of an expander monster already occur at some
  > *measured* module-dual coefficient `C(V^)`, or only at boundary coefficients?

  A theorem that every `G`-action on a compact space carrying an invariant probability measure of
  full support satisfies Baum--Connes with those coefficients would **kill** the module route; no
  such theorem is known, and the monsters' failures at `l^inf(G)` do not settle the measured case.

**Model test.** With `W = V` the coefficient is `C`, `mu_(G,C)` alone; the trivial group
`G = 1` satisfies Baum--Connes with coefficients and is K-exact, and no defect exists, as it must
not. An exact `G` (e.g. amenable, hyperbolic, linear) is K-exact by definition, so hosts nothing.
