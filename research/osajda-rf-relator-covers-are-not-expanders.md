---
rg: 2
id: osajda-rf-relator-covers-are-not-expanders
kind: claim
title: Z/2-homology covers never form an expander family, so the relators of Osajda's residually finite non-exact groups are not expanders and those groups are not known Baum--Connes coefficient-failure hosts
distinct_from:
  osajda-monster-hosts-for-bc-module-route: that is the source-verified host inventory; this proves a spectral fact about the relator graphs of its item (4) and draws the consequence that item (4) is not a verified host.
  module-defect-needs-non-k-exact-host: that proves a module defect needs a host failing Baum--Connes with coefficients; this shows the residually finite non-exact groups are not known to be such hosts.
---

**ESTABLISHED** by `osajda-rf-relator-covers-are-not-expanders-proof`.

**Theorem (spectral).** Let `B` be a finite connected simplicial `D`-regular graph with `n`
vertices and first Betti number `b_1(B) >= 1`. Let `B^ -> B` be its **Z/2-homology cover**, the
regular cover with deck group `H_1(B; Z/2)` corresponding to `ker(pi_1(B) -> H_1(B; Z/2))`. Let
`L = D·I - A` be the Laplacian of `B^` and `lambda_1(B^)` its smallest eigenvalue on the orthogonal
complement of the constants. Then

```text
lambda_1(B^)  <=  4 / n,     and so the Cheeger constant   h(B^)  <=  sqrt(8 D / n).
```

The bound is in terms of the size of the **base** `B`, not of the cover.

**Application to Osajda's residually finite groups** (arXiv:1703.03791; host item (4) of
`osajda-monster-hosts-for-bc-module-route`).
- The relators are `Theta^_1`, the Z/2-homology cover of `Theta_1`, and `Theta^_(i+1)`, the
  Z/2-homology cover of a finite normal cover `Theta-bar_(i+1)` of `Theta_(i+1)`. Here `(Theta_i)`
  is a sequence of `D`-regular graphs, `D >= 3`, of growing girth.
- Each base `B_i` is `D`-regular with `b_1 >= 1`. Its girth is at least `girth(Theta_i)`, since
  covering maps send cycles to closed non-backtracking walks. So `n_i = |V(B_i)| -> infinity`.
- By the theorem, `lambda_1(Theta^_i) <= 4 / n_i -> 0`. The isometrically embedded relator graphs
  are **not an expanding family**.

**Consequence for the module route.**
- Osajda derives non-exactness from growing girth alone, through Willett's theorem.
- Every known Baum--Connes coefficient failure uses an embedded expander:
  Higson--Lafforgue--Skandalis (weak embedding), Willett--Yu I, and Finn-Sell arXiv:1401.6841,
  whose Definition 3.5 asks for a coarsely embedded large-girth expander.
- So these residually finite groups are non-exact, but **no known theorem makes them fail
  Baum--Connes with coefficients**. They are not verified hosts for
  `some-nonexact-group-has-a-k-inexact-module-triple`.
- The residually finite congruence handle in
  `monster-bc-failure-at-measured-coefficient-is-the-module-crux` has no known host.
- This lane does not settle whether any residually finite group contains a weakly or coarsely
  embedded expander. The check behind "no known theorem" is bounded to the four sources named
  above, with no further search.

**Model tests.**
- *Hypothesis-failing model.* For a tree (`b_1 = 0`) there is no nontrivial character, the cover
  is `B` itself, and the argument gives nothing, as it should.
- *Cycle.* `B = C_n` (`D = 2`, `b_1 = 1`). The Z/2-homology cover is `C_(2n)` and
  `lambda_1 = 2 - 2 cos(pi/n)`, which is about `pi^2 / n^2` and at most `4/n` (at `n = 3`:
  `1 <= 4/3`).
- *Real object.* `B = K_4` (`D = 3`, `n = 4`, `b_1 = 3`). The bound gives `lambda_1 <= 1` for the
  32-vertex cover. Flipping one edge of `K_4` gives a signed adjacency whose all-ones Rayleigh
  quotient is `(12 - 4)/4 = 2`, so the twisted Laplacian has an eigenvalue at most `3 - 2 = 1`.
  This matches.
- *Not too strong.* An expander `B` keeps its own spectral gap. Only the non-trivial characters
  of the large abelian deck group create small eigenvalues. This is why abelian covers such as
  Bilu--Linial 2-lifts must be chosen carefully to stay expanders.

**Novelty.** The spectral bound is elementary and very likely folklore. It is recorded for the
correction it forces in the host inventory, which earlier stated without verification that these
groups can be built over an expanding family.
