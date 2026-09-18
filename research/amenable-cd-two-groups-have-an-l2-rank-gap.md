---
rg: 2
id: amenable-cd-two-groups-have-an-l2-rank-gap
kind: claim
title: In the integral group ring of a finitely generated amenable group of cd 2, the L2-ranks of nonzero elements are bounded away from zero
distinct_from:
  amenable-finite-cd-integral-group-rings-are-domains: that asks for no zero divisors, i.e. (for amenable groups) L2-rank exactly 1 for every nonzero element; this asks only for some positive lower bound
  elementary-amenable-torsion-free-strong-atiyah: that is integrality of all matrix L2-ranks for elementary amenable groups; this is a lower bound for 1x1 ranks for amenable cd-2 groups, with no integrality
  amenable-cd-two-l2-rank-gap-forces-baumslag-solitar: that proves this statement is equivalent to Kropholler's question in dimension 2; this is the open statement itself
---

**OPEN.** Let `G` be a finitely generated amenable group with `cd G = 2`. Then there is `c > 0`
such that `dim_U(U(G) a) >= c` for every nonzero `a ∈ Z[G]`. Equivalently,
`dim_NG ker(r_a : ℓ²G → ℓ²G) <= 1 − c`, where `r_a` is right multiplication by `a`.

By `amenable-cd-two-l2-rank-gap-forces-baumslag-solitar` (items 3–4), this is equivalent to
Kropholler's question for groups of cd at most 2, and it then holds with `c = 1`. It suffices to
have the bound for nonzero elements of the trace ideal of one second syzygy `P ≤ Z[G]^d`.

**Shape of a counterexample.** A counterexample has nonzero `a_n ∈ Z[G]` with
`dim_NG ker(r_{a_n}) → 1`. The `a_n` can be chosen in the trace ideal of `P`, each in the image
of a dual-basis functional. For amenable `G`, `dim_NG ker(r_a)` is the Følner limit of the
normalized kernel dimensions of `a` acting on finite Følner pieces (Elek; recalled). So a
counterexample needs integral group-ring elements whose finite kernel densities approach 1.

## Attempts

- **2026-09-18 (lane `w9-112`): annihilator iteration. Dead as a proof; it closes up on itself.**
  See `amenable-cd-two-annihilator-iteration-closes-up`. The planned line was: a thin `a` is a
  zero divisor; `J = ann_l(a)` is a non-finitely-generated projective of dimension `1 − rk(a)`
  (`gl.dim Q[G] <= 2` plus integral Baum–Connes traces); iterate on `J`. Every step goes
  through. `T(J)` contains zero divisors of arbitrarily small rank, so the iteration takes one
  zero divisor to an infinite chain `a_{n+1} ∈ T(ann_l a_n)` with `rk(a_n) → 0` and
  `dim ann_l(a_n) ↑ 1`. No input is ever violated. The exact failing step is the last one: no
  quantity decreases in a way that can bottom out. Ranks tend to 0 without reaching it, and
  Følner densities are the same numbers (Elek). By-product: for torsion-free amenable `G` with
  `cd_Q G <= 2`, the infimum of ranks is either 1 (domain) or 0. Calibration: `Z/2 ≀ Z` satisfies
  every input except integrality and has thin idempotents. So a proof needs an input not implied
  by "one zero divisor exists", and every known such input (coherence, one finite annihilator,
  elementary amenability of the support) is equivalent to this claim.
- **2026-09-18 (lane `w10-112`): a non-circular input, local indicability. Reduction, both
  directions.** See `amenable-cd-two-kropholler-iff-locally-indicable`. The
  Jaikin-Zapirain–López-Álvarez theorem (Strong Atiyah for locally indicable groups, via their
  Proposition 6.5 with trivial kernel) makes `Q[G]` a domain for every amenable LI group. So this
  claim holds, with `c = 1`, for every locally indicable `G`. It is equivalent to the purely
  group-theoretic statement **(Q_ab)**: no finitely generated amenable group of cd 2 has finite
  abelianization. Equivalently, every amenable group of cd at most 2 is left-orderable (Witte
  Morris). A counterexample contains one with finite abelianization. Such a one has Serre's
  property FA except through an index-2 amalgam, and its LI residual carries the whole zero-divisor
  obstruction. Obstruction for the Linnell-class route: an amenable group lies in Linnell's class
  `C` iff it is elementary amenable, so placing the Remark R subgroup in `C` is the target itself.
  What remains open: (Q_ab). The finite-index step is where it stalls, because passing strong
  Atiyah to finite extensions is open, so virtual `b_1 > 0` would not suffice.
- **2026-09-18 (lane `w11-112`): (Q_ab) on the counterexample K. Literature record, two
  reductions, and the finite-index barrier removed without free subsemigroups.**
  - *Literature: what is already solved.*
    - Elementary amenable: Hillman–Linnell. Kropholler–Linnell–Lück: a finitely generated EA group
      of cd at most 2 is `1`, `Z` or `BS(1,m)`.
    - `FP_2`: solved; a counterexample is never `FP_2`
      (`amenable-fp-iff-affiliated-top-homology-vanishes`). Almost coherent groups reduce to this.
    - Linear groups: Tits alternative.
    - Branch groups and the Grigorchuk groups: infinite cd.
    - Residually finite: I found no result. Virtually indicable: not known to suffice in general.
  - *Directed unions and extensions.* See
    `kropholler-dim-two-counterexamples-live-in-generating-classes`. Obstruction: a two-dimensional
    counterexample in the extension-union closure `ED(X)` of a subgroup-closed amenable class `X`
    contains a finitely generated one lying in `X`. So no construction by extensions and directed
    unions from non-counterexample pieces can produce `K`. The step that absorbs each extension is
    the EA-radical theorem: a finitely generated subgroup meets the kernel, or embeds one level
    lower.
  - *No free subsemigroups.* See
    `subexp-amenable-cd-two-kropholler-iff-no-intermediate-growth`. Rosset-type kernels plus
    item 3(c) of `amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar` give: a finitely
    generated amenable NFS group of cd 2 with virtual `b_1 > 0`, or with any infinite EA quotient,
    is `Z²` or `Kb`. So in the NFS class the finite-index stall above disappears. Both-direction
    reductions: Kropholler in dimension 2 for `SG` holds iff no group of intermediate growth has cd at
    most 2. For `ED(amenable NFS)` it holds iff every finitely generated amenable NFS cd-2 group is
    virtually indicable.
  - *What remains.* Two cases are left. A counterexample `K` with a free subsemigroup, where the
    Rosset kernels fail (`BS(1,2)` shows why). Or an NFS `K`, where every finite-index subgroup has
    finite abelianization and there are no infinite EA quotients. The second case contains every
    possible counterexample of intermediate growth.
- **2026-09-18 (lane `w12-112`): the NFS and intermediate-growth case. The Euler-characteristic
  route is equivalent to the target, and it reduces to one weak-Bass inequality. Three
  obstructions, and the H_FD route is circular.** See
  `amenable-cd-two-bass-defect-equals-euler-characteristic` (proposed ESTABLISHED) and the route
  `amenable-cd-two-rank-gap-via-l2-finite-weak-bass`.
  - *Identity.* For an infinite, finitely generated amenable `G` of cd at most 2, the relation
    module `P` has `dim_U(U ⊗ P) = n − 1` and `rank_Q(Q ⊗ P) = n − b_1 + b_2`. So its Bass defect
    is `χ_Q(G) = 1 − b_1 + b_2`.
  - *Reduction, both directions.* The target holds iff `b_1 = 1 + b_2` for all such `G`, iff
    `χ_Q <= 0`, iff every relation module satisfies the weak Bass inequality.
  - *The counterexample `K`.* In `K`, the defect `1 + b_2(K)` sits entirely in the core `P'` with
    no finitely generated summand. In the NFS case it is the same on every finite-index subgroup.
  - *One-direction reduction.* The target follows from the open statement
    `l2-finite-projectives-over-amenable-groups-satisfy-weak-bass`: rational rank is at most
    `L²`-dimension for countably generated projectives of finite `L²`-dimension over torsion-free
    amenable groups. That is a statement about projective modules with no group theory in it.
  - *Obstructions (the brief's growth, Euler-characteristic and L2 route).*
    - (A) Finite truncations. The Hantzsche–Wendt group `HW` is torsion-free, virtually `Z³` and
      has `b_1 = 0`. Its Fox matrices satisfy `rank ε(J) = n > n − 1 >= rank_U(J)`. So no
      termwise rank comparison on finitely many relators can work.
    - (B) Flatness. The colimit of `B = J^*J` over `HW` is a countably generated flat module with
      defect 1 that is not projective. This kills Lazard–Govorov, Følner-truncation and
      f.g.-submodule arguments.
    - (C) `L²` and Følner or growth data. The `U`-dimension profile `(n − 1, n, 1)` is the same as
      for `Z²`, and Degrijse's `χ = χ^(2)` step is literally `D(P) = 0`. So the growth of the
      cellular chain complex together with `L²`-Betti vanishing yields exactly the identity, and
      no bound on `b_2`.
  - *H_FD.* This is a reformulation, not a reduction. By Shalom, an amenable group with H_FD is
    virtually indicable. By `subexp-amenable-cd-two-kropholler-iff-no-intermediate-growth`,
    virtually indicable NFS cd-2 groups are `Z²` or `Kb`, and these have H_FD. So among NFS cd-2
    groups, having H_FD is the same as not being a counterexample. Every known proof of H_FD
    (polycyclic, Shalom; virtually nilpotent, Ozawa) goes through a solvable or finite-dimensional
    structure that `K` lacks.
  - *Next step.* Prove the weak-Bass inequality for countably generated projectives of finite
    `L²`-dimension. The first case to try is groups of subexponential growth. It needs a trace on
    idempotents of column-finite matrices that extends Hattori–Stallings and uses `E² = E`
    globally, since items A and B rule out approximation by finite corners and by flat colimits.
