---
rg: 2
id: amenable-cd-two-bass-defect-equals-euler-characteristic
kind: claim
title: For a finitely generated amenable group of cd 2, the weak-Bass defect of its relation module equals its rational Euler characteristic 1 - b_1 + b_2, so Kropholler's question in dimension 2 is exactly the weak Bass inequality for these non-finitely-generated projectives; flatness, finite truncations and L2 data cannot supply it
distinct_from:
  amenable-cd-two-groups-have-an-l2-rank-gap: that is the open rank-gap form; this identifies the single missing inequality as a weak-Bass inequality for one countably generated projective, and proves that three classes of arguments cannot give it
  amenable-cd-two-kropholler-iff-locally-indicable: that reduces the question to b_1 >= 1 for every finitely generated amenable cd-2 group; this shows the sharper b_1 = 1 + b_2 is equivalent, and rewrites it as rank_Q(Q ⊗ P) <= dim_U(U ⊗ P) for the relation module
  l2-small-projectives-with-rank-gap-are-finitely-generated: that splits an L2-small projective as finitely generated plus a core with no finitely generated summand; this computes the Bass defect of that core for the relation module of a counterexample, namely 1 + b_2
  amenable-free-top-syzygy-forces-type-fp: that bounds free summands of the second syzygy by d - 2; here all finitely generated projective summands have defect 0, and the whole defect 1 + b_2 sits in the core
  amenable-fp-iff-affiliated-top-homology-vanishes: that uses Degrijse's Euler-characteristic step only for groups of type FP; this computes what that step becomes without finiteness, namely the defect of P
  subexp-amenable-cd-two-kropholler-iff-no-intermediate-growth: that reduces the NFS case to intermediate growth by Rosset kernels; this gives the invariant that an intermediate-growth group of cd 2 would have to violate, namely D = 1 + b_2 >= 1 on every finite-index subgroup
---

**ESTABLISHED** (proposed; referee pending) through
`amenable-cd-two-bass-defect-equals-euler-char-proof`, from
`amenable-fp-iff-affiliated-top-homology-vanishes` (imports (J1)–(J3), (J6)),
`amenable-cd-two-kropholler-iff-locally-indicable` (items 1, 2 and 3(i)),
`l2-small-projectives-with-rank-gap-are-finitely-generated` (item 3),
`subexp-amenable-cd-two-kropholler-iff-no-intermediate-growth` (item 1, only for item 3(c)),
and recalled imports: the Bass conjecture for amenable groups (Berrick–Chatterji–Mislin), Bass's
theorem that big projectives over commutative noetherian connected rings are free, and the
structure of the Hantzsche–Wendt group.

**Notation.** `U = U(G)`. Modules are left modules and `⊗ = ⊗_{Z[G]}`. `b_i = dim_Q H_i(G; Q)`.
For a `Z[G]`-module `M` with `dim_U(U ⊗ M) < ∞`, its **Bass defect** is

> `D(M) = rank_Q(Q ⊗ M) − dim_U(U ⊗ M)  ∈ R ∪ {+∞}`.

For a finitely generated projective `M` over a torsion-free amenable group, `D(M) = 0`. This is
the weak Bass conjecture, known for amenable groups (Berrick–Chatterji–Mislin). A presentation
of `G` on `n` generators gives the **relation module** `P = ker(Z[G]^n → Z[G], e_i ↦ x_i − 1)`.
When `cd_Z G <= 2`, `P` is a countably generated projective module.

1. **Defect identity.** Let `G` be infinite, finitely generated and amenable, with `cd_Z G <= 2`.
   For every finite generating set,

   > `dim_U(U ⊗ P) = n − 1`, `rank_Q(Q ⊗ P) = n − b_1 + b_2`, so `D(P) = χ_Q(G) := 1 − b_1 + b_2`.

   In particular `D(P)` does not depend on the presentation. It is `+∞` exactly when
   `b_2 = ∞`. More generally, let `G` be any finitely generated group with `cd_R G <= 2`, where
   `R = Z` or `Q`, and take the relation module over `R[G]`. If `b_2^(2)(G) < ∞`, then
   `D(P) = χ_Q(G) − χ^(2)(G)`, where `χ^(2) = b_0^(2) − b_1^(2) + b_2^(2)`.
2. **Equivalence (both directions).** The following are equivalent.
   - (a) Kropholler's question in dimension at most 2 (every amenable group of `cd_Z <= 2` is
     elementary amenable). Equivalently, the target `amenable-cd-two-groups-have-an-l2-rank-gap`.
   - (b) `b_1(G) = 1 + b_2(G)` for every infinite finitely generated amenable `G` with
     `cd_Z G <= 2`.
   - (c) `χ_Q(G) <= 0` for every such `G`.
   - (d) For every such `G` and one (equivalently every) finite generating set, the relation
     module satisfies the weak Bass inequality `rank_Q(Q ⊗ P) <= dim_U(U ⊗ P)`.
3. **Where the defect sits in a counterexample.** Suppose (a) fails. Let `K` be a finitely generated
   counterexample with finite abelianization (item 3(i) of the LI node), `n` generators, relation
   module `P`.
   - (a) `D(P) = 1 + b_2(K) >= 1`, while `dim_U(U ⊗ P) = n − 1`.
   - (b) Write `P = P_0 ⊕ P'` as in item 3 of the L2-small node: `P_0` is finitely generated and
     `P'` has no nonzero finitely generated direct summand. Then `D(P_0) = 0`, and `P'` carries
     the whole defect:
     `dim_U(U ⊗ P') = n − 1 − s` is an integer `>= 1` (where `s = dim_U(U ⊗ P_0) <= n − 2`), and
     `rank_Q(Q ⊗ P') = n − s + b_2(K)`.
   - (c) If `K` has no free subsemigroup (for instance if `K` has intermediate growth), then every
     finite-index subgroup `N` has `D(res_N P) = χ_Q(N) = 1 + b_2(N) >= 1`.

   Hence (a) follows from the open statement
   `l2-finite-projectives-over-amenable-groups-satisfy-weak-bass`, the weak Bass inequality for
   countably generated projectives of finite `L²`-dimension over torsion-free amenable groups.
   It only needs the case of a finitely generated group of cd 2 with finite abelianization and a
   module with no finitely generated summand. This direction only: (a) is not known to imply
   that statement for modules other than relation modules.
4. **Obstruction A: finite truncations and specialization ranks.** Let `G` be any infinite
   finitely generated group with `b_1(G) = 0`, and fix `n` generators. Then finitely many relators
   have a Fox matrix `J ∈ M_{k×n}(Z[G])` with

   > `rank_Q ε(J) = n > n − 1 >= rank_U(J)`.

   The Hantzsche–Wendt group `HW` is such a `G`: it is torsion-free, amenable (virtually `Z³`) and
   has `b_1 = 0`. So no inequality `rank_Q ε(A) <= rank_U(A)` holds for all matrices `A` over
   `Z[G]` when `G` is torsion-free amenable. In a counterexample `K`, the defect is already visible
   on the Fox rows of finitely many relators, and that finite configuration also occurs in `HW`,
   where nothing is wrong. So an argument that uses only finitely many relators, together with
   torsion-freeness, amenability and ranks over `U` and `Q`, fails. The exact failing step is the
   termwise comparison `rank ε(J_k) <= rank_U(J_k)` on truncations. The input that separates `K`
   from `HW` is the projectivity of the whole infinite module `P` (`cd 2` against `cd 3`).
5. **Obstruction B: flatness does not suffice.** Let `J` be as in item 4 for `G = HW`, put
   `B = J^* J ∈ M_n(Z[G])`, and let
   `M_B = colim(Z[G]^n →·B Z[G]^n →·B ⋯)`. Then `M_B` is a countably generated flat
   `Z[HW]`-module with

   > `rank_Q(Q ⊗ M_B) = n`, `dim_U(U ⊗ M_B) = n − 1`, so `D(M_B) = 1`,

   and `M_B` is not projective. So the inequality `D <= 0` fails for countably generated flat
   modules of finite `L²`-dimension over torsion-free amenable groups. Any proof of item 2(d), or
   of the open statement of item 3, must use projectivity beyond flatness. This kills three kinds
   of argument:
   - Lazard–Govorov arguments, which write `P` as a colimit of finitely generated free modules and
     pass to the limit;
   - Følner or ball truncations of a colimit presentation;
   - any argument that sees `P` only through its finitely generated submodules.

   The failing step is the passage from a colimit of free modules to a direct summand of a free
   module. There the Hattori–Stallings trace, which makes `D = 0` for finitely generated
   summands, is not defined.
6. **Obstruction C: `L²` data are blind to the defect.** For every infinite amenable `G` with
   `cd_Z G <= 2` and every `n`, the `U`-dimensions along `0 → P → Z[G]^n → Z[G] → Z → 0` are
   `(n − 1, n, 1)`, and all `L²`-homology has dimension 0. This is the same profile as `Z²` on `n`
   generators. For amenable `G`, Følner and ball counts of cells compute only these
   `U`-dimensions (Elek; recalled). So an argument from `L²`-Betti vanishing, the Euler
   characteristic and growth of the cellular chain complex gives exactly the identity of item 1,
   and no bound on `b_2`. Degrijse's Euler-characteristic step (`χ = χ^(2)`, used for type `FP`
   in `amenable-fp-iff-affiliated-top-homology-vanishes`) is literally the statement `D(P) = 0`.
   Without finite generation of `P`, that is item 2(d) itself.

**Calibrations.**

- `Z`, `Z²`, `Kb`, `BS(1,m)`: `χ_Q = 0`, so `D(P) = 0`, as item 2 requires. For `m ≠ 1`,
  `BS(1,m)` has `b_1 = 1` and `b_2 = 0`; `Z²` has `b_1 = 2` and `b_2 = 1`.
- **Finite groups over `Q`** (`cd_Q = 0`): `D(P) = 1 − 1/|G| > 0`, and `(Q_ab)` fails for
  perfect finite groups. Torsion-freeness is necessary. This is why the open statement of
  item 3 is posed for torsion-free groups.
- **`Z/2 ≀ Z` over `Q`** (`cd_Q = 2`, thin idempotents): `b_1 = 1` and `b_2 = 0`, so `D = 0`.
  The defect sees the abelianization, not the zero divisors.
- **Hantzsche–Wendt, dimension 3.** Its relation module is not projective. The analogue of
  (c) ⇒ (b) fails: `χ_Q = 1 − 0 + 0 − 1 = 0` but `b_1 = 0`. In dimension 2 the top Betti
  number enters with a plus sign, which is what makes (c) ⇒ (a) work. `HW` also realises items 4
  and 5.
- **Consistency with `FP_2`.** If `P` is finitely generated, then `D(P) = 0` by the weak Bass
  conjecture, and a group with finite abelianization would have `1 + b_2 = 0`, which is
  impossible. This re-proves, for groups with finite abelianization, that a counterexample is
  never `FP_2`.

**What this changes.** The brief's route, "`L²`-Betti vanishing plus Euler characteristic
forcing `b_2` control", is shown to be exactly equivalent to the target (item 2), and item 6
locates its only content. What remains is one weak-Bass inequality for countably generated
projectives of finite `L²`-dimension, a question about projective modules with no group theory in
it. Items 4 and 5 show that a proof of it must use projectivity itself: finite truncations and
flatness are both refuted by `HW`.
