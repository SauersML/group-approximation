# BNSR invariants of pure braid groups: pencil characters and higher resonance (2026-09-13)

Lane z1-09-pure-braid. Continues `zp-pure-braid-bnsr-middle-range-2026-09-13.md`. The data in
Section 3 are computational evidence (random points, arithmetic mod `p = 2^31 - 1`), not proofs.

## 1. Symmetric coordinates on the (n+1) punctures

`H_n = P_n / Z(P_n) = PMod(S_{0,n+1})`. Label the punctures `1, ..., n, n+1` (`n+1 = infinity`). For
`s != t`, let `T_{st}` be a Dehn twist about a curve bounding a disc containing exactly punctures `s, t`.
Two such curves differ by a pure mapping class (both sides carry the same labelled punctures), so
`T_{st}` is well defined in `H_1(H_n)`. A character is recorded as `c_{st} = chi(T_{st})`.

- Relations: the twist about a curve around a set `S` is `sum_{pairs in S} T_{pair}` in homology
  (abelianization of `P_n`: `A_S = sum_{i<j in S} A_{ij}`). The twist around all punctures but one is trivial.
  So every row sum vanishes: `sum_{t != s} c_{st} = 0`. Counting gives `binom(n+1,2) - (n+1) = binom(n,2) - 1`,
  the rank of `H_1(H_n)`.
- Dictionary with `P_n`: `A_{ij} -> T_{ij}` for `i, j <= n`, so `c_{ij} = a_{ij}` (zero-sum `chi`), and
  `c_{i,n+1} = -sum_{j != i, j <= n} a_{ij}`.
- Symmetry: `Mod(S_{0,n+1})` contains `H_n` as a normal subgroup with quotient `S_{n+1}`. Conjugation permutes
  twist classes, `T_{st} -> T_{sigma(s) sigma(t)}`, so `S_{n+1}` acts on characters by permuting indices.
  BNSR invariants are invariant under automorphisms (Zaremsky arXiv:1507.08597, p. 4), so each
  `Sigma^m(H_n)` is `S_{n+1}`-invariant.
- For `U <= [n+1]` let `L_U` be the characters supported on pairs inside `U` with all row sums zero
  (`dim L_U = binom(|U|,2) - |U|`). This is the pullback along the forgetful map `M_{0,n+1} -> M_{0,U}`.
  `|U| = 4` gives the 2-dimensional pencil planes: `binom(n+1,4) = binom(n,3) + binom(n,4)` of them, the KMM
  circles (`U` containing `n+1` gives a `P_3`-circle, otherwise a `P_4`-circle).

## 2. Theorem P' (sunflowers)

Let `U_1, ..., U_r <= [n+1]` with `|U_i| >= 4` and `U_i ∩ U_j = {p}` for all `i != j`, for one fixed puncture `p`.
Let `D = sum_i (|U_i| - 3)`. Every nonzero character in `L_{U_1} + ... + L_{U_r}` lies outside `Sigma^D(H_n)`,
and its pullback to `P_n` lies outside `Sigma^D(P_n)`.

*Proof.* Choose `sigma in S_{n+1}` with `sigma(p) = n+1`. Then `sigma(U_i) = A_i ∪ {n+1}` with pairwise disjoint
`A_i <= [n]`, `|A_i| = |U_i| - 1 >= 3`. By the dictionary, `L_{A_i ∪ {n+1}}` consists of the zero-sum characters
of `P_n` supported inside `A_i`. Theorem P (middle-range artifact, Section A) gives non-membership in
`Sigma^D(P_n)` with `D = sum(|A_i| - 2)`, hence in `Sigma^D(H_n)` (split projection, Meinert 2.8). The symmetry
moves this back to `U_i`. □

For `n = 5`, `D = 2`: the six 5-subsets `U` of `[6]` give 5-dimensional subspaces `L_U` outside `Sigma^2`. Five
of them are the zero-sum 4-strand characters; the sixth is `{chi : every row sum of a is 0}`.

## 3. Computations (braid arrangement `A_4`, `n = 5`; script os_resonance.py / os_resonance2.py)

The Orlik–Solomon algebra uses the NBC basis (one edge `e_{ij}`, `i < j`, per top vertex `j`) with the Arnold
rewriting `e_{ik} e_{jk} = e_{ij} e_{jk} - e_{ij} e_{ik}`. Betti numbers `1, 10, 35, 50, 24`. Sanity checks
passed: a generic character gives an exact complex; a generic zero-sum character gives `H^3 = H^4 = 6 = |chi(H_5)|`;
a KMM circle gives `H^1 = 1`.

Degree <= 2 (for `P_5 = H_5 x Z` with zero-sum `a`, `H^2(P_5, a) = H^2(H_5, a) + H^1(H_5, a)`):

| character family (random point) | `(H^0, H^1, H^2)` | count |
|---|---|---|
| single plane `L_U`, `|U| = 4` | (0, 1, 8) | – |
| `L_U`, `|U| = 5` (all six) | (0, 0, 2) | – |
| `L_{U1} + L_{U2}`, `|U1 ∩ U2| = 3` (inside a 5-set) | (0, 0, 2) | 60 |
| `L_{U1} + L_{U2}`, `|U1 ∩ U2| = 2` | (0, 0, **1**) | 45 |
| three planes inside a common 5-set | (0, 0, 2) | 60 |
| three planes not inside a 5-set | (0, 0, 0) | 395 |
| `L_U` (`|U| = 5`) + plane not inside `U` | (0, 0, 0) | 60 |
| exactly one negative coefficient (Zaremsky Prop. 5.6) | (0, 0, 0) | – |
| generic point of `{a_S = 0 : S in family} ∩ {zero sum}`, up to 3 conditions | (0, 0, 0) | all |

**Finding.** Two pencil planes meeting in exactly two punctures are resonant in degree 2, and they are not
inside any `L_U` with `|U| = 5`. The prediction "`R^2(H_5)` is the six `L_U` with `|U| = 5`" recorded in the
middle-range artifact (E.1) and in the conjecture node was incomplete. The data are consistent with
`R^2(H_5) = (six 5-dimensional L_U) ∪ (45 four-dimensional L_{U1} + L_{U2}, |U1 ∩ U2| = 2)`.

## 4. The degree-2 cocycle for two meeting pencils

Components of `R^1` of an arrangement are isotropic (`L ∧ L = 0` in `A^2`; for a triple point this is the OS
relation). Let `a = b_1 + b_2` with `b_i in L_{U_i}`, and let `b_i^⊥ in L_{U_i}` be independent of `b_i`. Then
`a ∧ (b_1^⊥ ∧ b_2^⊥) = b_1 ∧ b_1^⊥ ∧ b_2^⊥ + b_2 ∧ b_1^⊥ ∧ b_2^⊥ = 0` by isotropy. The other products are
coboundaries: `b_1 ∧ b_2' = a ∧ b_2'` and `b_1' ∧ b_2 = -a ∧ b_1'`. So `H^2(A, a) != 0` exactly when
`b_1^⊥ ∧ b_2^⊥ notin a ∧ A^1`. The computation shows this for `|U1 ∩ U2| = 2`; an exact certificate (a linear
functional killing `a ∧ A^1` but not `b_1^⊥ ∧ b_2^⊥`, for all parameters) is still to be written.

Consequence once resonance is certified: by the resonance upper bound
(`arrangement-bnsr-invariants-avoid-real-resonance`, degree 2), those characters lie outside `Sigma^2(P_5)`.
They pull back to every `P_n`, `n >= 5`, along forgetful maps (split, Meinert 2.8). Unlike Theorems P and P',
this is not explained by a split quotient: the two pencils share two punctures, and the half-plane layering
fails because loops around a shared anchor must cross.

## 5. Refined conjecture: pencil depth

For a family `F = (U_1, ..., U_r)` of subsets of `[n+1]` with `|U_i| >= 4`, define
`depth(F) = min over set partitions π of F of sum_{blocks B of π} (|∪_{i in B} U_i| - 3)`.

**Conjecture PD.** `R^{<=m}(H_n; R)` is the union of the subspaces `L_{U_1} + ... + L_{U_r}` over families of depth
`<= m`, and (with Conjecture RS) `Sigma^m(P_n)` is the complement of their spheres together with `{sum a = 0}`
when `m >= n - 2`.

Checks. `m = 1`: single 4-sets (KMM). Top degree: `U = [n+1]`, depth `n - 2`. Sunflowers: depth
`sum(|U_i| - 3)`, matching Theorem P'. `n = 5`: pairs meeting in 2 have depth `min(2, 3) = 2`; triples of planes
not inside a 5-set have depth 3; a 5-set plus an outside plane has depth `min(3, 3) = 3`. All match Section 3.

`n = 6` (braid arrangement `A_5`, Betti `1, 15, 85, 225, 274, 120`; degrees <= 3; random points mod p):

| family on the 7 punctures | depth | `(H^0, H^1, H^2, H^3)` |
|---|---|---|
| single plane | 1 | (0, 1, 13, 59) |
| two disjoint triples `{1,2,3}`, `{4,5,6}` (sunflower, core 7) | 2 | (0, 0, 1, 11) |
| planes `{1234}`, `{3456}` (meet in 2) | 2 | (0, 0, 1, 13) |
| planes `{1234}`, `{3457}` (meet in 2) | 2 | (0, 0, 1, 13) |
| `L_{12345}` + plane `{4567}` (meet in 2) | 3 | (0, 0, 0, 2) |
| `L_{12345}` + plane `{1567}` (meet in 1) | 3 | (0, 0, 0, 2) |
| planes `{1234}`, `{3456}`, `{5612}` (pairwise meet in 2) | 3 | (0, 0, 0, 6) |
| `L_{123456}` | 3 | (0, 0, 0, 6) |

In every case the first nonzero `H^i` with `i >= 1` sits exactly at the predicted depth.

## 6. Exact certificate plan for Section 4

Rank semicontinuity gives a one-point certificate. The products `L_{U1} ∧ L_{U2}` are cocycles for every
parameter value (isotropy), and `rank(a ∧ A^1) <= 9` always. So if at one integer point
`rank_Q(a ∧ A^1 + L_{U1} ∧ L_{U2}) >= 10`, the same holds on a dense open set of parameters, giving `H^2 >= 1`
there, and closedness puts all of `L_{U1} + L_{U2}` in `R^2`. A nonzero minor mod p is a nonzero integer, so
modular rank suffices. Isotropy of the two planes is checked exactly over `Z`.
