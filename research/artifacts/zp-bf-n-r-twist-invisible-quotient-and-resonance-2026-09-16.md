# bF_{n,r}, full-twist-invisible characters: the first-leaf quotient, mirror symmetry, resonance data

Swarm lane zaremsky-2-13, 2026-09-16. Unreviewed. Part 4 of the bF_{n,r} series. Notation is from parts 1–3:
`zp-pure-braided-bht-characters-2026-09-13.md` (part 1), `zp-pure-braided-bht-sigma-2026-09-13.md` (part 2),
`zp-pure-braided-bht-roots-and-sigma1-2026-09-13.md` (part 3). Target hole:
`bf-n-r-twist-invisible-braid-characters-in-sigma-infinity`.

Status of this file:

- Proved here: Propositions 1, 2, 2', 4, 5, 6.
- Proposition 3 rests on two cited theorems. One was checked from the source text on 2026-09-16. The other was
  checked only as quoted in that source.
- Corollary 4.1 uses a standard theorem, cited without fetching the source in this session.
- §7 is computational evidence, and its certificate boundary is stated there.
- The hole stays open.

## 0. Conventions

- **Basic data.** `n >= 2`, `d = n - 1`, `A = Z[1/n]`, `res: A -> Z/d` (part 1, Lemma 1). `bF_{n,r} = N ⋊ F_{n,r}`,
  where `N` is the union of the groups `PB(T) = {(T, b, T)}` over forests `T`, and `s(T_-, T_+) = (T_-, 1, T_+)`.
- **Action convention.** `g = (T_-, T_+)` maps the leaves of `T_+` affinely onto the leaves of `T_-`. So
  `s(g) (T_+, b, T_+) s(g)^{-1} = (T_-, b, T_-)`, and composition of homeomorphisms matches multiplication.
- **Leaves.** The leaves of a forest with `k` leaves are the half-open intervals `I_j = [l_j, l_{j+1})`, with
  `l_1 = 0` and `I_k = [l_k, r)`. `res(l_j) = j - 1` (part 1, §1).
- **Winding coordinates.** `omega_{ij}: PB_k -> Z` is the coordinate of `A_{ij}` in `H_1(PB_k) = Z^{binom(k,2)}`.
  It is the winding number of `z_j - z_i` for a loop in `Conf_k(C)`.
- **Expansion.** Splitting leaf `i` cables strand `i` into `n` parallel strands `i_1, ..., i_n`, and
  `A_{ij} -> sum_s A_{i_s j}` in `H_1` (part 1, §3). Dually, `omega'_{i_s, j} = omega_{ij}`,
  `omega'_{i_s, i_t} = 0`, and all other coordinates are unchanged.
- **Characters.** `W = Hom(N, R)^{F_{n,r}}` is described by the free data of part 1, Theorem 1. `Phi_k(A_{ij}) =
  phi(type(i, j, k))`. `tau_phi(k) = sum_{i<j} Phi_k(A_{ij})`. `W_0 = {tau_phi(k) = 0 for all large k}`; since
  `tau_phi` is affine on `k >= 3` (part 1, Proposition 2), this means `tau_phi(k) = 0` for all `k >= 3`,
  `k ≡ r mod d`.
- `Omega = A ∩ (0, r)`.

## 1. The first-leaf quotient

**The module.** Let `M` be the group of right-continuous step functions `f: (0, r) -> Z` with finitely many
jumps, all at points of `Omega`, and with `f = 0` near `0`. `F_{n,r}` acts by `g·f = f o g^{-1}`. The functions
`e_x = 1_{[x, r)}` (`x` in `Omega`) form a `Z`-basis, via `f = sum_x (f(x) - f(x^-)) e_x`. Also
`g·e_x = e_{g(x)}`, since `g^{-1}(y) >= x` iff `y >= g(x)`. So `M = Z[Omega]` as a permutation module, and
`M ⋊ F_{n,r} = Z wr_Omega F_{n,r}` (restricted permutational wreath product).

**Proposition 1.** For a forest `T` with `k` leaves and `b` in `PB_k`, put
`m(T, b, T) = sum_{j=2}^{k} omega_{1j}(b) 1_{I_j}`. Then:

- `m: N -> M` is a well-defined, `F_{n,r}`-equivariant homomorphism;
- `Psi(nu · s(g)) = (m(nu), g)` is a surjective homomorphism `Psi: bF_{n,r} -> Z wr_Omega F_{n,r}` over `F_{n,r}`.

Concretely, `m(nu)(y)` is the winding number of the first strand around the strand whose leaf contains `y`.

*Proof.* (a) On each `PB(T)`, `m` is a homomorphism because the `omega_{1j}` are.

(b) Invariance under expansion of leaf `i`:

- If `i >= 2`, leaf `1` is unchanged. The new coordinates give `sum_s omega_{1i} 1_{I_{i_s}} = omega_{1i} 1_{I_i}`,
  because the pieces `I_{i_s}` partition `I_i`. The other terms are unchanged.
- If `i = 1`, the new first leaf is `I_{1_1}`. The pieces `1_t` (`t >= 2`) get coefficient `omega'_{1_1, 1_t} = 0`,
  and every old `j >= 2` keeps `omega_{1j}` and `I_j`.

So `m` is defined on the directed union `N`.

(c) Equivariance. `m(s(g) (T_+, b, T_+) s(g)^{-1}) = m(T_-, b, T_-) = sum_j omega_{1j}(b) 1_{g(I_j)}`, and
`1_{g(I)} = 1_I o g^{-1}`, since `g` is an increasing homeomorphism.

(d) `Psi` is a homomorphism: `(nu s(g))(nu' s(g')) = nu (s(g) nu' s(g)^{-1}) s(gg')` maps to
`(m(nu) + g·m(nu'), gg') = (m(nu), g)(m(nu'), g')`.

(e) Surjectivity. Given `x` in `Omega`, choose a forest in which `x = l_j` for some `j >= 2`. With
`b = A_{1j} A_{1,j+1} ... A_{1k}` we get `m = sum_{i >= j} 1_{I_i} = e_x`. Also `Psi(s(g)) = (0, g)`. ∎

**Lemma 2'.** Points `x, y` of `Omega` lie in one `F_{n,r}`-orbit iff `res x = res y`. Every residue class of
`Omega` is infinite.

*Proof.* Necessity: `res(g(x)) = res(g(x) - g(0)) = res(x)` by part 1, Lemma 1. Sufficiency: part 1, Lemma 2 maps
`[0, x]` onto `[0, y]` and `[x, r]` onto `[y, r]` (residues `res x` and `r - res x`); glue the two maps. The class
of `x` contains `x/n, x/n^2, ...`. ∎

So `Hom(Z wr_Omega F_{n,r}, R) = Hom(F_{n,r}, R) ⊕ {lambda_c}`, where `c: Z/d -> R` and `lambda_c(e_x) = c(res x)`.

## 2. First-leaf and last-leaf characters

**Proposition 2.** For `c: Z/d -> R` put `phi_c = lambda_c o m`, an element of `W`.

(i) `phi_c(A_{1j}) = c(j-1) - c(j)` for `2 <= j <= k-1`, `phi_c(A_{1k}) = c(k-1)`, and `phi_c(A_{ij}) = 0` for
`i >= 2`.

(ii) In the free data of part 1, Theorem 1:
- `EPP(gamma) = c(gamma+1) - c(gamma+2)`, `EPE = c(r-1)`, and `PPP = PPE = PEP = 0`;
- derived: `EEP = c(1) - c(2)`, `PEE = 0`, `EEE = c(r-1)`.

(iii) `c -> phi_c` is injective. Its image is `{phi in W : PPP = 0, PPE = 0, PEP = 0}`, of dimension `d`.

(iv) `tau_{phi_c}(k) = c(1)` for every `k`. So `phi_c` lies in `W_0` iff `c(1) = 0`, and the first-leaf part of
`W_0` has dimension `d - 1`.

*Proof.*

(i) `1_{I_j} = e_{l_j} - e_{l_{j+1}}` for `j < k`, `1_{I_k} = e_{l_k}`, and `res(l_j) = j - 1`.

(ii) For the pair `(1, j)`, the gap `A` is exact; `G` is exact iff `j = 2`, otherwise `gamma = j - 2`; `B` is
exact iff `j = k`; and `k ≡ r`. The derived formula `EEP = EPP(0) + PEP(0) - PPP(0,0)` gives `c(1) - c(2)`,
which matches. `EPP` has sum zero.

(iii) If `PPP = PPE = PEP = 0`, the data reduce to `EPP` (sum zero) and `EPE`, a space of dimension `d`. If
`EPP = 0` then `c` is constant, and then `EPE = c(r-1) = 0` forces `c = 0`. So the map is injective between
spaces of equal dimension.

(iv) `sum_{j=2}^{k-1} (c(j-1) - c(j)) + c(k-1) = c(1)`. ∎

**Proposition 2' (last leaf).** Use left-open leaves `(l_j, l_{j+1}]`, the module of left-continuous step
functions vanishing near `r` with basis `1_{(0,x]}`, and `m'(T, b, T) = sum_{j<k} omega_{jk}(b) 1_{(l_j, l_{j+1}]}`.
The same proof gives an equivariant `m'` and characters `phi'_{c'}` with:

- values: `phi'(A_{jk}) = c'(j) - c'(j-1)` for `2 <= j <= k-1`, `phi'(A_{1k}) = c'(1)`, and zero on pairs not
  involving strand `k`;
- data: `PPE(alpha) = c'(alpha+1) - c'(alpha)`, `EPE = c'(1)`, `EPP = PPP = PEP = 0`, `PEE = c'(r-1) - c'(r-2)`,
  `EEP = 0`;
- `tau = c'(r-1)`.

The first-leaf and last-leaf subspaces meet in the line of pure `EPE` data, where `tau = EPE`. So their
`W_0`-parts meet in `0` and span a `2(d-1)`-dimensional subspace of `W_0` (`dim W_0 = d^2 + d - 2`). ∎

For `n = 3` the first-leaf part of `W_0` is the line `c = (1, 0)`: `phi(A_{1j}) = (-1)^{j+1}` for `j < k`, and
`phi(A_{1k}) = c(k-1)`.

## 3. The quotient is finitely presented and its lamp characters lie in Sigma^2

**Proposition 3.** (a) `Z wr_Omega F_{n,r}` is finitely presented. (b) For every `c != 0` and every
`psi` in `Hom(F_{n,r}, R)`, the character `lambda_c + psi o pr` lies in `Sigma^2(Z wr_Omega F_{n,r})`.

*Proof.* (a) We use Cornulier's criterion [C06], as quoted in [M18, §6]: "a wreath product H wr_X G is finitely
presented if and only if G and H are finitely presented, G acts diagonally on X^2 with finitely many orbits and
the stabilizers of the G-action on X are finitely generated." Take `H = Z` and `X = Omega`.

- `F_{n,r}` is finitely presented: Brown 1987, or part 3, Lemma 6 together with `F_{n,1}`.
- Orbits on `Omega^2`:
  - the diagonal has `d` orbits (Lemma 2');
  - pairs `x < y` with equal `res x` and `res(y - x)` lie in one orbit (part 1, Lemma 2 on `[0, x]`, `[x, y]`,
    `[y, r]`, glued), giving at most `d^2` orbits;
  - the same bound holds for `x > y`.
- Stabilizers: `Stab(x) = F_{[0,x]} × F_{[x,r]}`, where `F_{[u,v]}` is the group of PL homeomorphisms of `[u, v]`
  with slopes in `<n>` and breakpoints in `A`. Part 1, Lemma 2 gives such a homeomorphism `h: [0, x] -> [0, r_1]`
  with `r_1` in `{1, ..., d}` and `r_1 ≡ res x`. Conjugation by `h` is an isomorphism `F_{[0,x]} -> F_{n,r_1}`.
  Likewise `F_{[x,r]} ≅ F_{n,r_2}`. Both groups are finitely generated.

(b) [M18, Theorem B], checked from the arXiv PDF on 2026-09-16: "Let Γ = H wr_X G be a finitely presented
wreath product and let χ: Γ → R be a non-trivial character. If the set T = {x ∈ X | χ|H_x ≠ 0} has at least 3
elements, then [χ] ∈ Σ^2(Γ)." Here `T = {x : c(res x) != 0}` is a nonempty union of residue classes, so it is
infinite by Lemma 2'. ∎

**Remark 3.1 (what Proposition 3 does and does not give).**

- It removes the analogy in the target hole's caution. `Z wr Z` is not finitely presented, and its base characters
  miss `Sigma^2`. The quotient here is finitely presented, and every lamp character lies in `Sigma^2`. So this
  quotient gives no `Sigma^2` obstruction for first-leaf characters.
- Membership does not pass from a quotient up to the group (for example `F_2 -> Z`), so (b) is not evidence for
  membership in `Sigma^2(bF_{n,r})`. Holes pass up only along split quotients (Meinert; T3 of part 2).
- `Sigma^m(Z wr_Omega F_{n,r})` for `m >= 3` is not determined here.

**Remark 3.2 (splitting of Psi is open).** The natural lift of `e_x` uses a forest with `x = l_j`:

`D_x = (T, Delta^2_k · (Delta^2_{[1, j-1]})^{-1} · (Delta^2_{[j, k]})^{-1}, T)`,

where `Delta^2_{[a,b]}` is the full twist on strands `a..b`. The three twists commute. This lift has three good
properties:

- It is compatible with expansion. Cabling a strand inside a full twist multiplies it by the inverse block twist
  (part 1, Proposition 2, proof), and the correction appears in `Delta^2_k` and in exactly one block twist, so it
  cancels.
- It is equivariant: `s(g) D_x s(g)^{-1} = D_{g(x)}`.
- It lifts `e_x`: `m(D_x) = e_x`, since `omega_{1i}(D_x) = 1 - [i <= j-1]`.

It is still not a splitting. Take `k = 3`, `x = l_2`, `y = l_3`; for example `n = 3`, `r = 1`, and one caret.
Then `D_x = Delta^2 A_{23}^{-1}` and `D_y = Delta^2 A_{12}^{-1}`. These commute iff `A_{12}` and `A_{23}` commute.
But their images generate `PB_3 / Z(PB_3) ≅ F_2`, hence freely. I have neither a splitting nor a proof that none
exists. The caution calls the quotient non-split; that is not verified here. Even with a splitting, Meinert's
criterion would transfer only holes, and by Proposition 3 there are none at `m <= 2`.

## 4. Mirror symmetry

**Proposition 4.** Complex conjugation on configuration spaces induces an involutive automorphism `mu` of
`bF_{n,r}` with `mu o s = s` and `mu^*(pi^* psi + phi) = pi^* psi - phi` for `phi` in `W`. Hence, for every `m`,

`[pi^* psi + phi]` lies in `Sigma^m(bF_{n,r})` iff `[pi^* psi - phi]` does.

*Proof.* Represent `b` in `PB_k` by a loop in `Conf_k(C)` based at the real configuration `(1, ..., k)`.

- Complex conjugation fixes the base point and induces `sigma_i -> sigma_i^{-1}`, an automorphism of `B_k`
  preserving `PB_k`. Write `b -> b-bar`.
- It negates every winding number of `z_j - z_i`, so `omega_{ij}(b-bar) = -omega_{ij}(b)`.
- Cabling strand `i` replaces `z_i` by `z_i + epsilon t_s` with real `0 = t_1 < ... < t_n` and `epsilon` small.
  This is the blackboard cabling of part 1, §3, and conjugation commutes with it.

So `mu(T_-, b, T_+) = (T_-, b-bar, T_+)` respects expansion. It is multiplicative because
`(T_-, b, T)(T, b', T_+) = (T_-, b b', T_+)` after common expansion. It is an involution and fixes `s(F_{n,r})`.
Every `phi` in `W` factors through `H_1(N) = colim H_1(PB(T))`, so `phi o mu = -phi` on `N`, while `pi o mu = pi`.
BNSR invariants are invariant under automorphisms. ∎

**Corollary 4.1.** Let `phi` in `W` have cyclic image. Then `ker phi` is of type `F_m` iff `[phi]` lies in
`Sigma^m(bF_{n,r})`. So the case `psi = 0`, `phi` rational in `W_0 \ {0}`, of the target hole is equivalent to:
`ker phi` is of type `F_infinity`.

*Proof.* `bF_{n,r}` is of type `F_infinity` (Skipper–Wu, arXiv:2103.14589, as used in part 2). For a group of type
`F_m` and a discrete character `chi`, `ker chi` is of type `F_m` iff `[chi]` and `[-chi]` both lie in `Sigma^m`
(Bieri–Renz 1988 in the homological setting, Renz in the homotopical one; standard, not re-fetched in this
session). Apply Proposition 4 with `psi = 0`. ∎

## 5. A pencil-depth bound for first-leaf characters

**Coordinates.** We use the symmetric coordinates on the `k + 1` punctures, `infinity = k + 1` (pencils artifact
`zp-pure-braid-bnsr-pencils-2026-09-13.md`, §1). A zero-sum character of `P_k` is recorded as `c_{ij} = a_{ij}`
and `c_{i,infinity} = -sum_{j != i} a_{ij}`. `L_U` is the space of characters supported on pairs inside `U` with
all row sums zero.

For `phi_c` with `c(1) = 0`, write `a_j = Phi_k(A_{1j})`. The coordinates are:

- `c_{1j} = a_j`;
- `c_{j,infinity} = -a_j` for `j >= 2`;
- `c_{1,infinity} = -sum_j a_j = 0`;
- all other `c_{st} = 0`.

Let `S = {j : a_j != 0}` and `s = |S|`. Among `2 <= j <= k-1`, every run of `d` consecutive `j` contains all
cyclic differences `c(t-1) - c(t)`. They sum to `0` and are not all `0`, because `c` is nonconstant. So
`s >= 2 floor((k-2)/d)`.

**Proposition 5 (depth bound).** Let `U_1, ..., U_q` be subsets of `[k+1]` with `|U_i| >= 4`, and suppose the
character above lies in `L_{U_1} + ... + L_{U_q}`. Then every set partition of the family into blocks `B`, with
unions `V_B`, satisfies `sum_B (|V_B| - 3) >= s/2`. So the family has pencil depth at least `s/2`, in the sense of
`braid-arrangement-higher-resonance-varieties-computed`.

Equality is attained whenever the nonzero `a_j` can be paired as `a_j = -a_{j'}`. Then the `s/2` petals
`{1, j, j', infinity}` pairwise meet in `{1, infinity}`, the character is their sum, and the partition into
singletons costs `s/2`.

*Proof.* Every support edge lies in some `U_i`, hence in some `V_B`. The support edges are `{1, j}` and
`{j, infinity}` for `j` in `S`, `2s` in all. Count the support edges inside a block `V` with `v = |V| >= 4`:

- if `1, infinity` are both in `V`: at most `2(v - 2)`;
- if exactly one is: at most `v - 1`;
- if neither is: `0`.

Each bound is at most `4(v - 3)` for `v >= 4`. So `2s <= 4 sum_B (|V_B| - 3)`.

For the equality statement, a petal's restriction has `c_{1j} = a`, `c_{j,infinity} = -a`, `c_{1j'} = -a`,
`c_{j',infinity} = a`, and it has zero row sums. ∎

**Consequences and limits.**

- *Conditional.* The pencil-depth formula is not proved. Its "no other components" direction would give
  `Phi_k ∉ R^{<=m}(P_k)` for `m < s/2`. With `pure-braid-bnsr-complements-are-real-resonance-varieties`, that gives
  `[Phi_k]` in `Sigma^m(P_k)` for `m < s/2`. Since `s -> infinity`, part 2, Lemma 5 would then put
  `[pi^* psi + phi_c]` in `Sigma^infinity(bF_{n,r})`.
- *Unconditional upper limit.* The character lies in `L_U` with `U = S ∪ {1, infinity}`, so
  `pure-braid-sunflower-characters-obstruct-bnsr-invariants` (one petal) gives `[Phi_k] ∉ Sigma^{s-1}(P_k)`. Any
  proof must use `k -> infinity`; no fixed `k` suffices.

## 6. Interval twists vanish identically on W_0

**Proposition 6.** Let `phi` in `W_0`, `k ≡ r mod d`, and let `S = {i, i+1, ..., i + td}` be an interval of
strands with `t >= 1` and `k - td >= 3`. Then `w(S) := sum_{p<q in S} Phi_k(A_{pq}) = 0`.

*Proof.* The functions `Phi_k` and `tau_phi` depend on `r` only through `r mod d` (part 1, Theorem 1: the data and
derived formulas are indexed by residues). So we may assume `r <= d`, and then a forest `T''` with `k' = k - td`
leaves exists, since `k' >= 3` and `k' ≡ r`.

Expand leaf `i` of `T''` `t` times, each time at a leaf descending from leaf `i`. This gives a forest `T` whose
leaves `i, ..., i + td` are the descendants of leaf `i`. In `H_1`, the full twist of `T''` becomes
`Delta^2_k (Delta^2_S)^{-1}`, since pairs inside the bundle get winding `0` and all other pairs get `1`. Types
depend only on `(p, q, k)`. Hence `tau_phi(k') = tau_phi(k) - w(S)`, and both `tau` values vanish on `W_0`. ∎

**Consequence.** On `M_{0,k+1}` (punctures `[k+1]`, `infinity = k+1`), the dense edges of the braid arrangement
are the subsets `U ⊆ [k+1]` with `2 <= |U| <= k-1`, of codimension `|U| - 1`. Their weight is the sum of the
symmetric coordinates over pairs inside `U`. Because all row sums are zero, `U` and its complement have the same
weight. For `U ⊆ [k]` the weight is `w(U)`.

So Proposition 6 makes the weight vanish on every interval `S = {i, ..., i+d}`, a dense edge of codimension `d`, for
every `phi` in `W_0` and every `k >= n + 2`. By the complement symmetry the same holds for `[k+1] \ S`. For large
`k`, and any two given punctures `p, q`, some such interval avoids both, so its complement is a zero-weight dense
edge containing `p` and `q`.

Nonresonance vanishing theorems for Aomoto complexes (Yuzvinsky type) need nonzero weights on dense edges. Some
versions test all dense edges, and some test only the edges contained in a chosen hyperplane at infinity
`H_{pq}`, that is, the `U ⊇ {p, q}`. Both hypotheses fail for every `phi` in `W_0` once `k ≡ r` is large
(`k >= 3n + 2` suffices):

- the first kind fails at an interval `S`;
- the second kind fails at `[k+1] \ S`, for an interval `S` avoiding `p` and `q`.

So these theorems cannot apply to any `phi` in `W_0`. I have not examined codimension-filtered variants, which
test only low-codimension edges and conclude vanishing only in low degrees. The interval edges have codimension
`d`, so the first kind of hypothesis already fails in codimension `d`.

This kills the generic-weight route to the claim `bf-n-r-twist-invisible-restrictions-nonresonant`. It is not an
obstruction to that claim.

Numerical confirmation is in `dense_edge_sums.py` (§7). For `n = 4` and `k <= 12` (`r = 1, 2, 3`), the subsets
with `w(S) = 0` at every sampled random point of `W_0` are exactly the intervals of length `≡ 1 mod d`. For `n = 3`
there are further, non-interval zero-weight subsets from `k = 10` (`r = 2`, for example `{2, 4, 6, 9}` and
`{2, 5, 7, 9}`) and `k = 11` (`r = 1`). *(Referee correction, 2026-09-16: an earlier version said "coincidental
subsets once `k >= 11`". For `n = 3` the four sampled points span `W_0`, which has dimension 4, so these subsets have
weight zero identically on `W_0`; they are not coincidental. The `zero_at_every_point` lists in the JSON are
truncated at 20 entries; the `count_zero_at_every_point` field is the full count.)*

*Caveat.* The precise hypotheses of the Yuzvinsky and Cohen–Dimca–Orlik vanishing theorems were not re-read for this
artifact (only the abstract of arXiv:math/0210409 was checked). The argument above shows that both usual forms of
the weight hypothesis fail on `W_0`. A variant with a different hypothesis would need a separate check.

## 7. Computation

**Where.** `experiments/zp-bf-n-r-first-leaf-star-resonance-2026-09-16/`. The script `os_resonance_bf.py`
(stages `main` and `deep`) writes `results.json` and `results_deep.json`. `dense_edge_sums.py` writes
`dense_edge_sums.json`.

**Method.**

- Orlik–Solomon algebra of the braid arrangement in the nbc normal form: monomials `e_{i_1 j_1} ... e_{i_p j_p}`
  with distinct columns, reduced by the Arnold relation.
- Aomoto differential `a ∧`, ranks by Gaussian elimination mod `p = 2^31 - 1` and `p = 10^9 + 7`.
- `Phi_k` is computed from Theorem 1 data.

**Sanity checks** (all pass):

- graded dimensions match the Stirling numbers for `k = 3..9`;
- `d^2 = 0` at random characters, `k = 4, 5, 6`;
- a positive character at `k = 5` gives an exact complex;
- a `P_3`-circle and a `P_4`-circle at `k = 4` give `H^1 = 1`;
- agreement with the repo's older implementation (`research/artifacts/zp-pure-braid-os-resonance-2026-09-13/`) at
  three random zero-sum characters, `k = 5`;
- random `W_0` data satisfy the cabling relations RI/RJ and `tau = 0` for `k <= 11`;
- the first-leaf formula of Proposition 2 and `tau = c(1)` hold.

**Certificate boundary.**

- Rank over `F_p` is at most rank over `Q` for an integer matrix, so `dim H^i` over `F_p` is at least `dim H^i`
  over `Q`. A reported `H^i = 0` is therefore exact over `Q` (and `R`), subject to the correctness of the code
  that the checks above test.
- A nonzero value is evidence only. Two primes agree in every two-prime case.
- None of this proves membership in `Sigma^m(P_k)`. That needs the open resonance conjecture.

**Results** (`dim H^0, ..., H^maxdeg` of `(A(P_k), Phi_k ∧)`; "fnz" = first nonzero degree):

| family | n | r | k | s | H^0..H^maxdeg | fnz |
|---|---|---|---|---|---|---|
| first-leaf c=(1,0) | 3 | 1 | 5 | 4 | 0,0,2,10,8 | 2 |
| first-leaf c=(1,0) | 3 | 1 | 7 | 6 | 0,0,0,6,72,246,180 | 3 |
| first-leaf c=(1,0) | 3 | 1 | 9 | 8 | 0,0,0,0 (one prime) | >= 4 |
| first-leaf c=(1,0) | 3 | 2 | 4 | 2 | 0,1,4,3 | 1 |
| first-leaf c=(1,0) | 3 | 2 | 6 | 4 | 0,0,2,20,58,40 | 2 |
| first-leaf c=(1,0) | 3 | 2 | 8 | 6 | 0,0,0,6,114 (H^4 one prime) | 3 |
| random W_0 point | 3 | 1 | 5 | – | 0,0,0,6,6 | 3 |
| random W_0 point | 3 | 1 | 7 | – | 0,0,0,0,0,120,120 | 5 |
| random W_0 point | 3 | 1 | 9 | – | 0,0,0 | >= 3 |
| random W_0 point | 3 | 2 | 4 | – | 0,0,2,2 | 2 |
| random W_0 point | 3 | 2 | 6 | – | 0,0,0,0,24,24 | 4 |
| random W_0 point | 3 | 2 | 8 | – | 0,0,0,0 | >= 4 |
| part-2 example ×2 | 3 | 1 | 5 | – | 0,0,0,6,6 | 3 |
| part-2 example ×2 | 3 | 1 | 7 | – | 0,0,0,0,0,120,120 | 5 |
| part-2 example ×2 | 3 | 1 | 9 | – | 0,0,0 | >= 3 |
| part-2 example ×2 | 3 | 2 | 4 | – | 0,1,4,3 | 1 |
| part-2 example ×2 | 3 | 2 | 6 | – | 0,0,1,13,47,35 | 2 |
| part-2 example ×2 | 3 | 2 | 8 | – | 0,0,0,0 | >= 4 |
| first-leaf c=(1,0,0) | 4 | 1 | 4 | 2 | 0,1,4,3 | 1 |
| first-leaf c=(1,0,0) | 4 | 1 | 7 | 4 | 0,0,2,32,178,388,240 | 2 |
| first-leaf c=(1,0,0) | 4 | 2 | 5 | 2 | 0,1,8,19,12 | 1 |
| first-leaf c=(1,0,0) | 4 | 2 | 8 | 4 | 0,0,2,46 | 2 |
| first-leaf c=(1,0,0) | 4 | 3 | 6 | 2 | 0,1,13,59,107,60 | 1 |
| first-leaf c=(1,0,0) | 4 | 3 | 9 | 4 | 0,0,2 | 2 |
| first-leaf c=(0,0,1) | 4 | 1 | 4 | 2 | 0,1,4,3 | 1 |
| first-leaf c=(0,0,1) | 4 | 1 | 7 | 4 | 0,0,2,32,178,388,240 | 2 |
| first-leaf c=(0,0,1) | 4 | 2 | 5 | 2 | 0,1,8,19,12 | 1 |
| first-leaf c=(0,0,1) | 4 | 2 | 8 | 4 | 0,0,2,46 | 2 |
| first-leaf c=(0,0,1) | 4 | 3 | 6 | 4 | 0,0,2,20,58,40 | 2 |
| first-leaf c=(0,0,1) | 4 | 3 | 9 | 6 | 0,0,0 | >= 3 |

The random `W_0` points use seed `20260916`; their values `Phi_k` are recorded in `results.json`. The part-2
example is scaled by 2: `PPP = 2(-1)^gamma`, `PEP = 1`, `EPE = 2` for odd `r` and `1` for even `r`.

**Observations** (evidence, not theorems):

1. *First-leaf characters.* In every computed case the first nonzero degree is `s/2`, with dimension `(s/2)!`
   (`1, 2, 6`). This matches Proposition 5. The exact vanishing below `s/2` is a certificate.
2. *Generic `W_0` points and the part-2 example with `r` odd.* The complexes are acyclic below degree `k - 2`, the
   top degree of `M_{0,k+1}`, where `dim = (k-2)!`. This is the behaviour of a generic zero-sum character.
3. *The part-2 example with `r` even.* It is resonant in degree `1` at `k = 4` and degree `2` at `k = 6`, and has
   `H^{<=3} = 0` at `k = 8`. The first resonant degree still grows.
4. No case shows a resonance degree that stays bounded as `k` grows. So the resonance upper bound gives no
   obstruction to the target hole in the computed range.

## 8. Approaches and where they die

- *Quotient transfer.* `Psi` gives no transfer at all without a splitting, and a splitting would transfer only holes,
  of which there are none at `m <= 2` (Proposition 3). Splitting is open (Remark 3.2).
- *Central elements.* `Phi_k` kills the full twist, the only central element of `PB_k` (as recorded on the hole).
- *Nonresonance vanishing theorems.* Their weight hypotheses fail identically on `W_0` (Proposition 6).
- *Fibration `P_k = F_{k-1} ⋊ P_{k-1}`.* The restriction to the free fibre is never in `Sigma^1(F_{k-1})`, which is
  empty for `k >= 3`. So the normal-subgroup transfer is unavailable in the direction needed.
- *Resonance route.* It needs the open conjecture `pure-braid-bnsr-complements-are-real-resonance-varieties` and
  eventual nonresonance (`bf-n-r-twist-invisible-restrictions-nonresonant`). Proposition 5 gives the combinatorial
  lower bound for first-leaf characters under the pencil-depth formula; the computations above support
  nonresonance in low degrees.

## References

- [C06] Y. de Cornulier, Finitely presented wreath products and double coset decompositions, Geom. Dedicata 122
  (2006). Not fetched; used only as quoted in [M18].
- [M18] L. A. de Mendonça, On the Σ-invariants of wreath products, arXiv:1709.06303 (v2, 28 Mar 2018; Pacific J.
  Math. 298 (2019)). PDF text checked 2026-09-16: Theorem B, and the finite-presentation criterion in §6.
- K. S. Brown, Finiteness properties of groups, J. Pure Appl. Algebra 44 (1987). Not re-fetched.
- D. C. Cohen, A. Dimca, P. Orlik, Nonresonance conditions for arrangements, arXiv:math/0210409. Abstract only
  checked; the theorem hypotheses were not re-read (unverified in detail).
- R. Skipper, X. Wu, arXiv:2103.14589 (type `F_infinity` of `bF_{n,r}`), as quoted in part 2.
- R. Bieri, B. Renz, Valuations on free resolutions and higher geometric invariants of groups, Comment. Math. Helv.
  63 (1988). Standard; not re-fetched.
- The repo's parts 1–3 and the pure-braid resonance artifacts named above.
