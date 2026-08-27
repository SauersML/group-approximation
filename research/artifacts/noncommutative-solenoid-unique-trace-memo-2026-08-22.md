# Noncommutative-solenoid unique-trace rigidity for the carrier's Heisenberg windows

Memo, 2026-08-22.  Lane: `non-hyperlinear-group` via
`hnn-carrier-factorial-character-collapse` (FC1) / `sl3-pair-relative-commutant-route` (RC3).
Deliverable of the "solenoid unique-trace" task.  All group-theoretic and
operator-algebraic proofs below are complete unless explicitly marked GAP or
OPEN; literature inputs are confined to Section D and were verified against the
sources named there.

**Headline results.**

1. **(Theorem A, established.)**  Complete classification of the traces of the
   `p`-solenoidal Heisenberg group `N = H_3(Z[1/p])`: a trace is canonical
   (vanishes off the center) exactly when its central spectral measure on the
   `p`-solenoid gives zero mass to the countable TORSION subgroup.  The fiber
   objects are Latremoliere--Packer noncommutative solenoids; the correct
   criterion is their APERIODICITY (= nontorsion), strictly weaker than the
   irrationality the task sheet anticipated — and the difference is exactly
   where the enemy lives (the leak's central marginal is supported on rational
   aperiodic points).

2. **(Transparency theorem, established.)**  No subgroup-local unique-trace or
   character-rigidity bridge can close (FC1): for the Heisenberg window
   `E_N = <N, t>` of the carrier — and for every window `<A, t>` with `A`
   amenable — there EXIST factorial hyperlinear characters with exactly the
   enemy's local shape (canonical aperiodic restriction, non-central letter).
   Built from an amenable wreath, so unconditional.  The minimal window this
   argument cannot reach is the `SL_2`-corner window, which is the rank-one
   carrier.

3. **(Rank-one window reduction, established.)**  Unconditionally:
   the rank-one vanishing-branch collapse (R1) below implies (FC1) for the
   `SL_3` carrier, hence (RC3), hence the goal.  The proof runs the enemy's
   restriction to the corner window through an ergodic decomposition, a
   Connes-embeddability-of-components lemma (proved), and Peterson--Thom
   character rigidity of `SL_2(Z[1/p])` (verified source).  This is a new
   arrow: the `n = 3` character problem is NOT harder than the rank-one one —
   an independent, purely subgroup-theoretic confirmation of the CORE A
   capstone, with a two-page proof in place of the Kostant cusp computation.

4. **(R1, OPEN, drafted as a node.)**  Every factorial hyperlinear character of
   `E_2 = < SL_2(Z[1/p]), s | [s, SL_2(Z)] = 1 >` whose `SL_2(Z[1/p])`-restriction
   vanishes off `{±I}` centralizes `s` against `SL_2(Z[1/p])`.

Notation for the whole memo: `p` a fixed prime;
`Gamma = SL_3(Z[1/p])`, `Lambda = SL_3(Z)`,
`H = < Gamma, t | [t, Lambda] = 1 >` the carrier;
`N = H_3(Z[1/p]) <= Gamma` upper unitriangular, with
`a(x) = e_12(x)`, `b(y) = e_23(y)`, `c(z) = e_13(z)`, `x, y, z in Z[1/p]`,
`[a(x), b(y)] = c(xy)`, `c` central; `N(Z) = N cap Lambda = H_3(Z)`.
Normal form `g(x,y,z) := a(x) b(y) c(z)`; the multiplication is

```text
g(x,y,z) g(x',y',z') = g(x+x', y+y', z+z'-x'y).            (M)
```

A *trace* on a discrete group is a normalized conjugation-invariant
positive-definite function; *character* = extremal trace; a trace/character is
*hyperlinear* when its GNS von Neumann algebra embeds trace-preservingly into
a tracial matrix ultraproduct (the lane's standing usage).

---

## Section A.  The torsion dichotomy for traces of `H_3(Z[1/p])`

### A.0  Duals, torsion, and the three central sectors

`S_p := dual of (Z[1/p], +)` is the `p`-solenoid, a compact connected abelian
group.  For `zeta in S_p` write `theta_n(zeta) in [0,1)` for the argument of
`zeta(p^-n)`; the compatibility `zeta(p^-n) = zeta(p^-(n+1))^p` says

```text
p * theta_(n+1) = theta_n  (mod 1),                        (Xi)
```

so `zeta <-> (theta_n)_n` identifies `S_p` with the parameter group `Xi_p` of
Latremoliere--Packer [LP, Thm 2.1] (their `Q_N`-adic notation with `N = p`).

Three central sectors:

- **Torsion** `T_p := Tors(S_p)`.  Multiplication by `p` is an automorphism of
  `Z[1/p]`, hence of `S_p`; so `S_p` has no `p`-torsion, and
  `T_p = { zeta : zeta^m = 1, gcd(m,p) = 1 } ~= directsum_(q != p) Z(q^infty)`,
  a countable subgroup.  `zeta` has order exactly `m` iff
  `ker zeta = m Z[1/p]` (a character of the cyclic group `Z[1/p]/mZ[1/p] ~= Z/m`
  of full order is faithful).  In the `(theta_n)` picture, torsion = bounded
  denominators = finite range = PERIODIC sequences; this is the equivalence
  (2) <-> (5) of [LP, Thm 2.12].
- **Rational aperiodic**: all `theta_n in Q` but unbounded denominators; e.g.
  `theta_n = 1/p^n` [LP, Rem 2.14].  These are NOT torsion.  A key example:
  the annihilator of `Z`,
  `Ann(Z) = { zeta : zeta|_Z = 1 } = lim_<- (mu_(p^n), p-th power) ~= Z_p`,
  is torsion-free and consists (apart from `1`) entirely of rational aperiodic
  points.  `T_p cap Ann(Z) = {1}`.
- **Irrational**: some (equivalently every) `theta_n` irrational.  (From `(Xi)`,
  `theta_n` rational iff `theta_(n+1)` rational, so rationality is
  all-or-nothing along the sequence.)

The dichotomy that matters below is torsion versus nontorsion (= LP-aperiodic),
NOT rational versus irrational.  The task sheet's expectation "unique trace iff
irrational" is wrong in exactly the sector the program cares about: the leak's
central marginal is carried by `Ann(Z) ~= Z_p`, i.e., by rational APERIODIC
points, and those fibers are rigid.

### A.1  Central disintegration of a trace

Let `phi` be a trace on `N`, with GNS triple `(pi, L^2, xi)` and
`M = pi(N)''`; the vector state extends `phi` to a normal tracial state
`tau_M` on `M`.  Since `c(Z[1/p])` is central in `N`, the unitaries
`pi(c(z))` lie in `Z(M)`; let `E(.)` be their joint spectral measure on
`S_p` (Gelfand spectrum of the generated central subalgebra, identified with
a closed subset of `S_p` by Bochner), so `pi(c(z)) = int zeta(z) dE(zeta)`.
Define the *central measure* `mu := <E(.)xi, xi>`, i.e.

```text
phi(c(z)) = int_(S_p) zeta(z) d mu(zeta).                  (CM)
```

**Proposition A1 (fiber disintegration).**  For `w in N` set
`nu_w(B) := tau_M(E(B) pi(w))`.  Then:

1. `nu_w << mu` with a density `h_w in L^infty(mu)`, `|h_w| <= 1` a.e.;
2. for `mu`-a.e. `zeta`, the function `phi_zeta(w) := h_w(zeta)` is a
   normalized trace on `N` with central character `zeta`
   (`phi_zeta(c(z) w) = zeta(z) phi_zeta(w)`); and
3. `phi(w) = int phi_zeta(w) d mu(zeta)` for all `w in N`.

*Proof.*  (1)  `E(B) in Z(M)` commutes with `pi(w)`, so
`|nu_w(B)| = |<pi(w) E(B) xi, E(B) xi>| <= ||E(B) xi||^2 = mu(B)`;
absolute continuity and the `L^infty`-bound follow by differentiation.
(2)  Traciality: `nu_(uv)(B) = tau_M(E(B) pi(u) pi(v)) = tau_M(E(B) pi(v) pi(u))
= nu_(vu)(B)` (trace property plus centrality of `E(B)`), so
`h_(uv) = h_(vu)` a.e.; positive-definiteness: for `w_1..w_r in N` and
`c in Q[i]^r`,
`sum c_i^bar c_j nu_(w_i^-1 w_j)(B) = <E(B) eta, eta> >= 0` with
`eta = sum c_j pi(w_j) xi` (again using that `E(B)` commutes with each
`pi(w_i)`), so the density matrices are a.e. psd (countably many rational
constraints, then continuity); central character:
`nu_(c(z)w)(B) = int_B zeta(z) d nu_w`, so `h_(c(z)w) = zeta(z) h_w` a.e.;
normalization `h_e = 1` a.e. since `nu_e = mu`.  Countably many conditions
(`N` is countable), so one null set covers all.  (3) is
`int h_w d mu = nu_w(S_p) = phi(w)`.  ∎

If `phi` is factorial, `Z(M) = C`, each `pi(c(z))` is a scalar, and `mu` is a
point mass: factorial traces have a central character.

### A.2  The fibers are noncommutative solenoids

Fix `zeta in S_p`.  A trace `phi` on `N` with central character `zeta`
determines `tau(W(x,y)) := phi(g(x,y,0))` on the twisted group algebra:
by `(M)` and the central character,

```text
tau(W(u) W(v)) = sigma_zeta(u,v) tau(W(u+v)),
sigma_zeta((x,y),(x',y')) := zeta(-x'y),                    (CO)
```

and conversely every tracial state of the full twisted group C*-algebra
`A_zeta := C*(Z[1/p]^2, sigma_zeta)` pulls back to a trace of `N` with
central character `zeta` (compose with the quotient
`C*(N) -> A_zeta`, `g(x,y,z) -> zeta(z) W(x,y)`; conjugation invariance of the
pullback under `a(s), b(t)` is exactly traciality of `tau` against
`W(s,0), W(0,t)`, computed below).  The correspondence is bijective and
affine.  Since `Z[1/p]^2` is amenable, full and reduced twisted algebras
coincide.

The antisymmetrized bicharacter of `sigma_zeta` is

```text
rho_zeta(u, v) = sigma_zeta(u,v) sigma_zeta(v,u)^-1 = zeta(x_u y_v - x_v y_u),
```

which matches the canonical Latremoliere--Packer multiplier `Psi_alpha` with
`alpha = (theta_n(zeta))` [LP, Thm 2.3]; since `H^2` of a discrete abelian
group is classified by the antisymmetrization (Kleppner, as used in [LP,
Sec. 2]), `A_zeta ~= A^S_alpha`, the noncommutative solenoid of [LP, Def 3.1].
Structure facts, all verified against the source:

- `A^S_alpha ~= C(S_p) rtimes Z[1/p]` for the `alpha`-twisted odometer-type
  action [LP, Prop 3.3].
- **Direct-limit bookkeeping** (task item): the subgroups `(p^-n Z)^2` exhaust
  `Z[1/p]^2`; on the `n`-th one the twist restricts to the rotation-algebra
  multiplier with angle `theta_(2n)` (the generators `u_n = W(p^-n, 0)`,
  `v_n = W(0, p^-n)` satisfy `u_n v_n = e^(2 pi i theta_(2n)) v_n u_n`, index
  `2n` because `rho` evaluates `zeta` at `p^-n * p^-n`).  So
  `A_zeta = lim_-> (A_(theta_0) -> A_(theta_2) -> A_(theta_4) -> ...)` with
  connecting maps `U -> U^p`, `V -> V^p`, and stage compatibility
  `p^2 theta_(2n+2) = theta_(2n) (mod 1)` — exactly [LP, Thm 3.7] (their
  `N^2 alpha_(2n+2) = alpha_(2n) + r_n`).

### A.3  Fiber trace rigidity: the symmetrizer computation

**Lemma A2.**  Let `tau` be any tracial state of `A_zeta`.  Then
`tau(W(v)) = 0` for every `v` outside the symmetrizer

```text
S_zeta := { v : rho_zeta(u, v) = 1 for all u }.
```

Moreover `S_zeta = 0` if `zeta` is nontorsion, and
`S_zeta = (mZ[1/p])^2` if `zeta` has exact order `m`.

*Proof.*  `W(u) W(v) W(u)^* = rho_zeta(u,v) W(v)`, so traciality gives
`tau(W(v)) = rho_zeta(u,v) tau(W(v))` for every `u`; if `v notin S_zeta` pick
`u` with `rho_zeta(u,v) != 1`.  For the computation: `v = (x,y) in S_zeta`
iff `zeta(x y' - x' y) = 1` for all `(x', y')`, i.e. iff the ideal
`(x, y) Z[1/p]` lies in `ker zeta`.  A nonzero ideal is `d Z[1/p]` with
`Z[1/p]/dZ[1/p]` finite; if `zeta` kills it, `zeta` is torsion.  So
nontorsion `zeta` forces `S_zeta = 0`.  If `zeta` has exact order `m` then
`ker zeta = mZ[1/p]` and the ideal condition reads `x, y in mZ[1/p]`.  ∎

This matches [LP, Thm 2.12] exactly: symmetrizer nontrivial iff the parameter
sequence is periodic (their item (5)), with the explicit form
`{(p_1 b/N^m, p_2 b/N^n)}` (their item (6), their `b` = our `m`).

**Proposition A3 (fiber trace simplex).**

1. If `zeta` is nontorsion, `A_zeta` has a UNIQUE tracial state, the canonical
   `tau_0(W(v)) = 1_(v=0)`.
2. If `zeta` is torsion of exact order `m`, the trace simplex of `A_zeta` is
   affinely isomorphic to the probability measures on
   `dual((mZ[1/p])^2) ~= S_p x S_p`: the traces are exactly
   `tau_eta = eta o E_S`, where `E_S : A_zeta -> C*((mZ[1/p])^2)` is the
   conditional expectation annihilating `W(v)`, `v notin S_zeta`, and `eta`
   is any state of `C*(S_zeta)` (note `sigma_zeta` is trivial on
   `S_zeta x S_zeta` since `zeta((mx')(my)) = 1`, so that subalgebra is the
   untwisted `C*((mZ[1/p])^2)`).

*Proof.*  (1)  By Lemma A2 a trace is `1_(v=0)` on the dense span of the
`W(v)`; states are norm-continuous, so there is at most one.  Existence:
average over the dual action of `S_p^2` (`(z,w).W(x,y) = <z,x><w,y> W(x,y)`),
as in [LP, Thm 3.6].  (2)  `E_S` exists as the Haar average over the compact
annihilator of `S_zeta` inside `S_p^2` acting dually (the fixed algebra is the
span of `W(S_zeta)` by double-annihilation for the discrete group
`Z[1/p]^2`); it is ucp, so `tau_eta` is a state, and it is tracial: both
`tau_eta(W(u)W(v))` and `tau_eta(W(v)W(u))` vanish unless `u+v in S_zeta`, in
which case `rho_zeta(u,v) = rho_zeta(u, -u + s) = 1` (antisymmetry
`rho(u,-u) = 1` plus `s in S_zeta`), so `sigma_zeta(u,v) = sigma_zeta(v,u)`.
Conversely Lemma A2 says any trace is supported on `S_zeta`, i.e. factors as
`eta o E_S` with `eta = tau|_(C*(S_zeta))`.  ∎

Cross-check with [LP]: simplicity of `A^S_alpha` iff aperiodicity [LP, Thm
3.5], and unique trace under simplicity [LP, Thm 3.6]; Proposition A3(1) is
the same uniqueness with the (elementary) symmetrizer proof, valid for ALL
aperiodic parameters including the rational aperiodic ones, and A3(2) is the
complementary description on the periodic side.

### A.4  Theorem A: the torsion-mass criterion

**Theorem A.**  Let `phi` be a trace on `N = H_3(Z[1/p])` with central
measure `mu` as in `(CM)`.

1. (Canonical vanishing.)  If `mu(T_p) = 0`, then

   ```text
   phi(g(x,y,z)) = 0 for all (x,y) != (0,0),
   ```

   i.e. `phi` is the canonical trace `gamma_mu` determined by `mu`:
   `gamma_mu(g(0,0,z)) = mu^(z)`, zero off the center.
2. (Sharpness.)  If `mu(T_p) > 0`, there is a NON-canonical trace with the
   same central measure: since `T_p` is countable, the torsion part of `mu`
   is atomic, `mu_t = sum_i m_i delta_(zeta_i)`; choose for each `i` a
   nontrivial character `eta_i` of `S_(zeta_i) = (m_i' Z[1/p])^2` and set
   `phi = gamma_(mu - mu_t) + sum_i m_i (tau_(eta_i) pullback)`.  Then
   `phi(g(x,y,0)) = sum_i m_i eta_i(x,y) != 0` for suitable
   `(x,y) != 0`.
3. (Character list, for completeness.)  The extremal traces of `N` are:
   for each nontorsion `zeta`, the canonical `gamma_(delta_zeta)`; for each
   torsion `zeta` of exact order `m` and each `eta in dual((mZ[1/p])^2)`, the
   trace `g(x,y,z) -> zeta(z) eta(x,y) 1_((x,y) in (mZ[1/p])^2)`.

*Proof of (1), self-contained (no disintegration needed).*  Fix
`(x,y) != (0,0)` and let `F(z) := phi(g(x,y,z)) = int zeta(z) h(zeta) dmu`
with `h = h_(g(x,y,0))` from Proposition A1(1) (only part (1) of A1 is used).
Conjugation by `a(s)` and `b(t)` gives, from `(M)`,

```text
a(s) g(x,y,z) a(s)^-1 = g(x, y, z + sy),
b(t) g(x,y,z) b(t)^-1 = g(x, y, z - tx),
```

so invariance forces `F(z) = F(z + w)` for every `w` in the nonzero ideal
`I = (x,y) Z[1/p] = d Z[1/p]`.  Hence for every `w in I` and every `z`,
`int zeta(z) (1 - zeta(w)) h(zeta) dmu = 0`; the characters
`zeta -> zeta(z)` span a dense *-subalgebra of `C(S_p)` (Stone--Weierstrass),
so the complex measure `(1 - zeta(w)) h dmu` vanishes: `h = 0` a.e. off
`{zeta : zeta|_I = 1}`.  That set is the annihilator of `dZ[1/p]`, the dual
of the FINITE group `Z[1/p]/dZ[1/p]`, hence a finite subgroup of `S_p`,
hence contained in `T_p`.  If `mu(T_p) = 0` then `h = 0` a.e. and `F ≡ 0`. ∎

*Proof of (2).*  Each `tau_(eta_i)`-pullback is a trace on `N` with central
measure `delta_(zeta_i)` (Prop A3(2) and the correspondence of A.2), and
`gamma_(mu - mu_t)` is the integral of canonical fiber traces, psd as such.
The stated combination has central measure `mu` and the displayed
non-vanishing.  ∎

*Proof of (3).*  By A1 an extremal trace has a central character; by A3 the
fiber simplices are as listed, with extreme points the listed traces; their
factoriality is Kleppner's condition (trivial symmetrizer) in case (1) and a
routine check in case (2); none of this is used downstream.  ∎

**Corollary A4 (allowed central measures).**  Full-mass-canonical holds for:
Haar (nonatomic, `T_p` countable); ANY nonatomic measure; any measure
supported on `Ann(Z) ~= Z_p` with no atom at `1` (torsion meets `Ann(Z)` only
in `1`).  It fails for: any atom at a torsion point, in particular any atom
at `1` interacts with the degenerate commutative fiber
`A_1 = C*(Z[1/p]^2) = C(S_p^2)` (trace simplex = all of `Prob(S_p^2)`).

**Remark (context).**  For `H_3(Z)` the analogous dichotomy (irrational
central angle ⟹ vanishing off center) is classical, and character theory of
discrete nilpotent groups is an old subject (Carey--Moran; cf. also
Levit--Vigdorovich arXiv:2206.02268 for solvable groups); Theorem A for the
localized group with the exact torsion-vs-rational-aperiodic criterion and
the LP fiber dictionary is what the graph needs and did not record.  Novelty
is claimed relative to the Cairn graph, not to the world.

---

## Section B.  Application map

Recall the enemy in its two recorded forms: (a) a factorial hyperlinear
character `tau` of `H` with `tau|_Gamma = delta_e` violating

```text
tau(t^-1 gamma^-1 t gamma) = 1 for all gamma in Gamma,      (FC1)
```

and (b) a leak: a unitary `k in pi(Lambda)' cap M` of a matrix ultraproduct
with `Lambda`-bi-invariant profile `psi_k(g) = tr(k^* pi(g) k pi(g)^*)`,
`psi_k ≡ 1` on `Lambda`.  Throughout, `k = pi_tau(t)` in the GNS of (a).

### B.1  The collapse is a statement about one Heisenberg subgroup

Since `[t, Lambda] = 1` in `H`, `k` commutes with `pi(Lambda)`.  If
`psi(gamma) := tau(t^-1 gamma^-1 t gamma) = 1` then, in the GNS with trace
vector `xi`, Cauchy--Schwarz equality gives
`pi(gamma)^-1 k pi(gamma) xi = k xi`, and `xi` separating yields exact
commutation.  Since

```text
Gamma = < Lambda, N >
```

(the corner unipotents `e_12, e_23, e_13` over `Z[1/p]` lie in `N`; signed
Weyl permutations in `Lambda` carry them to all six root subgroups; and
`SL_3` of the Euclidean domain `Z[1/p]` is generated by elementaries), we get:

**Observation B1.**  (FC1) holds for `tau` iff `psi ≡ 1` on `N`.  Similarly
with `N` replaced by the corner `Delta = SL_2(Z[1/p])` (upper-left block),
since `Gamma = < Lambda, Delta >` too.

This is the `N`-variant of the recorded single-commutation reduction
(`sl3-pair-relative-commutant-route`, attempt 1, with `h = diag(2,1,1/2)`);
it aims the whole collapse at exactly the subgroup Theorem A classifies.

### B.2  Where solenoidal Heisenberg traces with nontrivial central data occur

**(a) On subgroups of `Gamma`: nowhere (forced).**  `tau|_Gamma = delta_e`,
so `tau|_N = delta_e = gamma_Haar`: canonical, central measure Haar,
`Haar(T_p) = 0`.  Consistent with Theorem A, zero free parameters.  (Task
item (a): verified against the carrier node; no content, as predicted.)

**(b) On mixed subgroups of `H`: impossible.  (New small theorem.)**

**Proposition B2 (`p`-divisible elements are elliptic).**  Every element of
`H` that is a `p^n`-th power for every `n` is elliptic on the Bass--Serre
tree of `H`, i.e. lies in a conjugate of `Gamma`.  Consequently every
subgroup of `H` isomorphic to a `p`-divisible group — in particular every
copy of `N`, of `Z[1/p]`, or of any quotient of `N` — lies pointwise in
conjugates of `Gamma`, and any character with `delta_e`-restriction to
`Gamma` restricts to `delta_e` on it.  There are NO mixed (letter-involving)
solenoidal Heisenberg subgroups.

*Proof.*  Translation lengths on trees satisfy `ell(g^k) = |k| ell(g)`.  If
`g = g_n^(p^n)` then `p^n | ell(g)` for all `n`, so `ell(g) = 0` and `g`
fixes a vertex; vertex stabilizers of the HNN tree are the conjugates of
`Gamma`.  `N` is `p`-divisible: by the power formula
`g(u,v,w)^k = g(ku, kv, kw - C(k,2) uv)` one solves
`g(x,y,z) = g(x/p, y/p, (z + C(p,2) xy/p^2)/p)^p` inside `N`.  For the trace
statement: `w = gamma^h` with `gamma in Gamma` gives
`tau(w) = tau(gamma) = delta_e(gamma) = delta_e(w)`.  ∎

What mixed structure DOES exist at the smallest scale is an amalgam of
solenoids, not a Heisenberg group: for the central root,
`< e_13(Z[1/p]), t e_13(Z[1/p]) t^-1 > ~= Z[1/p] *_Z Z[1/p]`
(the two copies are glued along `e_13(Z)`, which `t` centralizes; Britton
keeps alternating non-integral words reduced).  The enemy's two-block data on
this subgroup is a character of `Z[1/p] *_Z Z[1/p]` restricting to `delta_e`
on both factors — a correct minimal mixed testing surface, but outside the
Heisenberg mechanism; not pursued here.

**(c) On the leak profile: yes on the center, no on traciality.**
`psi_k|_N` is positive definite, `≡ 1` on `N(Z)`, and `Lambda`-conjugation
invariant, but NOT `N`-conjugation invariant (not a trace on `N`).  Its
central marginal is forced into the rigid sector: `psi_k(c(n)) = 1` for
`n in Z` puts the representing measure `nu` on `Ann(Z) ~= Z_p`, so ALL of
`nu`'s mass off the single point `1` sits on rational APERIODIC (nontorsion)
points — precisely the unique-trace fibers of Proposition A3.  For the exact
enemy (`psi = 1_Lambda`), `nu` = Haar on `Z_p`, atomless.  Had the task's
"irrational = rigid" guess been the truth, the entire enemy sector would have
been outside the mechanism; LP-aperiodicity catches it.

**Proposition B3 (traciality fence).**  Let `k in pi(Lambda)' cap M` be any
unitary with `psi_k ≡ 1` on `Lambda`.  If `psi_k|_N` is `N`-conjugation
invariant (in particular if `[k, pi(N)] = 0`), then `psi_k(c(z)) = 1` for
ALL `z in Z[1/p]` — the whole central solenoid tower commutes with `k`
exactly — and `psi_k|_N` factors through the abelianization `Z[1/p]^2`.

*Proof.*  `psi_k|_N` is then a trace on `N` with `psi ≡ 1` on `N(Z)` and
central marginal `nu` on `Ann(Z)`.  Torsion mass of `nu` is `nu({1})`
(Corollary A4).  Theorem A applied to the nontorsion part gives
`psi(a(1)) = nu({1}) . phi_1(a(1))`; since `psi(a(1)) = 1` and
`|phi_1(a(1))| <= 1`, `nu({1}) = 1`, i.e. `nu = delta_1`:
`psi(c(z)) = 1` for all `z`.  The fiber at `1` is commutative
(`A_1 = C(S_p^2)`), giving the factorization.  ∎

Contrapositive: the exact enemy (`psi(c(1/p)) = 0 != 1`) has maximally
non-tracial `N`-profile; the enemy's freedom on `N` is EXACTLY its traciality
defect.  Together with (a) and (b) this answers the task's step 3
honestly: no trace on a `Z[1/p]`-Heisenberg group with nontrivial central
marginal occurs anywhere in the enemy's structure directly; what occurs is
(i) the non-tracial profile with rigid-sector central marginal, and (ii) —
the productive surface — TRACES ON OVERGROUPS of `N` whose components
Theorem A pins, next.

**(c') Scaling invariance (task sub-question, answered negatively).**  The
diagonal `D = <h = diag(p,1,1/p), h' = diag(1,p,1/p)>` normalizes `N` with
`alpha_h : a(x),b(y),c(z) -> a(px), b(py), c(p^2 z)`, hence maps the fiber
`A_zeta` to `A_(zeta o p^2)`: it does not act on a single noncommutative
solenoid unless `zeta` is torsion of order dividing `p^2 - 1`.  On `C*(N)`,
an `alpha_h`-invariant trace merely has `x p^2`-invariant central measure,
and the single hyperbolic solenoid map has many invariant measures,
including finite-orbit measures ON TORSION POINTS (the `x p^2`-orbit of a
torsion point is finite); so there is NO unique-invariant-trace theorem from
the scaling alone, and both `h`-weights on the center are powers of `p`
(rank one).  An earlier version then pointed to a rank-two joint-solenoid
EKL program.  That pointer was wrong: the three positive root subgroups form
the nonabelian Heisenberg group, so no joint three-solenoid SNAG measure
exists.  The corrected global format is
`sl3-upper-unipotent-is-a-noncommutative-solenoid-field`, a `D`-transported
field of the noncommutative fibers classified here.  At the degenerate fiber
`zeta = 1` the unique-invariant-state question is FALSE outright
(`C(S_p^2)`, single map, recorded).

### B.3  Components of enemy restrictions are a.e. canonical

**Proposition B4.**  Let `E` be any countable group with `N <= E`, and let
`rho` be a trace on `E` with `rho|_N = delta_e`.  Write the extremal
(ergodic) decomposition `rho = int sigma_x d m(x)` over characters of `E`.
Then for `m`-a.e. `x`, the restriction `sigma_x|_N` is a CANONICAL solenoidal
trace: it vanishes off `c(Z[1/p])` and its central measure `mu_x` has
`mu_x(T_p) = 0`.  Moreover `int mu_x d m = Haar`.

*Proof.*  Restricting the decomposition to the center and taking Fourier
transforms, `int mu_x dm` represents `delta_e|_(c(Z[1/p]))`, which is the
transform of Haar; uniqueness in Bochner gives `int mu_x dm = Haar`.  Then
`int mu_x(T_p) dm = Haar(T_p) = 0` (the integrand is measurable: `T_p` is
countable and atom masses are Wiener averages of the transforms), so
`mu_x(T_p) = 0` a.e.; Theorem A(1) applies to a.e. `sigma_x|_N`.  ∎

This is the mechanism's positive payload: the enemy CANNOT be probed through
its (forced, trivial) restriction, but its ergodic components over any window
containing `N` are forced into the exact shape Theorem A classifies.

### B.4  The transparency theorem: no subgroup-local bridge exists

Let `E_N := <N, t> <= H`.  Britton (elements of `N \ N(Z)` are not in
`Lambda`) gives

```text
E_N ~= < N, t | [t, N(Z)] = 1 >,
```

the solenoidal-Heisenberg HNN microcosm of the carrier.  A subgroup-local
bridge would be: "every factorial hyperlinear character of `E_N` with the
enemy's local restriction data centralizes `t` against `N`".  This is FALSE:

**Theorem B5 (transparency of the Heisenberg window).**  There exists a
factorial hyperlinear character `sigma` of `E_N` such that `sigma|_N` is
canonical with aperiodic central measure (zero torsion mass), and yet
`Re sigma(t^-1 n^-1 t n) <= 1/2` for some `n in N` — so `pi_sigma(t)` does
not commute with `pi_sigma(N)`.

*Proof.*  Let `W_N := (directsum_(N/N(Z)) C_2) rtimes N`, the coset wreath
group over the Heisenberg pair, and `q : E_N -> W_N` the surjection fixing
`N` and sending `t` to the lamp at the base coset (well-defined: the base
lamp commutes with the stabilizer `N(Z)`; onto: the lamps are the
`N`-translates of the base lamp).  `W_N` is AMENABLE (abelian-by-nilpotent),
so every trace of `W_N` has injective (hyperfinite) GNS von Neumann algebra;
in particular every character of `W_N`, and every pullback along `q`, is
hyperlinear.  Consider `rho := delta_e^(W_N) o q`, a trace on `E_N` with
`rho|_N = delta_e`, and its extremal decomposition
`rho = int sigma_x dm(x)` (extremal components of the pullback are pullbacks
of extremal components of `delta_e^(W_N)`: kernels act trivially in GNS, so
subordinate traces also factor through `q`; and components of a hyperfinite-
GNS trace are a.e. hyperfinite).  By Proposition B4, a.e. `sigma_x|_N` is
canonical with `mu_x(T_p) = 0`.  Fix `n = a(1/p)`.  The word
`w = t^-1 n^-1 t n` has `q(w) = x_(N(Z)) x_(n^-1 N(Z)) != e` (two distinct
lamps: `n notin N(Z)`), so `rho(w) = 0`, i.e. `int Re sigma_x(w) dm = 0`
with `Re sigma_x(w) <= 1`; hence `m{ Re sigma_x(w) <= 1/2 } >= 1/4`
(Markov on `1 - Re`).  Intersect this positive-measure set with the co-null
set from B4: any `x` in the intersection gives the asserted `sigma`.  ∎

**Corollary B6 (general amenable windows).**  The same construction works
verbatim for `E_A := <A, t> ~= <A, t | [t, A cap Lambda] = 1>` for EVERY
subgroup `A <= Gamma` for which `W_A = (directsum_(A/(A cap Lambda)) C_2)
rtimes A` is hyperlinear — unconditionally for every amenable `A`, and, by
the recorded soficity of generalized Bernoulli actions with amenable
stabilizers (the Kun--Thom wall is only the NON-amenable-stabilizer case),
for every sofic `A` with `A cap Lambda` amenable.  In all such windows there
exist factorial hyperlinear characters with the enemy's exact local shape.
No unique-trace, character-rigidity, or invariant-state mechanism applied to
a window with amenable edge `A cap Lambda` can close (FC1).

**Corollary B7 (the minimal opaque window is rank one).**  A window immune
to B6 needs `A cap Lambda` non-amenable.  If `A` contains `Lambda` properly,
or contains two opposite root groups over `Z[1/p]`, then `A`'s window
already generates the full problem (`<Lambda, A> = Gamma` by elementary
generation).  The minimal natural window with non-amenable edge and proper
image is the `SL_2`-corner:

```text
E_2 := < Delta, t >_H ~= < SL_2(Z[1/p]), s | [s, SL_2(Z)] = 1 >,
Delta = upper-left SL_2 corner, Delta cap Lambda = SL_2(Z),
```

the RANK-ONE carrier.  (Britton again: corner elements with non-integral
entries are outside `Lambda`.)  So the window hierarchy bottoms out exactly
at CORE A's object — an independent, subgroup-theoretic re-derivation of the
capstone "no arithmetic route escapes rank one".

This proves, as a theorem rather than an intuition, the recorded sentence
"every amenable piece is locally realizable, so the obstruction must be a
rigidity of the non-amenable assembly"
(`sl3-near-exact-leaks-live-in-the-two-primary-tower`, plateau bullet): even
the full local HNN carrier over any amenable piece, with all enemy
hypotheses (factorial, hyperlinear, canonical restriction) imposed, is
realizable.

### B.5  The rank-one window reduction

The transparency analysis leaves exactly one local claim standing; here is
its precise form and the proof that it suffices.

**(R1) (OPEN).**  Every factorial hyperlinear character `sigma` of
`E_2 = < SL_2(Z[1/p]), s | [s, SL_2(Z)] = 1 >` whose restriction to
`SL_2(Z[1/p])` vanishes off the center `{±I}` satisfies
`sigma(s^-1 g^-1 s g) = 1` for all `g in SL_2(Z[1/p])`.

Two proved lemmas feed the reduction.

**Lemma L0 (hyperlinear traces are weak-* closed).**  For a countable group
`E`, the set of hyperlinear traces is closed under pointwise limits.
*Proof.*  A trace is hyperlinear iff for every finite `F subset E` and
`eps > 0` there are `d` and unitaries `(u_g)_(g in F cup F.F)` in `U(d)`
with `||u_g u_h - u_(gh)||_2 <= eps` and `|tr(u_g) - tau(g)| <= eps` for the
relevant elements (matrix microstates for the GNS embedding).  This local
condition passes to pointwise limits by a diagonal argument.  ∎

**Lemma L1 (a.e. ergodic component of a hyperlinear trace is hyperlinear).**
Let `rho` be a hyperlinear trace on a countable group `E` with extremal
decomposition `rho = int sigma_x dm(x)`.  Then `sigma_x` is hyperlinear for
a.e. `x`.
*Proof.*  Let `M = pi_rho(E)''` embed trace-preservingly in a matrix
ultraproduct `Q`, and let `(z_B)` be the central projections of the
decomposition's measure algebra.  For a positive-measure `B`, the normalized
trace `rho_B := rho(z_B . )/m(B)` on `E` has GNS algebra `M z_B`, which
embeds in the corner `z_B Q z_B`; a corner of a matrix ultraproduct by any
projection is again a matrix ultraproduct (cut each coordinate by a
projection of matching rank), so `rho_B` is hyperlinear.  Refining `B` along
a generating filtration, martingale convergence gives
`sigma_x(w) = lim_(B -> x) rho_B(w)` for every `w` in the countable group,
a.e.; Lemma L0 finishes.  ∎

**Theorem B8 (reduction).**  (R1) implies (FC1) for the `SL_3` carrier `H`:
every factorial hyperlinear character `tau` of `H` with
`tau|_Gamma = delta_e` satisfies `tau(t^-1 gamma^-1 t gamma) = 1` for all
`gamma in Gamma`.  Hence (R1) implies (RC3) (by the recorded equivalence
`rcc-carrier-character-face-compression`) and the goal (by
`non-hyperlinear-from-sl3-relative-commutant-collapse`).

*Proof.*  Let `tau` be such a character; `M_tau` embeds in a matrix
ultraproduct.  Set `rho := tau|_(E_2)`, a trace on `E_2 ~= <Delta, t>`
(iso by Corollary B7) with `rho|_Delta = delta_e`; its GNS is the subalgebra
`pi_tau(E_2)'' <= M_tau`, so `rho` is hyperlinear.  Take the extremal
decomposition `rho = int sigma_x dm(x)` over characters of `E_2`.  A.e.
`sigma_x` is factorial (extremal) and hyperlinear (Lemma L1).  It remains to
verify the restriction hypothesis of (R1) a.e., then integrate.

*Corner classification step.*  By Peterson--Thom [PT, proof of Thm 2.6 via
Prop 2.8; see Section D], every extremal character of
`Delta = SL_2(Z[1/p])` (a localization with infinitely many units) either
factors through a finite quotient of `Delta` or vanishes off the center
`{±I}`.  Decompose each `sigma_x|_Delta` by Choquet over this dichotomy and
let `f_x in [0,1]` be the total mass of the finite-quotient part.  Choose a
sequence `g_j in Delta`, `g_j != ±I`, with `g_j` in the intersection of all
normal subgroups of `Delta` of index `<= j` (a finite-index, hence infinite,
subgroup — no congruence subgroup property needed).  Then for every FIXED
finite-quotient extremal character `chi`, `chi(g_j) = 1` for all large `j`
(eventually `g_j in ker`), while every vanishing-branch extremal gives
`0` at `g_j`; dominated convergence inside the Choquet integral yields

```text
lim_j sigma_x(g_j) = f_x  for every x,
```

which also shows `x -> f_x` is measurable.  Integrating in `x` and using
dominated convergence again:
`int f_x dm = lim_j int sigma_x(g_j) dm = lim_j rho(g_j) = lim_j delta_e(g_j) = 0`.
So `f_x = 0` a.e.: a.e. `sigma_x|_Delta` is a mixture of vanishing-branch
extremals, i.e. vanishes off `{±I}`.

*Conclusion.*  A.e. `sigma_x` satisfies all hypotheses of (R1); hence
`sigma_x(t^-1 g^-1 t g) = 1` for all `g in Delta`, a.e.  Integrating,
`psi(g) = rho(t^-1 g^-1 t g) = 1` on `Delta`; by Cauchy--Schwarz equality in
the GNS of `tau`, `k = pi_tau(t)` commutes with `pi_tau(Delta)`; it commutes
with `pi_tau(Lambda)` by the defining relation; and
`Gamma = <Lambda, Delta>` (Observation B1), so `k` commutes with
`pi_tau(Gamma)`, which is (FC1).  ∎

**Status ledger for (R1).**  (i) The amenable-wreath escape of Theorem B5
does NOT refute it: the corresponding wreath
`W_2 = C_2 wr_(SL_2(Z[1/p])/SL_2(Z)) SL_2(Z[1/p])` has NON-amenable
stabilizers, and its hyperlinearity is exactly the recorded Kun--Thom wall —
(R1) and CE of that Bernoulli action stand or fall together, matching
`coset-bernoulli-ce-refutes-relative-commutant-collapse`.  (ii) The
finite-dimensional sector is consistent: f.d. representations of
`SL_2(Z[1/p])` factor through finite (congruence) quotients where the images
of `SL_2(Z)` and `SL_2(Z[1/p])` coincide (co-density,
`sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`), forcing `s` central
there — but such `sigma` are excluded by the vanishing-branch hypothesis
anyway.  (iii) `delta_e`-shaped characters: if `E_2` is hyperlinear, apply the
component machinery of Theorem B8 to the central components `tau_omega` of
`delta_e^(E_2)` (each has `tau_omega(g_j) = 0` off the center, and
`tau_omega(t^-1 g^-1 t g) = 0` for `g notin SL_2(Z)` since Britton keeps that
word off `{±I}`): a.e. ergodic component is vanishing-branch, hyperlinear
(L1), factorial, and a positive measure of them violate the conclusion
(Markov, as in Theorem B5).  So (R1) implies `E_2` — the rank-one HNN
carrier itself — is not hyperlinear.  (R1) is thus a goal-reaching claim, exactly like its
recorded `n >= 3` sibling, not an auxiliary lemma.  (iv) Tree deformations
pass through it for the same reason recorded in the carrier node (the enemy
respects the amalgam geometry).

### B.6  Verdict

- The mechanism CANNOT close (FC1) through any subgroup-local window: proved
  transparency for every amenable-edge window (Theorem B5, Corollary B6).
  This demotes, permanently, the entire family of "prove unique-trace/
  invariant-state rigidity on an amenable subgroup and localize" attacks,
  and proves the recorded non-amenable-assembly intuition.
- The mechanism DOES feed the lane, twice.  First, Theorem A is the
  classification input the carrier node's plateau bullet asked to be tested
  against: it pins the ergodic components of every enemy restriction over
  every window containing `N` (Proposition B4).  Second, and mainly, the
  window analysis plus the component machinery (L0, L1, PT) proves the NEW
  unconditional arrow

  ```text
  (R1)  =>  (FC1) [n = 3]  =>  (RC3)  =>  goal,
  ```

  reducing the `SL_3` carrier collapse to a single rank-one open claim —
  `hnn-carrier-factorial-character-collapse` is the node fed, via the new
  route drafted below, with (R1) as its one open input.

---

## Section C.  Proposed Cairn node drafts

Six files: two established claim+proof pairs, one OPEN claim, one conditional
route into the existing collapse node.  All `distinct_from` targets verified
to exist in `research/`.  Suggested artifact copy of this memo:
`research/artifacts/noncommutative-solenoid-unique-trace-memo-2026-08-22.md`
(referenced below as THE MEMO; lead to land and wire).

### C.1  `research/heisenberg-solenoid-trace-torsion-dichotomy.md`

```markdown
---
rg: 2
id: heisenberg-solenoid-trace-torsion-dichotomy
kind: claim
title: Traces of the p-solenoidal Heisenberg group are canonical exactly off the torsion central sector
artifacts:
  - research/artifacts/noncommutative-solenoid-unique-trace-memo-2026-08-22.md
distinct_from:
  sl3-upper-unipotent-is-a-noncommutative-solenoid-field: that records the corrected D-transported field of noncommutative fibers for the full upper-unipotent carrier; this is the fiberwise trace classification itself, with an exact torsion criterion.
  far-sector-is-solenoid-measure-rigidity: that is APPROXIMATE measure rigidity for one hyperbolic solenoid automorphism in the SL_2 far sector, where single-map rigidity fails; this is an EXACT trace classification whose rigidity comes from twisted-group-algebra symmetrizers, not from dynamics, and it is insensitive to the single-map obstruction.
  relative-t-heisenberg-adjoint-quantum-expansion: that turns finite irreducible Heisenberg quotients into quantum expanders via relative property (T); this classifies the infinite-level trace simplex of the discrete Z[1/p]-Heisenberg group itself.
---

Let `N = H_3(Z[1/p])` with center `c(Z[1/p])`, `S_p` the p-solenoid dual of
`Z[1/p]`, and `T_p ~= directsum_(q != p) Z(q^infty)` its countable torsion
subgroup.  Every trace `phi` of `N` has a central measure `mu` on `S_p`
(`phi(c(z)) = int zeta(z) dmu`).  Claim (established; proof route):

1. If `mu(T_p) = 0` then `phi` vanishes off the center:
   `phi(a(x)b(y)c(z)) = 0` for `(x,y) != (0,0)`.
2. Sharp converse: if `mu(T_p) > 0` there are non-canonical traces with
   central measure `mu`, supported on `(mZ[1/p])^2`-cosets over the torsion
   atoms.
3. Fiberwise: traces with central character `zeta` are the tracial states of
   the Latremoliere--Packer noncommutative solenoid `C*(Z[1/p]^2, sigma_zeta)`
   (arXiv:1110.6227, NYJM 24A (2018) 155-191); that algebra has a unique
   trace iff `zeta` is NONTORSION (= LP-aperiodic, their Thms 2.12/3.5/3.6),
   including all rational aperiodic `zeta` — strictly weaker than
   irrationality, and the leak-relevant sector `Ann(Z) ~= Z_p` is exactly
   rational aperiodic minus the point `1`.

Consequences wired elsewhere: components of any enemy restriction over any
window containing `N` are a.e. canonical
(`amenable-carrier-windows-are-character-transparent` uses this), and Haar,
or any atomless central measure, forces canonicality.
```

### C.2  `research/heisenberg-solenoid-trace-torsion-dichotomy-proof.md`

```markdown
---
rg: 2
id: heisenberg-solenoid-trace-torsion-dichotomy-proof
kind: route
title: Symmetrizer support plus central Fourier inversion proves the torsion dichotomy
target: heisenberg-solenoid-trace-torsion-dichotomy
requires: []
artifacts:
  - research/artifacts/noncommutative-solenoid-unique-trace-memo-2026-08-22.md
---

Vanishing direction, self-contained.  Fix `(x,y) != 0` and let
`F(z) = phi(a(x)b(y)c(z))`.  Conjugation by `a(s), b(t)` translates the
central coordinate by the nonzero ideal `I = (x,y)Z[1/p] = dZ[1/p]`, so `F`
is `I`-periodic.  Writing `F(z) = int zeta(z) h dmu` with `|h| <= 1` (the
density of `B -> tau_M(E(B) pi(a(x)b(y)))` against `mu`, dominated because
the central spectral projections commute with the group image), periodicity
gives `(1 - zeta(w)) h = 0` in `L^1(mu)` for every `w in I` (characters span
densely in `C(S_p)`), so `h` is supported on the annihilator of `I` = the
dual of the finite group `Z[1/p]/dZ[1/p]` — a finite, hence torsion,
subgroup.  `mu(T_p) = 0` kills `h`.

Fiber form.  A trace with central character `zeta` is a tracial state of the
twisted algebra `A_zeta` with multiplier `sigma_zeta((x,y),(x',y')) =
zeta(-x'y)`; `W(u)W(v)W(u)* = rho_zeta(u,v) W(v)` with
`rho_zeta(u,v) = zeta(x_u y_v - x_v y_u)` forces every trace to vanish off
the symmetrizer `S_zeta`, and `S_zeta != 0` iff `ker zeta` contains a
nonzero ideal iff `zeta` is torsion (then `S_zeta = (mZ[1/p])^2`, `m` the
exact order).  This matches Latremoliere-Packer Thm 2.12 exactly, and their
Thm 3.7 gives the rotation-algebra tower `A_(theta_0) -> A_(theta_2) -> ...`
with `U -> U^p`, `V -> V^p` and `p^2 theta_(2n+2) = theta_(2n) (mod 1)`.

Converse.  Over a torsion atom `zeta` (order `m`), the multiplier is trivial
on `S_zeta = (mZ[1/p])^2`; the dual-action average onto `span W(S_zeta)` is
a conditional expectation, and `eta o E_S` is a tracial state for every
character `eta` of `S_zeta` (traciality: `rho_zeta(u, -u + s) = 1`); choose
`eta` nontrivial.  Full computations: THE MEMO, Section A.
```

### C.3  `research/amenable-carrier-windows-are-character-transparent.md`

```markdown
---
rg: 2
id: amenable-carrier-windows-are-character-transparent
kind: claim
title: Every amenable-edge window of the HNN carrier admits enemy-shaped factorial hyperlinear characters
artifacts:
  - research/artifacts/noncommutative-solenoid-unique-trace-memo-2026-08-22.md
distinct_from:
  hnn-carrier-factorial-character-collapse: that asserts the GLOBAL collapse for the full carrier; this proves no subgroup-local window with amenable edge can witness it, locating the collapse's content irreducibly in the non-amenable assembly.
  sl3-near-exact-leaks-live-in-the-two-primary-tower: that records local realizability of the enemy's RESTRICTION DATA on amenable subgroups (plateau bullet); this strengthens realizability to full factorial hyperlinear characters of the local HNN window `<A, t>` satisfying every enemy hypothesis at once, killing the entire local-rigidity attack family rather than one probe.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that conditions on OPEN Connes embeddability of the nonamenable-stabilizer coset Bernoulli; this uses amenable-stabilizer wreaths, so the countermodels are unconditional.
---

Let `H` be the carrier over `Gamma = SL_3(Z[1/p])`, and for `A <= Gamma` let
`E_A = <A, t>_H ~= <A, t | [t, A cap Lambda] = 1>` (Britton).  Claim
(established; proof route): whenever the coset wreath
`W_A = (directsum_(A/(A cap Lambda)) C_2) rtimes A` is hyperlinear — so
unconditionally for every amenable `A`, and for sofic `A` with amenable edge
`A cap Lambda` by the recorded amenable-stabilizer soficity — there exist
factorial hyperlinear characters `sigma` of `E_A` with the enemy's exact
local shape: `sigma|_A` canonical (for the Heisenberg window `A = N`:
vanishing off the center with aperiodic central measure, per
`heisenberg-solenoid-trace-torsion-dichotomy`), yet
`sigma(t^-1 a^-1 t a) != 1` for some `a in A`.

Consequences.  (i) No unique-trace / character-rigidity / invariant-state
mechanism run inside a window with amenable edge can close the collapse;
the obstruction, if real, lives only in windows with NON-amenable
`A cap Lambda`.  (ii) Any such window either regenerates the whole group
(`<Lambda, A> = Gamma` once `A` holds two opposite `Z[1/p]`-root groups or
strictly contains `Lambda`) or bottoms out at the `SL_2`-corner window
`E_2 ~= <SL_2(Z[1/p]), s | [s, SL_2(Z)] = 1>` — the RANK-ONE carrier.  The
window hierarchy therefore re-derives the CORE A capstone (all arithmetic
routes meet at rank one) by pure subgroup theory, independently of the
Kostant cusp computation.  (iii) Every p-divisible element of `H` is
elliptic (`ell(g^(p^n)) = p^n ell(g)`), so there are no mixed solenoidal
Heisenberg subgroups, and characters with `delta_e` vertex restriction
vanish on every elliptic element: the enemy's freedom is carried entirely
by hyperbolic (irreducibly multi-t-block) elements.
```

### C.4  `research/amenable-carrier-windows-are-character-transparent-proof.md`

```markdown
---
rg: 2
id: amenable-carrier-windows-are-character-transparent-proof
kind: route
title: Amenable coset wreaths plus component averaging build the local countermodels
target: amenable-carrier-windows-are-character-transparent
requires: [heisenberg-solenoid-trace-torsion-dichotomy]
artifacts:
  - research/artifacts/noncommutative-solenoid-unique-trace-memo-2026-08-22.md
---

Window `E_A -> W_A`: send `A` to the base copy and `t` to the lamp at the
base coset (the lamp commutes with the stabilizer `A cap Lambda`, so the
HNN relation maps to a true relation; surjectivity because the lamps are the
`A`-translates).  For amenable `A`, `W_A` is amenable, so EVERY trace of
`W_A` has hyperfinite GNS; pull back `delta_e^(W_A)` and decompose into
extremal components (pullbacks of extremal components — kernel elements act
trivially in GNS — so factorial, and hyperfinite a.e.).  For `A = N`:
components restrict to `N` as a.e. CANONICAL aperiodic traces, because the
component central measures average to Haar and torsion mass integrates to
`Haar(T_p) = 0` (torsion-dichotomy input).  Failure of letter-centrality on
a positive-measure set: for `n = a(1/p)`, the word `t^-1 n^-1 t n` maps to a
product of two distinct lamps, so the average of `Re sigma_x` over
components is 0 while each is `<= 1`; Markov gives measure `>= 1/4` where
`Re <= 1/2`.  Intersect with the co-null canonical set.  Full details and
the elliptic/p-divisibility lemma: THE MEMO, Sections B.2 and B.4.
```

### C.5  `research/sl2-carrier-vanishing-branch-character-collapse.md`

```markdown
---
rg: 2
id: sl2-carrier-vanishing-branch-character-collapse
kind: claim
title: Vanishing-branch factorial hyperlinear characters of the rank-one carrier centralize the letter
artifacts:
  - research/artifacts/noncommutative-solenoid-unique-trace-memo-2026-08-22.md
distinct_from:
  hnn-carrier-factorial-character-collapse: that is the n >= 3 carrier claim with the regular-restriction hypothesis; this is the n = 2 carrier with the strictly weaker vanishing-off-center restriction hypothesis (needed because ergodic components only preserve the vanishing-branch shape), and by the corner-window route it IMPLIES the n >= 3 claim — the two are now ordered, not parallel.
  relative-commutant-collapse-for-sl2-pair: that is the operator form quantifying over every unitary of a matrix ultraproduct commutant with regular restricted trace; this quantifies over factorial hyperlinear characters of ONE countable group, the form character rigidity and charmenability speak, and it suffices for the SL_3 goal via the window reduction rather than via co-density of the SL_2 pair alone.
  no-exact-quasi-regular-leak: that excludes the single extreme exact profile `1_Lambda`; this quantifies over ALL vanishing-branch factorial enemies of the rank-one carrier, intermediate between the exact form and the full collapse.
---

Let `E_2 = < SL_2(Z[1/p]), s | [s, SL_2(Z)] = 1 >`.  Claim (OPEN): every
factorial hyperlinear character `sigma` of `E_2` whose restriction to
`SL_2(Z[1/p])` vanishes off the center `{±I}` satisfies

    sigma(s^-1 g^-1 s g) = 1   for all g in SL_2(Z[1/p]).        (R1)

By `sl3-collapse-from-rank-one-corner-window`, (R1) implies the full n = 3
carrier collapse (FC1), hence (RC3), hence the goal.

## Attempts

- **Why this exact hypothesis.**  Ergodic components of the SL_3 enemy's
  corner-window restriction are factorial, hyperlinear (corner-of-
  ultraproduct + martingale + weak-* closedness of hyperlinear traces), and
  a.e. vanishing-branch on the corner by Peterson-Thom character rigidity of
  `SL_2(Z[1/p])` (arXiv:1303.4007, Thm 2.6: extremal characters factor
  through finite quotients or vanish off center) plus a congruence-escape
  averaging that kills the finite-quotient mass.  The hypothesis is exactly
  what survives decomposition; the regular-restriction form would be too
  strong to consume.
- **Countermodel ledger.**  The amenable-wreath transparency countermodels
  (`amenable-carrier-windows-are-character-transparent`) do NOT apply: the
  relevant wreath over `SL_2(Z[1/p])/SL_2(Z)` has non-amenable stabilizers,
  and its hyperlinearity is the Kun-Thom wall; a hyperlinear such wreath
  would refute (R1) (pull back the regular character), so (R1) and CE of
  that coset Bernoulli stand or fall together — the recorded pairing of
  `coset-bernoulli-ce-refutes-relative-commutant-collapse`, now at rank one
  in character form.
- **Falsification gate.**  If `E_2` is hyperlinear, run the reduction
  route's component argument on the central components `tau_omega` of
  `delta_e^(E_2)` (they satisfy `tau_omega(g_j) = 0` off the center and
  `tau_omega(s^-1 g^-1 s g) = 0` for `g notin SL_2(Z)`, since Britton keeps
  that word off `{±I}`): a positive measure of their ergodic components are
  vanishing-branch factorial hyperlinear characters violating (R1).  So (R1)
  asserts, inter alia, that the rank-one HNN
  carrier is not hyperlinear: this is a goal-reaching claim, and refuting it
  means EITHER exhibiting a hyperlinear vanishing-branch enemy (killing the
  whole character lane at rank one) OR proving `E_2` hyperlinear (redirecting
  the program), both informative.
- **Known consistent sectors.**  Finite-dimensional characters of `E_2` are
  letter-central by co-density of the pair
  (`sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`), and are excluded by
  the vanishing hypothesis anyway.  Tree deformations pass through the enemy
  exactly as recorded for the n >= 3 carrier: the enemy respects the
  Bass-Serre geometry, so IPP/spectral-gap arguments see nothing.
- **Toolkit pointer.**  The subgroup `SL_2(Z[1/p])` here has character
  rigidity (PT) and property (tau); what is missing is any rigidity
  statement for characters of the HNN CARRIER over the pair — the same
  virgin territory the n >= 3 node records, now in the weakest form the
  program needs.  The two-adic tower / Iwahori far-sector machinery is the
  natural quantitative attack surface, since a vanishing-branch enemy's
  finite shadows are exactly the doubly-deep solenoid-Haar plateaus already
  charted.
```

### C.6  `research/sl3-collapse-from-rank-one-corner-window.md`

```markdown
---
rg: 2
id: sl3-collapse-from-rank-one-corner-window
kind: route
title: The SL_2 corner window reduces the SL_3 carrier collapse to the rank-one vanishing branch
target: hnn-carrier-factorial-character-collapse
requires: [sl2-carrier-vanishing-branch-character-collapse]
artifacts:
  - research/artifacts/noncommutative-solenoid-unique-trace-memo-2026-08-22.md
---

Let `tau` be a factorial hyperlinear character of the n = 3 carrier `H`
with `tau|_Gamma = delta_e`.  Steps, each unconditional:

1. **Corner window.**  `Delta =` upper-left `SL_2(Z[1/p])` corner;
   `E := <Delta, t>_H ~= <SL_2(Z[1/p]), s | [s, SL_2(Z)] = 1>` by Britton
   (non-integral corner entries leave `Lambda`).  `rho := tau|_E` is a
   hyperlinear trace (GNS is a subalgebra of the embedded `M_tau`) with
   `rho|_Delta = delta_e`.
2. **Components.**  Ergodic decomposition `rho = int sigma_x`: a.e.
   `sigma_x` is factorial and HYPERLINEAR — corners of matrix ultraproducts
   are matrix ultraproducts, martingale convergence identifies `sigma_x` as
   a weak-* limit of corner traces, and hyperlinear traces are weak-*
   closed.
3. **Corner classification.**  Peterson-Thom (arXiv:1303.4007 = Crelle 716
   (2016) 207-228, Thm 2.6): extremal characters of `SL_2(Z[1/p])` (a
   localization with infinitely many units) factor through finite quotients
   or vanish off `{±I}`.  Pick `g_j != ±I` in the intersection of all
   normals of index <= j; every finite-quotient extremal is eventually 1 on
   `g_j`, every vanishing-branch extremal is 0 there, so
   `lim_j sigma_x(g_j) =` the finite-quotient mass `f_x`, and
   `int f_x = lim_j rho(g_j) = lim_j delta_e(g_j) = 0`: a.e. component is
   vanishing-branch on the corner.  (No CSP is used; index-bounded cores
   suffice.)
4. **Consume the hole and regenerate.**  The target's input
   `sl2-carrier-vanishing-branch-character-collapse` applies to a.e.
   `sigma_x`, giving letter-centrality against `Delta`; integrate, use
   Cauchy-Schwarz equality against the separating trace vector, and
   `Gamma = <Lambda, Delta>` (signed Weyl conjugates of the corner roots
   give all root groups; elementary generation over the Euclidean `Z[1/p]`)
   to get `[pi_tau(t), pi_tau(Gamma)] = 0`, i.e. (FC1).

Full proofs of the lemmas (weak-* closedness, component hyperlinearity,
congruence-escape averaging): THE MEMO, Section B.5.  Value: with the
established `rcc-carrier-character-face-compression`, this route makes the
whole SL_3 lane rest on ONE rank-one character claim — an independent
subgroup-theoretic confirmation of the CORE A capstone, and the first
strict ordering between the n = 2 and n >= 3 carrier collapse claims.
```

---

## Section D.  Literature trust surface

Verified directly from sources during this task:

- **[LP] F. Latremoliere, J. Packer, "Noncommutative solenoids", New York
  J. Math. 24A (2018), 155-191; arXiv:1110.6227.**  Read from the arXiv PDF
  (pp. 1-16).  Used and verified: Thm 2.1 (parameter group `Xi_N`, the
  sequences with `N nu_(n+1) = nu_n + k`, `Xi_N ~= S_N`); Thm 2.3 (canonical
  multiplier `Psi_alpha((p1/N^k1, p2/N^k2),(p3/N^k3, p4/N^k4)) =
  exp(2 i pi alpha_(k1+k4) p1 p4)`); Thm 2.12 (symmetrizer nontrivial iff
  finite range iff periodic; explicit form `(bZ[1/N])^2`); Rem 2.14
  (rational aperiodic parameters exist, `alpha_n = 1/N^n`, symmetrizer
  trivial); Def 3.1, Prop 3.3 (crossed-product picture); Thm 3.5
  (simplicity iff aperiodic); Thm 3.6 (dual-invariant trace, unique when
  simple); Thm 3.7 (direct limit of rotation algebras `A_(alpha_(2n))`,
  generators to `N`-th powers, `N^2 alpha_(2n+2) = alpha_(2n) + r_n`).
  CORRECTION to the task sheet: the criterion is aperiodicity, NOT
  irrationality; rational aperiodic solenoids are simple with unique trace.
- **[PT] J. Peterson, A. Thom, "Character rigidity for special linear
  groups", J. reine angew. Math. 716 (2016), 207-228; arXiv:1303.4007.**
  Read from the author PDF (pp. 1-5, 14-17).  Used and verified: the SL_2
  main theorem (proof of Thm 2.6 concluding "τ(g) = 0 for any non-central
  element" unless τ factors through a finite quotient; Prop 2.8 dichotomy
  finite-quotient-or-weak-mixing) for `SL_2(B S^-1)` with infinitely many
  units — `Z[1/p]` qualifies (units `± p^Z`).  Also verified en passant:
  their Thm 2.10 records Bekka's `SL_n(B S^-1)`, `n >= 3` version.
- Standard facts used without page-level verification (folklore tier, all
  with proofs or proof sketches in the memo where load-bearing): Bochner
  duality for discrete abelian groups; Kleppner's identification of `H^2` of
  discrete abelian groups with antisymmetric bicharacters (as quoted inside
  [LP, Sec. 2]); Serre's Bass-Serre theory (`ell(g^k) = |k| ell(g)`,
  elliptic = conjugate into vertex groups, Britton's lemma); elementary
  generation `SL_3(R) = E_3(R)` for Euclidean `R` (row reduction; `Z[1/p]`
  is a localization of a Euclidean domain); amenable groups have injective
  group von Neumann algebras (hence all their traces are hyperlinear);
  corners of matrix ultraproducts are matrix ultraproducts; martingale
  convergence.  The amenable-STABILIZER soficity strengthening quoted in
  Corollary B6 is used only for the non-amenable-`A`/amenable-edge extension
  of the transparency fence, is flagged as the recorded in-graph fact (the
  Kun-Thom wall is the non-amenable-stabilizer case), and nothing else
  depends on it — the amenable-`A` case, which is all Sections B.4-B.5 use,
  is unconditional.
- NOT relied on (context only): Carey-Moran characters of nilpotent groups;
  Levit-Vigdorovich arXiv:2206.02268 (already recorded in-graph).

Gaps ledger: the memo contains exactly one OPEN input, (R1) = node C.5.
Everything else — Theorem A both directions, Propositions B2/B3/B4, Theorem
B5, Corollaries B6/B7 (amenable case), Lemmas L0/L1, Theorem B8 — is proved
in full above.
