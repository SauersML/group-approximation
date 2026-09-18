# Virtually Fuchsian packets and Zariski closures of Deligne witness packets (2026-09-17)

Lane d-sp4 (swarm-0917), role inverter. Target: `sp4-schur-kernel-meets-the-deligne-triple-class`.
Claims: `virtually-fuchsian-coefficients-have-zero-schur-kernel` (any group) and
`deligne-witness-packets-are-zariski-dense-or-hilbert-type` (for `Sp_4(Z)`).
Exact and numerical checks: `experiments/sp4-schur-zariski-closure-packets-2026-09-17/verify.py`,
output in `output.txt` (ends `ALL PASS`). The proofs do not depend on the numerics.

## 0. Notation and imported nodes

- `K_2(Q, w) = ker(H_2(Q; Z) -> H_2((Q * <t>)/<<w>>; Z))` for `w in Q * <t>` with `deg_t(w) != 0`.
- A *multiplier class* of a group `S` is the class `beta_phi in H^2(S; U(1)) = Hom(H_2(S; Z), U(1))`
  pulled back from `PU(n) = U(n)/U(1)` along a homomorphism `phi : S -> PU(n)`, `n < infinity`.
- (PU) `projective-unitary-classes-vanish-on-schur-kernel`: for `Q` countable, `w` nonsingular and
  every `phi : Q -> T = U/A` (with `U = prod U(d_n)/N`, `A` the scalars), `beta_phi` vanishes on
  `K_2(Q, w)`. Take `d_n = n` constant and `N` the kernel of one coordinate projection. Then
  `T = PU(n)`, so every finite-dimensional multiplier class vanishes on `K_2(Q, w)`.
- (LOC) `schur-kernel-localizes-to-coefficient-subgroup`: if `B <= Q` contains the coefficients
  and `B -> (B * <t>)/<<w>>` is injective, then `K_2(Q, w) = iota_* K_2(B, w)`.
- (KL) `kervaire-laudenbach-holds-for-hyperlinear`: for hyperlinear `B` (for example residually
  finite `B`), `B -> (B * <t>)/<<w>>` is injective.
- (AM) `amenable-coefficients-have-zero-schur-kernel`.
- (MP2) `deligne-schur-witness-needs-maslov-carrying-packet`: packet pruning P1, P2, P2', P3, P4,
  each allowed on a finite-index subgroup `B_0`.

Standard facts used, recalled and not re-fetched:

- (F-UCT) `H^2(S; A) -> Hom(H_2(S; Z), A)` is onto, with kernel `Ext(H_1 S, A)`. This kernel is
  `0` for divisible `A` such as `U(1)` and `Q/Z`.
- (F-Hopf) For `S = <a_1, b_1, ..., a_g, b_g | prod [a_i, b_i]>` and `phi : S -> PU(n)` with lifts
  `A_i, B_i in U(n)`, `prod [A_i, B_i] = lambda I` and `<beta_phi, [S]> = lambda^{±1}`. The sign
  depends only on conventions.
- (F-top) A connected noncompact `n`-manifold `M` has `H_n(M; Z) = 0` (Hatcher, *Algebraic
  Topology*, Prop. 3.29).
- (F-Sel) Selberg's lemma: finitely generated subgroups of `GL_n` of a characteristic-`0` field are
  virtually torsion-free. This is used the same way in `finite-by-fuchsian-virtually-surface-proof`.
- (F-alg) Borel, *Linear Algebraic Groups*; Humphreys:
  - in characteristic `0` the unipotent radical of a `Q`-group is defined over `Q`;
  - `H(R)` has finitely many components;
  - `sl_2`-triples in `sp_4` are classified by the partitions `[2,1,1]`, `[2,2]`, `[4]` (odd parts
    with even multiplicity);
  - real forms of `SL_2` are `SL_2(R)` and `SU(2)`.

## 1. Lemma IND (induction of projective representations through a twisted group algebra)

**Lemma IND.** Let `S <= B` have finite index, and let `c` be a normalized `U(1)`-valued 2-cocycle
on `B`. Suppose `[c|_S] = beta_phi` for some `phi : S -> PU(n)`. Then `[c] = beta_rho` for a
homomorphism `rho : B -> PU(n [B : S])`.

*Proof.*

1. Lift `phi` to `pi : S -> U(n)`. Its multiplier is cohomologous to `c|_S`. After multiplying
   `pi` by a function `S -> U(1)`, `pi(s) pi(s') = c(s, s') pi(ss')` holds exactly.
2. Let `C^c[B]` have basis `u_g` with `u_g u_h = c(g, h) u_{gh}`, and let `C^c[S]` be its span of
   the `u_s`, `s in S`. The formula for `pi` makes `C^n` a left `C^c[S]`-module.
3. Choose a transversal `r_1, ..., r_m` of `B/S`. Since `u_{r_i} u_s = c(r_i, s) u_{r_i s}` with
   `|c| = 1`, `C^c[B]` is a free right `C^c[S]`-module with basis `u_{r_i}`.
4. Put `V = C^c[B] (x)_{C^c[S]} C^n = (+)_i u_{r_i} (x) C^n`, of dimension `nm`. Left
   multiplication gives an algebra map `C^c[B] -> End(V)`, so `rho(g) := u_g .` satisfies
   `rho(g) rho(h) = c(g, h) rho(gh)`.
5. Explicitly, if `g r_j = r_i s`, then `rho(g)` sends block `j` to block `i` by
   `c(g, r_j) conj(c(r_i, s)) pi(s)`. That map is unitary, and `rho(g)` permutes blocks, so
   `rho(g)` is unitary for the orthogonal sum of the standard inner products.
6. Hence `rho : B -> PU(nm)` has multiplier `c`. QED.

Part C of `verify.py` checks the explicit block formula numerically on `B = (Z/3)^2 x| Z/2`,
`S = (Z/3)^2`: the cocycle identity holds exactly and the representation is unitary.

## 2. Theorem A: virtually Fuchsian coefficients have zero Schur kernel

**Definition.** A group `S` is *projectively visible* if every element of `Hom(H_2(S; Z), Q/Z)`,
viewed in `Hom(H_2(S; Z), U(1)) = H^2(S; U(1))`, is a finite-dimensional multiplier class.

**Lemma VIS.** Finite groups are projectively visible. So is every torsion-free discrete subgroup
`S` of `PSL_2(R)`.

*Proof.*

- *Finite groups.* The twisted regular representation realizes every class. This is
  `projective-unitary-classes-vanish-on-schur-kernel`, "twisted regular representations realize
  every class in `Hom(H_2 Q, U(1))`".
- *Fuchsian groups.* `S` acts freely and properly on `H^2`, since point stabilizers are compact
  and `S` is discrete and torsion-free. So `M = H^2/S` is an orientable surface and a `K(S, 1)`.
  - If `M` is noncompact, `H_2(S; Z) = H_2(M; Z) = 0` (F-top), and there is nothing to realize.
  - If `M` is compact, it is a closed orientable surface of genus `g >= 1`. In fact `g >= 2` by
    Gauss--Bonnet. Here `H_2(S) = Z[M]`, so a class is determined by one value
    `exp(2 pi i p/q)`.
  - Send `a_1 -> X_q^k` and `b_1 -> Y_q`, with `X_q = diag(zeta_q^r)` and `Y_q` the cyclic shift,
    and send all other generators to `1`. The relator is sent to `[X_q^k, Y_q] = zeta_q^k I`, a
    scalar, so this defines `phi : S -> PU(q)`.
  - By (F-Hopf) its class evaluates to `zeta_q^{±k}` on `[M]`. Every `k` occurs, so every class
    is realized.
  - Part D of `verify.py` checks the commutator identity for `q = 2, 3, 5` on genus 2.

QED.

**Theorem A.** Let `Q` be a group and `w in Q * <t>` with `deg_t(w) != 0`. Let `B` contain the
coefficients of `w`, and suppose:

- `B` is countable and hyperlinear;
- some finite-index `S <= B` is projectively visible.

Then `K_2(B, w) = 0` and `K_2(Q, w) = 0`. In particular this holds when `B` is virtually a
torsion-free Fuchsian group. The hyperlinearity hypothesis is automatic for finitely generated such
`B`, which are residually finite: `S` is finitely generated linear, and finite-index overgroups of
residually finite groups are residually finite.

*Proof.*

1. Let `0 != x in H_2(B; Z)`. Since `Q/Z` is an injective cogenerator of abelian groups, there is
   `f : H_2(B) -> Q/Z` with `f(x) != 0`.
2. By (F-UCT), `f` is the evaluation of a class `[c] in H^2(B; U(1))` whose values lie in
   `Q/Z <= U(1)`.
3. The restriction `[c|_S]` corresponds to `f o iota_*`, again `Q/Z`-valued. By visibility it is a
   multiplier class of some `phi : S -> PU(n)`.
4. By Lemma IND, `[c] = beta_rho` for some `rho : B -> PU(n [B : S])`.
5. By (PU) applied to `B`, `beta_rho` vanishes on `K_2(B, w)`. So `x` is not in `K_2(B, w)`.
6. Hence `K_2(B, w) = 0`. By (KL), `B -> (B * <t>)/<<w>>` is injective, and (LOC) gives
   `K_2(Q, w) = iota_* 0 = 0`.

For virtually Fuchsian `B`, take `S` torsion-free by (F-Sel) and apply Lemma VIS. QED.

**What is new here, and what is not.**

- The existing consequence of (AM) ("the killed class must be invisible in the second homology
  of every finite quotient of the coefficient subgroup") is the same kind of criterion as (PU).
- Theorem A proves that visibility for a class of packets not reached by any recorded node:
  - virtually Fuchsian groups *with torsion*, such as cocompact triangle groups and arithmetic
    quaternionic unit groups;
  - these have `H_2(-; Q) = Q`, so P1 fails;
  - they are not locally indicable, even modulo their finite normal subgroups of order prime to
    3, so `locally-indicable-packets-have-zero-schur-kernel` fails;
  - they have torsion, so Forester--Rourke does not apply;
  - they are non-amenable, so (AM) does not apply as stated.
- The conclusion is integral: all of `K_2(Q, w)` vanishes, not only its Maslov part.

## 3. Theorem B: Zariski closures of Deligne witness packets

Let `Gamma = Sp_4(Z)`, `V = Q^4`, and let `B <= Gamma` be finitely generated. Let `H` be the
identity component of the Zariski closure of `B` in `Sp_4`. It is a connected `Q`-group, `B`
normalizes it, and `B cap H(Q)` has finite index in `B`.

**Theorem B.** If `H` is not `Sp_4` and not a `Q`-simple form of `SL_2 x SL_2` with
`H(R) = SL_2(R) x SL_2(R)`, then every nonsingular `w in Gamma * <t>` whose coefficients lie in
`B` satisfies `alpha_H(K_2(Gamma, w)) = 0`. So `w` is not a witness.

Also, whatever `H` is, if `B` is virtually a torsion-free Fuchsian group, then
`K_2(Gamma, w) = 0` (Theorem A).

*Proof: case analysis on `H`.*

**(C0) `H` not reductive.**
- `U = R_u(H) != 1` is a `Q`-group (F-alg), and `B` normalizes it.
- `V^U` is nonzero, because a unipotent group fixes a vector. It is proper, because `U != 1`. It is
  rational, because it is cut out by the `Q`-points of `U`, which are Zariski dense in `U`.
- So `B` preserves a proper nonzero rational subspace: P2.

**(C1) `H` a torus.** `B` is virtually abelian, hence amenable: (AM).

**(C2) `H` reductive with `H' = [H, H] != 1`.**

Over `C`, `H'` is semisimple of rank at most 2 with a faithful 4-dimensional symplectic
representation, so its type is `A1`, `A1 x A1`, `A2`, `B2 = C2` or `G2`:

- `G2` has no faithful representation of dimension below 7.
- The 4-dimensional faithful representations of `SL_3` are `3 + 1` and `3* + 1`. They are not
  self-dual, so they carry no invariant symplectic form. `PGL_3` has none of dimension below 8.
- `C2` of dimension 10 inside `Sp_4` is `Sp_4`.
- For `A1 x A1`, `V1 (x) V1` carries only a symmetric form. The only faithful symplectic option is
  `W_1 + W_2`, the orthogonal sum of two symplectic planes.
- For `A1`, self-dual 4-dimensional representations with a nondegenerate invariant alternating
  form are `V_0^2 + V_1` (`[2,1,1]`), `V_1^2` (`[2,2]`) and `V_3` (`[4]`). In `V_2 + V_0` the
  orthogonal types occur with odd multiplicity.

- **(C2a) `[2,1,1]`.** `V^{H'}` is a rational symplectic plane, and `B` preserves it: P2.

- **(C2b) `[4]`, principal.**
  - `V` is irreducible for `H'`, so its centralizer is `{±1}` and `H = H'`.
  - If `H(R) = SU(2)`, `B cap H(R)` is discrete in a compact group, hence finite: (AM).
  - Otherwise `H(R) = SL_2(R)`, and `B_0 = B cap H(R)` is a discrete subgroup of `SL_2(R)`. Its
    image in `PSL_2(R)` is Fuchsian with kernel of order at most 2. By (F-Sel), `B_0` has a
    torsion-free finite-index subgroup, which maps isomorphically onto a torsion-free Fuchsian
    group. Theorem A applies.

- **(C2c) `[2,2]`.**
  - Over `C`, `V = W (x) U` with `H' = SL(W)`, `omega = omega_W (x) g`, and `g` symmetric
    nondegenerate on the 2-dimensional multiplicity space `U`.
  - The centralizer of `H'` in `Sp(V)` is `O(U, g)`. So `H = H' T` with `T = Z(H)^0` either
    trivial or equal to `SO(U, g)`, a 1-dimensional `Q`-torus.
  - *`T` nontrivial and `R`-split.*
    - `T(R) = R^*` has real weight spaces `V_chi = W (x) u_+` and `V_{-chi} = W (x) u_-`, each of
      dimension 2.
    - `omega(tv, tv') = chi(t)^2 omega(v, v')` forces `V_chi` to be isotropic, so it is a real
      Lagrangian.
    - `H(R)^0` commutes with `T` and preserves `V_chi`. The finite-index subgroup
      `B_0 = B cap H(R)^0` does too: P3.
  - *`T` trivial or `R`-anisotropic.*
    - `H(R)^0 = H'(R) T(R)` with `T(R)` compact or trivial.
    - The quotient `H(R)^0 -> H'(R)/(H'(R) cap T(R)Z)` has compact kernel, and maps onto
      `PSL_2(R)` or onto a compact group.
    - Discrete subgroups map to discrete subgroups with finite kernel along a quotient by a compact
      normal subgroup: if `pi(gamma_n) -> 1`, choose `k_n -> k` in the kernel with
      `gamma_n k_n -> 1`; discreteness makes `gamma_n` eventually constant in the kernel.
    - So `B_0 = B cap H(R)^0` is finite, or finite-by-Fuchsian. By (F-Sel) it has a torsion-free
      finite-index subgroup, which meets the finite kernel trivially and is therefore
      isomorphic to a torsion-free Fuchsian group. Theorem A or (AM) applies.

- **(C2d) `A1 x A1` on `W_1 + W_2`.**
  - The centralizer of `H'` is `{±1} x {±1}`, so `H = H'`.
  - `Gal(Qbar/Q)` permutes the two `H'`-isotypic lines `{W_1, W_2}`.
  - *Both fixed.* `W_1` is a rational symplectic plane: P2.
  - *Swapped, with field of definition `K` of `W_1` quadratic.*
    - *`K` imaginary.* Complex conjugation swaps the factors and
      `H(R) = {(g, conj g)} = SL_2(C)`, connected and simply connected. `B_0 <= H(R)`, and
      P4 applies with `S = H(R)`.
    - *`K` real.* `H(R) = H_1(R) x H_2(R)`, each factor `SL_2(R)` or `SU(2)`.
      - Two compact factors: `B_0` is finite, (AM).
      - Exactly one compact factor: project to the noncompact factor with compact kernel. As in
        (C2c), Theorem A applies.
      - Two noncompact factors: the Hilbert type, excluded by hypothesis.

- **(C2e) `H = Sp_4`.** Excluded by hypothesis.

In every non-excluded case, either all of `K_2(Gamma, w)` vanishes, or `B` is not Maslov-carrying.
Then `<e, K_2> = 0` and `alpha_H = <e, -> mod 3` vanishes on `K_2` (MP2). QED.

**Corollary (witness checklist, refined).** Let `w` be a witness and `B_c` the subgroup generated
by its coefficients. Then:

- the identity component of the Zariski closure of `B_c` is `Sp_4`, or a Hilbert type
  `Q`-simple form of `SL_2 x SL_2` with real points `SL_2(R)^2` (field of definition of the
  invariant planes real quadratic);
- `B_c` is not virtually a torsion-free Fuchsian group, even when its Zariski closure is `Sp_4`
  (thin surface packets die).

## 4. An explicit packet that survived every recorded criterion and dies here

Parts A and B of `verify.py`.

**Setup.**
- `D = (-1, 3)_Q`, with `i^2 = -1`, `j^2 = 3`, `k = ij`. `D` is a division algebra, since
  `x_0^2 + x_1^2 - 3x_2^2 - 3x_3^2` is anisotropic over `Q_3`, and it is indefinite.
- `Lambda = Z<1, i, j, k>`, with trace dual `Lambda^# = span(1/2, i/2, j/6, k/6)`.
- `mu = -(i/2 + j/6 + k/6)`, a pure quaternion with `nrd(mu) = 1/12 > 0`.
- `f(x, y) = trd(mu conj(x) y)` is integral, alternating and unimodular on `Lambda`, with Gram
  matrix `[[0,1,-1,-1],[-1,0,1,-1],[1,-1,0,3],[1,1,-3,0]]` and Pfaffian `±1`.
- For `u in Lambda^1` (reduced norm 1), `f(ux, uy) = trd(mu conj(x) conj(u) u y) = f(x, y)`, and
  `u Lambda = Lambda`.
- So in an integral symplectic basis (found by the script), `B := Lambda^1` embeds in `Sp_4(Z)`.
  The script prints the images of `i` (order 4), `2 + j` and `2 + k` (trace 8, hyperbolic).

**Properties.**
- `H = D^1 = SL_1(D)` acting by left multiplication. This is type `[2,2]`, because over `R`
  `V = D (x) R = W (x) R^2`.
- Right multiplication by `Q(mu)^1` is the commutant torus. It is compact because `mu^2 < 0`
  (check A5), so this is the `omega + omega` configuration.
- The loop `cos theta + i sin theta` generates `pi_1(D^1(R)) = pi_1(SL_2(R))`, and its winding in
  `Sp_4(R)` is `2` (check B2; block `SL_2` gives `1`).
- `B = Lambda^1` is a cocompact arithmetic Fuchsian group with torsion (`i` has order 4). It is
  finitely generated.

**Why no recorded criterion prunes it.**
- *P1.* `H_2(B; Q) = Q`: `B/{±1}` acts cocompactly on `H^2` with orientable quotient, and rational
  homology is that of the quotient surface.
- *P2 and P2'.* A `B_0`-invariant rational subspace is invariant under the Zariski closure `D^1`,
  and `D^1(Q)` spans `D`. So it is a left `D`-submodule of `D`, hence `0` or `D`.
- *P3.* The `H(R)^0`-invariant 2-planes are `W (x) u`. They are isotropic only when `g(u, u) = 0`,
  which is impossible for definite `g`. Every finite-index `B_0` has the same `H`.
- *P4.* `B` is Maslov-carrying:
  - winding 2 gives `e|_B = 2 eps|_B`, with `eps` the class of the universal cover of `SL_2(R)`;
  - for a torsion-free finite-index surface subgroup `S` of genus `g_S`, the Milnor--Wood
    equality for Fuchsian groups (recalled) gives `<eps, [S]> = ±(g_S - 1) != 0`;
  - so `<e, iota_*[S]> != 0`, and no finite-index subgroup lies in a winding-zero connected
    subgroup.
- *Howie.* `B` has torsion, and `B/{±1}` still has torsion. So `B` is not locally indicable modulo
  a finite normal subgroup.
- *Forester--Rourke.* Needs torsion-free packets.
- *(AM).* `B` is non-amenable.

The 2026-09-16 notes list `omega + omega` and the principal `SL_2` as surviving every criterion.
By Theorem A, every equation with coefficients in this `B` has `K_2(Sp_4(Z), w) = 0`.

## 5. Open edges this settles, and what survives

**Settled.**
- *Principal `SL_2` packets (winding `-2`)*: (C2b).
- *`omega + omega` packets, `D^1` with `nrd mu > 0`*: (C2c) and Section 4.
- *"Real lines or real symplectic planes with rational hull `Q^4`"*:
  - a packet fixing a real line has `H` preserving a line, so `H` is non-reductive, a torus, or
    `[2,1,1]`, all pruned;
  - a real symplectic plane with full rational hull forces (C2d) with `K` real quadratic, which
    is Hilbert type, or one of the pruned cases.
- *"Classification of winding-zero subgroups"* is superseded: winding is no longer the relevant
  invariant.

**Survivors.**
- **(S1)** Zariski-dense packets `B_c <= Sp_4(Z)` that are not virtually torsion-free Fuchsian:
  finite-index subgroups, thin non-surface packets.
- **(S2)** Hilbert type packets inside `SL_1(D)(O_K)` for a real quadratic `K` split at both real
  places, not virtually Fuchsian. Examples are the Hilbert modular groups `SL_2(O_K)`, windings
  `(1, 1)`.

**Invariant, and where each killed member dies.**
- The invariant is the real rank and type of the Zariski closure, together with projective
  visibility of the Fuchsian part.
- Every packet whose closure has a single noncompact simple factor with compact commutant dies at
  Step 5 of Theorem A: (PU) applied to the representation induced through `C^c[S] <= C^c[B]`.
- Every other non-surviving packet dies at P2, P3 or P4.

## 6. Approaches considered and dropped (recorded dead ends)

- *Bounded cohomology extension of `e|_B` across the adjunction.* For virtually surface `B` this
  reduces to the rational extension question, and adds nothing beyond Theorem A.
- *Finite-cover transfer to a square system.* Already dead (target Attempt 7, section 5 of
  `sp4-schur-li-packets-2026-09-17.md`).
- *Amplified hosts `Sp_(4m)(R)`.* No theorem controls solvability there, and MP3 covers only block
  hosts. Not pursued.
- *Extending Theorem A to "virtually good" packets.* This would use the extension lemma of
  Grunewald--Jaikin-Zapirain--Zalesskii (residual finiteness of finite extensions of good
  residually finite groups). It is not imported: the citation was not re-read. For (S2) it would
  not help anyway: the real-place universal covers of `SL_2(R)^2` give Deligne-type non-residually
  finite extensions of Hilbert modular groups, so these groups are not good. A goodness-based
  extension could at best remove thin good packets in (S1) or (S2).
