# Linear Gottschalk route: frontier on main's nonsofic witnesses (2026-09-13)

This is lane `hl-gottschalk-linear`. It changes no node's status. Every "established" below refers to a claim ESTABLISHED on main and not independently reviewed.

## 0. Criterion and scope

- **Refutation direction.** `stable-finiteness-failure-refutes-surjunctivity` (established): if `BA = I_n != AB` in `M_n(k[G])` for a finite field `k`, then `G` is not surjunctive.
  - The converse, that L-surjunctivity over `K` is equivalent to stable finiteness of `K[G]` (Ceccherini-Silberstein--Coornaert), was not re-pinned at source in this lane. The refutation direction does not need it.
- **Characteristic zero is dead.** Kaplansky's theorem gives stable finiteness for every group, so only positive characteristic can carry a linear witness.
- **Sofic groups are dead.** `linear-sofic-group-algebra-is-stably-finite` covers every sofic group. So a linear witness needs a nonsofic group, and its supports generate a nonsofic subgroup.

## 1. Census of the linear route

| Witness group on main | Characteristic `p` status | Deciding node |
|---|---|---|
| Kun--Thom wreath `Z/2 wr_(G/Gamma) G` | stably finite over all fields | `kun-thom-wreath-stably-finite` |
| Kun--Thom double `G *_Gamma G` and the trivial HNN extension | stably finite over division rings of char `p` | `nonsofic-witness-finiteness-over-modular-division-rings` |
| free wreath `(*_X Z) x| H`, amenable action | stably finite over division rings of char `p` | same node |
| Clifford cover `E_S`, `p = 2` | stably finite (square-zero kernel) | `kun-thom-clifford-cover-nonsurjunctive`, Attempts |
| Clifford cover `E_S`, odd `p` | iff the skew ring `A_S^(p)` is: **OPEN** | `kun-thom-clifford-skew-rings-are-stably-finite` / `clifford-cover-anti-half-skew-ring-not-directly-finite` |
| Deligne triple cover `E_3`, `p = 3` | stably finite | `deligne-triple-cover-ternary-group-algebras-are-stably-finite` |
| Deligne triple cover `E_3`, `p != 3` | iff the twisted algebras `F^(w^(ja))[Sp_4(Z)]` are: **OPEN** | `deligne-triple-cover-group-algebras-are-stably-finite` / `deligne-twisted-group-algebra-is-not-stably-finite` |
| binary Leavitt unit group `R^x`, `F_2` | **OPEN**; direct iff stable | `leavitt-group-algebra-not-stably-finite`, `leavitt-stable-finiteness-equals-direct-finiteness` |
| ternary Leavitt unit group `G_3`, anti-central summand `S_-` | witness iff `(K_0(S_-), [eps_-])` has no state: **OPEN** | `ternary-anti-central-unit-class-is-nonpositive`, `twisted-leavitt-corner-fullness-equals-absence-of-k0-states` |
| torsion-free double `D_3`, integer-lamp wreath `W_hat` | reduce to the Kazhdan covers `G_OW`, `G_hat`: **OPEN** | `nonsofic-witness-finiteness-over-modular-division-rings`, items 3--4 |
| Fournier--Facio torsion-free group | **OPEN**, no reduction on record | `fournier-facio-group-is-nonsofic` |
| Higman's group `H` (soficity unknown) | **OPEN** | `higman-group-algebra-not-stably-finite` |

## 2. Rank functions and rigidity

This section answers step 2 of the directive using established nodes only.

1. **Faithful rank functions kill witnesses.** Take any ring `R` with a Sylvester matrix rank function `rk` that is positive on nonzero idempotents, and suppose `BA = I_n` in `M_n(R)`.
   - `E = I_n - AB` is idempotent.
   - `B(AB)A = (BA)(BA) = I_n`, so `rk(AB) >= rk(B(AB)A) = n`, and hence `rk(AB) = n`.
   - For complementary idempotents, `rk(E) + rk(AB) = rk(I_n) = n`, so `rk(E) = 0`.
   - Hence `E = 0`, so such an `R` is stably finite.
   - A linear witness therefore requires that no Sylvester rank function on `k[G]` is positive on the defect idempotent.
2. **The ternary Leavitt gate is sharper.** For `G_3 = L_(F_3)(1,2)^x` the established chain is:
   - a witness exists iff `(K_0(S_-), [eps_-])` admits no state (`anti-central-state-obstruction-equals-stable-finiteness`, `twisted-leavitt-corner-fullness-equals-absence-of-k0-states`);
   - any characteristic-three rank model of `G_3` moving `z = -1` yields a state (`anti-central-rank-models-kill-ternary-corner-witnesses`).
   So excluding every such rank model is **necessary** for a witness, and it is **not known to be sufficient**. What is needed is the absence of all `K_0` states. Equivalently, relative positivity of the lifted trace must fail (`anti-central-state-exists-iff-lifted-trace-relatively-positive`).
3. **Kun--Thom rigidity does not transfer to the linear route.**
   - The rigidity is relative property (T) acting on permutation/Hamming models of a coset action.
   - On the Kun--Thom witnesses themselves (wreath, double, free wreath), modular stable finiteness is established (Section 1). So this rigidity cannot by itself produce a linear witness on them.
   - Property (T) gives no rank rounding over finite fields (`kazhdan-group-rank-models-admit-no-expander-decomposition`).
   - Sofic and locally finite data realize an exactly multiplicative anti-central defect profile `5/9` (`anti-central-sofic-data-cannot-force-defect-submultiplicativity`).
   - So a linear witness must live on a core with no residually-p-by-stably-finite decomposition, and must use identities inside a nonsofic subgroup.
4. **Searches already run.** Finite-support lift and corner searches on main are `experiments/kaplansky_affine_lift_search.py`, `kaplansky_joint_lift_search.py`, `kaplansky_collision_partner_search.py`, `kaplansky_prefix_corner_shear_search.py` and `kaplansky_minimum_lift_certificate.py`. None found a witness. A complement of a ternary corner witness has negative rational lifted trace, so it has no finite-support idempotent lift over `Z_3[G_3]` (`anti-central-lifted-trace-is-relatively-positive`, Attempts). Small-support lift searches miss it by construction.

## 3. A reduction for the Deligne core (elementary)

**Stable finiteness passes to finite-index overgroups, also for twisted group algebras.**

Let `Lambda <= G` have index `m`, `k` a field and `c` a 2-cocycle with values in `k^x`.

- `k^c[G]` is a free left `k^c[Lambda]`-module on a transversal `T`, `|T| = m`.
- Right multiplication by `x in k^c[G]` is `k^c[Lambda]`-linear. This gives a unital injective ring homomorphism `k^c[G]^op -> End_(k^c[Lambda])(k^c[G]) = M_m(k^c[Lambda])`.
- Direct finiteness of a ring `S` is equivalent to direct finiteness of `S^op`, since `ab = 1` in `S` iff `b.a = 1` in `S^op`. Also `M_n(S^op) = M_n(S)^op`.
- So if `k^c[Lambda]` is stably finite, then `M_n(k^c[G])^op = M_n(k^c[G]^op)` embeds unitally in `M_(nm)(k^c[Lambda])`, which is directly finite. Hence `k^c[G]` is stably finite.

**Consequence.** For `p != 3`, stable finiteness of `F^(w^(ja))[Sp_4(Z)]` follows from stable finiteness of the restricted twisted algebra over any finite-index `Lambda <= Sp_4(Z)`, for example a torsion-free principal congruence subgroup. By Deligne, the restricted multiplier is still not inflated from finite quotients. So this reduces the group but not the difficulty.

## 4. Exact gap

A linear Gottschalk counterexample on main's witnesses needs one of:

- **(a)** for `G_3`: absence of states on `(K_0(S_-), [eps_-])`, beyond every rank model. A state kills the route.
- **(b)** for `R^x`: a scalar pair over `F_2[R^x]`.
- **(c)** for `E_S`: a pair in the complete-graph Clifford skew ring over `F_3`.
- **(d)** for `E_3`: a pair in a twisted algebra of a finite-index subgroup of `Sp_4(Z)`, `p != 3`.
- **(e)** a pair over `F_p[G_OW]`, `F_p[G_hat]`, or the Fournier--Facio group.
- **(f)** a pair over `F_p[H]` for Higman's group, together with nonsoficity of the support subgroup.

Each needs a mechanism beyond residual-p separation, soficity, surjunctivity and division rings of fractions. For (a) specifically, what is needed is positivity or its failure for `Z_3`-valued lifted traces of infinite-support idempotent lifts, which no known principle orders.
