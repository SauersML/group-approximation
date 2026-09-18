# Cone map for `gl-n-q-embeds-in-fp-simple-group` (lane gq-map, 2026-09-17)

Target: for `n >= 2`, the countable group `GL_n(Q)` embeds in a finitely presented simple
group (BBMZ arXiv:2306.16356v3, Problem 5.3(5), p. 7); and Problem 2.7, an explicit natural
finitely presented overgroup. This map lists every Cairn tool found on `origin/main`
(as of 2598812b3 and later) that bears on the target, and says for each one whether
the root's obstructions O1–O3, or further obstructions found in the graph, kill it.

Verdicts:
- **KILLED**: cannot contain `GL_n(Q)`.
- **ALIVE**: can carry `GL_n(Q)` if its open premise is supplied.
- **REDUCES**: turns the target into a named sufficient statement.
- **CONTEXT**: useful input, no host.

Node ids are in backticks. Status is the node's own bold status line. "(unrev.)" means the
node says it was not independently reviewed.

## 0. One-paragraph summary

The graph has exactly one proved source of divisibility inside a finitely presented simple
group: `(Q,+) <= 2V` (`rationals-embed-in-brin-thompson-group-2v`, Kojima–Sheng, with an
explicit mixed-radix odometer proof; unrev.). `2V` is finitely presented and simple, so the
additive group `Q` is settled on main. There is **no** node for Belk–Hyde–Matucci's
`Q <= T̄ <= VA` or for "every countable abelian group embeds in `VA`" (see §6, gap G1).
Everything linear or self-similar is killed by O1. `VA` itself is killed for every `n >= 2` by the root's distortion obstruction O4 (Burillo–Felipe), and so are the stepping stones `Aff(Q)` and `U_3(Q)` in `VA`. Any host must contain exponentially distorted cyclic subgroups. What survives is:
1. the **type (A) machine** (§2), which turns *any* finitely presented group with a
   suitable action containing `GL_n(Q)` into a finitely presented simple overgroup, and
   has four concrete host shapes;
2. **Cantor-homeomorphism hosts**: `nV`, germ extensions of `V`, shells (§3);
3. **ring and Leavitt hosts** (§4), which reduce the target to algebra Boone–Higman for
   one countable decidable algebra, `F_2[GL_n(Q)]`, or to a finitely generated ring
   containing `Q`.

For `n >= 3`, the `nV` family depends on the open question whether `SL_3(Z)` embeds in
`2V` (§3.1).

## 1. Obstructions (root O1–O4, plus M1–M8 found in the graph)

| # | Obstruction | Source | Kills |
|---|---|---|---|
| O1 | `(Q,+) <= GL_n(Q)` is divisible, so it lies in no residually finite group | root | every linear group over a f.g. ring, every group acting faithfully on a locally finite rooted tree, so all self-similar hosts, RN coefficient groups `H`, the polynomial S-integer hosts |
| O2 | `n >= 3`: `SL_3(Z) <= GL_3(Q)` embeds in neither `V` nor `VA` | root (survey Thm 4.4, Rem. 4.12) | `V`, `VA` as hosts for `n >= 3` |
| O3 | `Q ⊄ V` (Higman: an infinite-order element of `V` has roots of only boundedly many orders) | root; restated in `rationals-embed-in-brin-thompson-group-2v` | `V` for all `n >= 2` |
| O4 | distortion: every infinite-order element of `VA` is undistorted, and `VA` contains no group with distorted cyclic subgroups (Burillo--Felipe arXiv:2605.09763v1, Thm 1, Cor. 5). `GL_2(Q) ⊇ BS(1,2)` has exponential distortion, and `U_3(Q)` has a quadratically distorted centre | root (added 2688d4128) | `VA` for **every** `n >= 2`, and also for the stepping stones `Aff(Q)`, `U_3(Q)`. More generally, **every host must contain exponentially distorted cyclic subgroups**, so `V` and `VA` are out, and any undistortion theorem is a kill. `2V` passes (Callard–Salo distortion elements). |
| M1 | f.g. simple unit groups mod central units of char-0 rings with **bounded divisibility** (condition (D)) contain no unipotent elements | `char-zero-algebra-unit-hosts-exclude-unipotents` (ESTABLISHED) | every char-0 ring host of the Zaremsky/matrix-unit type whose coefficient subring is a subgroup of a free `Z[1/m]`-module, or lies in `M_n(B_0)` for a f.g. commutative domain `B_0`. A host ring containing `Q` violates (D), so this does **not** kill Q-containing rings. It says the ring must have unbounded divisibility. |
| M2 | point germ groups of subgroups of `nV` are free abelian of rank `<= n` (slope cocycle) | `nv-point-germ-groups-embed-in-zn-by-slope` | realizing a natural action of `GL_n(Q)` with non-abelian point germs (e.g. on `P^{n-1}(Q_p)`, which has `SL_{n-1}` germs) as a closed invariant subsystem of any `nV`. It does not forbid an abstract embedding. |
| M3 | an f.g. simple subgroup of piecewise-projective homeomorphisms of a compact **interval** is trivial | `fg-simple-projective-interval-groups-are-trivial` (ESTABLISHED) | interval hosts for the simple envelope. Circle, line and Cantor hosts are untouched. |
| M4 | a finitely presented shell envelope forces a finitely presented near group `R_nu` (and the ascending-HNN gate) | `shell-envelope-fp-forces-fp-germ-group` (unrev.) | shells over non-f.g. inputs, and over f.g. inputs whose near group fails the gate |
| M5 | the type `[A_2]` / relative route does not avoid finite presentation: the simple quotient `SV_{G/K}` is f.p. iff `G/K` is | `abstract-btb-simple-quotient-fp-gate` | hoping that a non-faithful action removes the need for a f.p. faithful image |
| M6 | a commutative f.g. ring cannot contain `Q` (Nullstellensatz: a maximal ideal has a finite residue field) | folklore, no node (gap G5) | every commutative coefficient ring. A ring host containing `Q` must be noncommutative, or not f.g. |
| M7 | a unital ring embeds in a simple unital ring iff it has prime characteristic or torsion-free additive group | `ring-simple-envelope-characteristic-obstruction` | nothing here (`Z[G]`, `Q[G]`, `F_2[G]` all qualify). It is a calibration for ring lanes. |
| M8 | `EL_4(L)` has the central `{±I_4}` whenever `2 != 0` in `L`, so it is not simple | `rank-four-elementary-center-obstructs-simplicity` | any ring route claiming `EL_4(R)` simple in characteristic `!= 2`. Use `EL_n/Z`, or rank 3. |

Not an obstruction: `complexity-bounded-host-classes-are-not-universal` limits fixed-complexity
host classes for *all* inputs. `GL_n(Q)` has a polynomial-time word problem in its standard
enumeration, so the result places no restriction on one host for it.

## 2. The type (A) machine (ALIVE, the main engine)

**Core theorem.** `type-a-action-gives-boone-higman-for-subgroups` (Zaremsky arXiv:2405.18354,
Thm A / Cor. B, quoted verbatim). Let `Γ` be finitely presented and act faithfully on `S`,
with finitely generated point stabilizers and finitely many orbits on two-element subsets.
Then **every subgroup** of `Γ`, countable or not, embeds in the finitely presented simple
group `SV_Γ`. So G follows from **any** such `Γ ⊇ GL_n(Q)`. This is a REDUCTION with no
finite generation needed on the input side.

**Closure** (`boone-higman-type-a-class-closed-under-finite-extensions`, `B_A` = subgroups of
type (A) actors):
- subgroups and finite direct products;
- finite-index overgroups;
- free products (BFFHZ Cor. F);
- permutational wreath products over `G`-sets with finite stabilizers
  (`permutational-boone-higman-closed-under-wreath-products`, unrev.);
- finite lamps (`bh-type-a-class-closed-under-permutational-lamp-wreaths`).

**Four concrete host shapes, each ESTABLISHED as a criterion.** Each turns G into "find one
finitely presented object":

| Shape | Node | What to build for `GL_n(Q)` |
|---|---|---|
| H1: `Alt_fin(X) <= Γ <= Sym(X)`, `Γ` f.p. | `fp-finitary-alternating-overgroups-have-type-a-actions` (unrev.); the equivalence `permutational-boone-higman-iff-finitary-alternating-hosts` (unrev., stated for f.g. `H`; the direction host ⇒ embedding holds for any subgroup) | a f.p. permutation group containing all finitary even permutations of a countable `X` and a copy of `GL_n(Q)`. Only finite presentation is non-automatic (`decidable-groups-embed-in-fp-finitary-overgroups`, OPEN, lists the necessary conditions: the f.p. quotient `Q = Γ/(Γ∩FSym)` must contain `GL_n(Q)` modulo a locally finite normal subgroup. Since `PSL_n(Q)` is simple and the locally finite part of the centre `Q^x` is `{±1}`, every locally finite normal subgroup of `GL_n(Q)` lies in `{±I}` (gq-map, short argument, unrev.). So in effect `GL_n(Q)/{±I}` must sit in the f.p. quotient.) Models: Houghton `H_n` (`n >= 3`), `FSym(Ω) ⋊ SV_G` (`finitary-symmetric-extensions-of-oligomorphic-actions-are-fp`). |
| H2: f.p. `Γ` with `V <= Γ <= Homeo(C)` | `fp-cantor-groups-containing-v-type-a-iff-clopen-stabilizer-fg` (unrev.) | a f.p. Cantor group containing standard `V` and `GL_n(Q)`, with **one** finitely generated clopen-set stabilizer. The action on clopen sets has at most 5 orbits on pairs automatically. |
| H3: f.p. full, clopen-transitive `D <= Homeo(Y)` | `fp-clopen-transitive-full-cantor-groups-have-type-a-actions` (unrev.) | a finitely presented full group of Cantor homeomorphisms whose local maps join any two clopen sets. Stabilizers are `D × D`, so nothing else needs checking. `2V`, `nV` and `V_d(H)` have this shape. |
| H4: affine actor `S ⋊ W` acting on `S` | `orbit-finite-affine-actions-are-type-a` (ESTABLISHED); universal version `decidable-groups-embed-in-orbit-finite-affine-actors` (OPEN) | f.p. `S ⋊ W` with `W` f.g. (then f.p.) and finitely many `W`-orbits on `S`, and `GL_n(Q) <= S ⋊ W`. Note that `Aff(Q^n) = Q^n ⋊ GL_n(Q)` already has 2 `W`-orbits on `S = Q^n`. It fails only because `W = GL_n(Q)` is not f.g. and `Γ` is not f.p. Screens: `S` has finitely many element orders, and `W` must be f.p. |

**Also available:**
- `fp-simple-highly-transitive-groups-satisfy-pbh` (BFFHZ Thm C, import): a f.p. simple highly
  transitive host is equivalent to a type (A) host.
- `centerless-fp-finitely-many-conjugacy-classes-gives-pbh`: a f.p. centreless group with
  finitely many conjugacy classes gives type (A) through the conjugation action.
  Candidate shape: a f.p. group containing `GL_n(Q)` with finitely many conjugacy classes.
- `abstract-btb-pairs-fp-and-relatively-simple` (FFWZ import) and M5.

**Landed by the gq swarm after the first version of this map** (7ee358237):
- `gl-n-q-in-permutational-boone-higman-class` (OPEN): `GL_n(Q) ∈ B_A`. This is the recommended
  target. Route `gl-n-q-bh-via-permutational-class` gives the root from it.
- `permutational-host-forms-agree-for-countable-inputs` (ESTABLISHED, unrev.): the host forms
  agree for arbitrary, non-f.g. inputs, which removes the "stated for f.g. `H`" caveat in H1.
- `gl-n-q-targets-are-cofinal-in-n` (ESTABLISHED, unrev.): `GL_n(Q) <= SL_(n+1)(Q)`,
  `PGL_(n+1)(Q)`, `GL_(n^2)(Q)`. Any hereditary property for all large `n` gives it for all
  `n`, so lanes may work with `SL_N(Q)` or `PGL_N(Q)` for large `N`.

## 3. Cantor-homeomorphism hosts

### 3.1 Brin–Thompson groups `nV` (ALIVE for n = 2; for n >= 3 hinges on one open question)

`nV` is finitely presented and simple (Brin; survey §4.4), and it has shape H3. On main:

**What `2V` is known to contain:**
- `(Q,+) <= 2V <= nV`: `rationals-embed-in-brin-thompson-group-2v` (Kojima–Sheng
  arXiv:2603.18410 Thm 1.2, unrefereed; own explicit odometer proof, unrev.). The mechanism is a
  mixed-radix odometer in coordinate 2, whose overflow applies an infinite-order `g ∈ V` in
  coordinate 1; `g × id` then has roots of every order. This is the template for divisibility
  on main.
- every RAAG: `every-raag-embeds-in-brin-thompson-group-2v` (Salo import);
- `GL_2(Z) <= V <= 2V`;
- caution: `brin-thompson-2v-embeds-in-no-zipper-group` is OPEN (demoted at landing, no referee
  votes). Do not rely on its undistortion clause until it passes review.
- distortion elements: `brin-thompson-mv-contains-a-distortion-element` (Callard–Salo import).
  So the undistortion argument that keeps `H_3(Z)` out of `V` fails in `2V`.

**What is open:**
- `every-gl-n-z-embeds-in-2v` vs `some-gl-n-z-does-not-embed-in-2v`;
- the Haagerup pair `brin-thompson-groups-nv-are-a-t-menable` /
  `brin-thompson-2v-is-not-a-t-menable` (Zaremsky Problem 2.7). If `nV` is Haagerup, no infinite
  Kazhdan group embeds, so `SL_3(Z) ⊄ nV` and the whole family is dead for `n >= 3`.

**Constraint M2:** point germ groups are abelian of rank `<= n`.

**Verdict:**
- `n = 2`: ALIVE. Nothing in the graph blocks `GL_2(Q) <= 2V` or `<= mV`.
- `n >= 3`: ALIVE **only if** `SL_3(Z) <= mV` for some `m`. That is the pivot question for
  lanes gq-bt-kojima and gq-nv-obstruct.

First stepping stones in this family:
- `Aff(Q) = Q ⋊ Q^x`: the odometer copy of `Q` plus a dilation normalizing it;
- `U_3(Q)`, which needs central divisibility plus a commutator structure.

### 3.2 Finite germ extensions of V and shells (ALIVE as a framework, hard)

- `shell-cantor-embeddings-are-finite-germ-extensions`: **every countable group** `P` embeds
  faithfully in a finite germ extension `E_nu = <V, hat(P)>` of `V`, including `P = GL_n(Q)`.
  But `E_nu` is f.g. only if `P` is. So for G, feed a f.g. overgroup of `GL_n(Q)` (for
  example the 2-generator HNN/Clapham overgroup, survey Prop. 3.3).
- Finite presentation is the entire difficulty:
  - `decidable-inputs-have-fp-shell-envelopes` and `decidable-inputs-have-fp-shell-stabilizers`
    are OPEN;
  - the necessary condition M4: the near group `R_nu` must be f.p.;
  - route `boone-higman-via-shell-germ-stabilizers` uses Belk–Hyde–Matucci arXiv:2407.03149
    Thm 2.1 (finite presentation of finite germ extensions from finite presentation of the
    stabilizers `S(M,M')`, `|M'| <= 2`).
- `orbit-preserving-germ-corollary-extensions-of-v-are-rational` (ESTABLISHED): a f.g. finite
  germ extension satisfying the BHM germ hypotheses and orbit preservation (T) consists of
  **rational** homeomorphisms, with word problem in time `2^O(n)`. A germ-extension host of
  that kind for `GL_n(Q)` would therefore put `GL_n(Q)` in the rational group `R`. Spark: does
  `(Q,+)` embed in `R`? If not, every such host needs non-orbit-preserving transports, as `VA`
  presumably has.
- Verdict: ALIVE. The natural place for divisibility is the **germ group at a singular
  point**. `VA` does exactly this for `Q` (gap G1: import it), but `VA` itself is excluded for
  `GL_n(Q)` by root O4 (no distortion). A germ-extension host must combine a VA-type divisible
  germ with a source of exponential distortion, which the `2V` slope cocycle has. Lanes: gq-germ-design,
  gq-q-in-germs, gq-germ-necessary, gq-va-*.

### 3.3 Rational similarity groups, RN groups, Scott groups

- **RN groups `V_d(H)`** (`rover-nekrashevych-finite-presentation-criteria`: Scott FP1,
  Nekrashevych FP2, simple commutator subgroup). The coefficient group `H` must be
  self-similar, hence residually finite, hence Q-free by O1. So `H` never contains `GL_n(Q)`.
  **KILLED as a way to put `GL_n(Q)` in the coefficient group.**
  - Not yet excluded: `GL_n(Q) <= V_d(H)` through the non-RF envelope itself. `V <= V_d(H)`
    and `Q ⊄ V`, so divisibility would have to come from mixing `H`-germs with `V`, as in `2V`.
  - `nV_d(H)` has a simple alternating core
    (`brin-thompson-nekrashevych-groups-have-simple-alternating-core`).
- **Scott's `Sc(n) ⊇ GL_n(Z)`, Zaremsky's self-similar affine groups over `Z[1/m]`**
  (`principal-ideal-affine-groups-are-self-similar`,
  `polynomial-parameter-affine-groups-are-self-similar`):
  - KILLED as containers (O1);
  - CONTEXT for the chain `GL_n(Z[1/m!])`. Each link embeds in some f.p. simple group, but in
    a different one for each `m`, with no compatibility on main.
  - `affine-self-similar-coordinate-rings-are-one-dimensional` limits the coordinate rings
    further.
- **Contracting RSGs** (BBMZ arXiv:2309.06224; `hyperbolic-groups-embed-in-contracting-rsgs`;
  full contracting RSGs embed in f.p. simple twisted Brin–Thompson groups, survey Thm 4.18):
  - ALIVE, with a constraint. At a rational point `ω` of a finite-nucleus RSG the germ group
    is virtually infinite cyclic (`rsg-proper-power-germ-torsion-via-cyclic-germ-groups`,
    BBMZ `prop:CyclicStabilizers`, import). A divisible group has no nontrivial image in a
    virtually cyclic group.
  - Consequence (gq-map, one line, unrev.): **every element of a divisible subgroup that fixes
    a rational point is the identity near that point.** `Q <= GL_n(Q)` must act with no
    rational fixed points outside the interiors of its fixed sets.
  - Related open claim: `finite-nucleus-rsg-proper-power-conjugates-are-equicontinuous`.
- **Odometer RN/RSG hosts for shells** (`fixed-base-shells-embed-in-contracting-rsg`,
  `fixed-base-shell-inputs-embed-in-odometer-rn-groups`): CONTEXT for shell lanes whose near
  charts are odometer-affine.

### 3.4 Piecewise projective / line and circle hosts (untested on main)

- M3 kills compact-**interval** hosts for the simple envelope. It leaves intermediate groups
  alone, and it says nothing about the circle.
- **Hyde–Lodha `Q_n`** (`hyde-lodha-fp-simple-groups-contain-thompson-f`, arXiv:2302.04805):
  f.p. simple groups of type `F_∞` containing `F`. They are candidate hosts; whether they
  contain `PSL_2(Z)`, `Q` or `Aff(Q)` is not on main.
- `fp-simple-amenable-via-hyde-lodha-group` is dead, and is irrelevant here.
- No node on main covers Thompson's `T` as piecewise `PSL_2(Z)`, `T̄`, Monod's `H(A)`,
  Lodha–Moore, or PIP groups (gap G2). Family C is **unmapped territory**.

## 4. Rings, Leavitt algebras, Steinberg groups

### 4.1 The binary Leavitt unit group `U = L_(F_2)(1,2)^x` (ALIVE as a candidate host)

**What is on main about `U`:**
- it is finitely presented: `leavitt-unit-group-finitely-presented` (Khanh arXiv:2609.08428v1
  Thm 6.1, import);
- it is simple: `binary-leavitt-unit-group-is-simple`, via `U = GL_3(L) = EL_3(L)`;
- it is in `B_A`: `binary-leavitt-unit-group-satisfies-pbh`;
- it contains every finite group: `leavitt-unit-group-contains-every-finite-group`;
- it contains `GL_n(A)` for every unital subalgebra `A <= L`:
  `leavitt-subalgebra-linear-groups-satisfy-boone-higman`.

**Contribution.** `U` is a single finitely presented simple group. Whether it contains
`(Q,+)`, `Aff(Q)` or `GL_2(Q)` is **not on main**. The subalgebra route cannot give that,
because `A` has characteristic 2. An embedding would have to be abstract, not a ring map.

**Spark S1.** For `L(1,2)`, `M_k(L) ≅ L` unitally for every `k >= 1`. So `U` holds unital
copies of `GL_k(L)` for all `k`, and the digit codes `c_{r,i}` of the `2V` odometer proof have
Leavitt analogues. Transporting that proof would give `(Q,+) <= U`.

### 4.2 Char-2 central simple Leavitt tensor hosts (REDUCES G to one algebra problem)

Route `boone-higman-via-central-simple-leavitt-tensor-host`. Put `R = B ⊗ L_(F_2)(1,2)`.

**Inputs on main:**
- `leavitt-tensor-hosts-acyclic-steinberg-and-fp`: if `K_1(R) = K_2(R) = 0` and `B` is f.p.,
  then `R^x` is f.p. (conditional on Khanh's criteria);
- `central-simple-leavitt-tensor-unit-groups-are-simple`: `B` central simple ⇒ `E_n(R)` simple
  for `n >= 3`, and `R^x` simple if `K_1 = K_2 = 0`.

The only open premise is `decidable-group-algebras-have-fp-central-simple-hosts` (OPEN, stated
for f.g. `G`). Nothing in the chain `G <= F_2[G]^x <= B^x <= R^x` uses finite generation of
`G`.

**REDUCTION R-alg (gq-map, unrev.).** G follows if `F_2[GL_n(Q)]` embeds unitally in a
finitely presented central simple `F_2`-algebra `B` with `K_1(B⊗L) = K_2(B⊗L) = 0`. By
Ara–Cortiñas it is enough that `B` be regular supercoherent. This is a countable instance of
the algebra form of Boone–Higman.

**Supporting nodes:**
- `belyaev-associative-higman-theorem`: an r.e.-presented algebra embeds in a f.p. algebra;
  this covers `F_2[GL_n(Q)]`;
- `decidable-clapham-via-effective-belyaev` and `fp-simple-algebras-have-solvable-word-problem`;
- `algebra-boone-higman-conjecture` (OPEN).

The simplicity and `K`-theory of the envelope are the whole gap. Sibling route:
`boone-higman-via-units-of-cantor-crossed-leavitt-tensors`, with
`decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units` (OPEN).

### 4.3 Characteristic-0 rings (ALIVE only for noncommutative Q-containing rings)

**Kill results.**
- **Kills commutative f.g. rings (M6).** The Q-containing ring must be noncommutative, or not f.g.
- **Kills bounded-divisibility rings (M1).** Every coefficient ring must have unbounded
  divisibility, which is consistent with containing `Q`.
- **Kills a Weyl-algebra route in characteristic 0.** `weyl-algebra-blocks-a-universal-leavitt-host`:
  `A_1(K)` does not embed in `L_K(1,2)` for char `K = 0`.
- **Kills `EL_4` simplicity in characteristic `!= 2` (M8).**

**Positive tools.**
- `ample-steinberg-el-simple-mod-centre-without-hausdorff` (ESTABLISHED, un-verify PASS): for any
  field `k`, `Q` included, and a simple Steinberg algebra `A = A_k(G)`, `EL_n(A)/Z` is simple
  for `n >= 3`. Over `k = Q`, `A` contains `Q`, so `EL_n(A) ⊇ SL_n(Q)`. **But** `A` is then not
  f.g. as a ring. Finite presentation of `EL_n(A)/Z` is the gap, and it is probably false in
  that form.
- `elementary-groups-over-polynomial-s-integers-are-fp` (reviewed): `E_n(Z[1/m][t])` is f.p.;
- `affine-extension-of-fp-elementary-group-is-fp` (reviewed): for commutative f.g. rings only.
  Both are KILLED for `Q` by M6. They are the template for "St_n + K_2 control ⇒ f.p." and are
  CONTEXT for a noncommutative ring `R ⊇ Q`.
- `agp-purely-infinite-simple-k1-is-unit-abelianization`: `K_1(R) = U(R)^ab` for purely
  infinite simple `R` (Ara–Goodearl–Pardo, import).

**REDUCTION R-ring (gq-map, unrev.).** G follows from a f.g. noncommutative ring
`R ⊇ Q` such that `EL_n(R)` or `R^x` (mod centre) is finitely presented and simple. Every
piece other than the ring itself exists on main for Steinberg/Leavitt-type rings.

## 5. Universal routes, countable-input facts, reformulations (CONTEXT)

Every universal route to `boone-higman-conjecture` or `permutational-boone-higman-conjecture`
also gives G, since `GL_n(Q)` lies in a 2-generator group with solvable word problem
(survey Prop. 3.3). They are as hard as Boone–Higman. The useful question is which one has a
premise that is **easier for this input**.

**Routes whose premise has a GL_n(Q)-shaped special case:**
- `pbh-via-orbit-finite-affine-actors` (H4). `Aff(Q^n)` is already orbit-finite; only finite
  generation and presentation are missing.
- `pbh-via-fp-finitary-overgroups` (H1).
- `boone-higman-via-central-simple-leavitt-tensor-host` (R-alg).
- `boone-higman-via-v-times-aperiodic-sft-full-groups`: a f.p. group with a minimal free SFT,
  then the alternating full group of `V × SFT`.
- `boone-higman-via-fp-shell-envelopes` / `boone-higman-via-shell-germ-stabilizers` /
  `boone-higman-via-perfect-shell-envelopes` / `boone-higman-via-enlarged-shell-stabilizers` (§3.2).

**Dead universal routes, recorded as such, not to retry:**
- `boone-higman-via-universal-fp-self-similar-host` (O1 in disguise);
- `boone-higman-via-rover-nekrashevych-hosts`;
- `boone-higman-via-hypothesis-free-shift-compiler`;
- `boone-higman-via-universal-leavitt-host`;
- `boone-higman-via-finitely-presented-simple-ring-quotient` (INVALIDATED);
- `boone-higman-via-complexity-graded-universal-inputs`.

**Countable-input facts** (non-f.p. hosts, CONTEXT):
- `countable-group-embeds-in-two-generator-simple-group` (Schupp);
- `countable-group-embeds-in-fg-simple-kazhdan-group`;
- `every-countable-group-embeds-in-an-fp2-group` (Leary, import);
- `every-countable-group-lies-in-a-faithful-ha2-actor` (open);
- `every-countable-group-embeds-in-a-simple-fp2-group` (open, Zaremsky 1.25) versus
  `some-countable-group-embeds-in-no-simple-fp2-group`.

An **`FP_2` simple host for `GL_n(Q)`** is a weaker target than G. It follows from an
`[HA_2]` actor containing `GL_n(Q)` (Fournier-Facio–Wu–Zaremsky Cor. 4.14). It is a possible
first win for family B.

**Reformulations** (`boone-higman-iff-infinite-simple-inputs`, `local-boone-higman-iff-boone-higman`,
`boone-higman-iff-simple-kazhdan-decidable-inputs`, `boone-higman-iff-fp-just-infinite-hosts`,
`bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`) all concern the whole conjecture. Their use
here is only as calibration.

**Problem 2.7 (G').**
- `mikaelian-explicit-higman-embedding-citation` (Mikaelian arXiv:2507.04347v8, an explicit
  Higman algorithm) is on main;
- per RULES §8b, the same paper **announces** an explicit f.p. 2-generator overgroup of
  `GL(n,Q)`, with no construction and not natural;
- `omega-input-reduces-to-mikaelian-tower` and `mikaelian-rho-tau-shortcuts-fail` record known
  source slips.

A natural answer is still open.

**Swarm literature artifacts:**
- `research/artifacts/gq-gq-lit-arxiv-priority.md` (6505750b9): no priority threat for G; an
  announcement for 2.7;
- `research/artifacts/gq-gq-lit-hosts.md` (75e692ae0): verbatim hypotheses of the host theorems
  (germ extensions, type (A)). Read it before using BHM Thm 2.1 or Zaremsky Thm A.
- `research/artifacts/gq-gq-state-of-attack.md`: the running board summary.

## 6. Gaps: things the target needs that have no node on main

- **G1.** Belk–Hyde–Matucci: `Q <= T̄`, `T̄ <= A`, `VA` finitely presented (type `F_∞`) and
  simple, every countable abelian group `<= VA` (survey Thm 4.11; arXiv:2407.03149). Also the
  exclusion `SL_n(Z) ⊄ VA`, `n >= 3` (survey Rem. 4.12). Owner: gq-lit-hosts /
  gq-lit-q-embeddings. Import as citation nodes.
- **G2.** Piecewise-projective and line/circle hosts: `T` as piecewise `PSL_2(Z)` homeomorphisms
  of `RP^1`; Monod `H(A)`; Lodha–Moore; Thurston PIP. Owner: family C.
- **G3.** Higman's theorem that `SL_3(Z) ⊄ V` and that torsion-free nilpotent subgroups of `V`
  are free abelian (survey Thm 4.4) as a node. It is only paraphrased inside other nodes.
- **G4.** A node for "`GL_n(Q)` has no locally finite normal subgroup outside `{±I}`" and for
  O1 as its own claim. Those two are what H1 and every RF-based kill consume.
- **G5.** M6, the fact that a commutative f.g. ring cannot contain `Q`, as a node.
- **G6.** `nV` finitely presented and simple (Brin; Hennig–Matucci; Brin simplicity), if not
  already a node. Search `brin-thompson-nv-*` before adding.

## 7. Sparks (not pursued by gq-map)

- **S1** `(Q,+) <= L_(F_2)(1,2)^x` by transporting the `2V` odometer, using `M_k(L) ≅ L` (§4.1).
- **S2** `Aff(Q) <= 2V`: the odometer copy of `Q` together with an element acting as `q -> 2q`.
  Kojima–Sheng's continuum of copies sharing one `Z` may already give one normalizer.
- **S3** Decide `SL_3(Z) <= 2V`. It controls the whole `nV` family for `n >= 3` (§3.1).
- **S4** Orbit-finite affine actor (H4) for `GL_n(Q)`: a f.p. `S ⋊ W` with `W` f.g. and
  finitely many orbits, e.g. `S` a countable group of finitely many element orders containing
  `Q^n`, and `W ⊇ GL_n(Q)` acting through a f.g. overgroup.
- **S5** Is `(Q,+)` a subgroup of the rational group `R` (Grigorchuk–Nekrashevych–
  Sushchanskii)? The answer decides whether BHM-type orbit-preserving germ extensions can host
  `Q` (§3.2).
- **S6** In RSG hosts, divisible elements fixing a rational point are locally trivial there
  (§3.3). This is a necessary condition any RSG-based construction must meet first.
