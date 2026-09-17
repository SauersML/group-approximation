# The sofic-indicable invariant and simple groups in the permanence closure

Lane `sw-017` (transplanter, wave `flagship-2026-09-17`). Supports `permanence-closure-fg-simple-groups-are-sofic`,
its route `permanence-closure-fg-simple-groups-are-sofic-proof`, the refutation of
`permanence-closure-contains-fg-simple-nonsofic-group`, and `kun-thom-full-group-balls-do-not-embed-in-permanence-closure`.

## 0. Why this approach

The earlier lanes pushed a simple group `Q` through the permanence operations stage by stage. That induction breaks at
local embeddings (O3): a ball of `Q` embeds into some group of an earlier stage, but the ball is not a subgroup, and
simplicity is not a property of balls. So the old theorems needed a finite presentation
(`gottschalk-counterexamples-lie-outside-the-permanence-closure`) or left O3 out
(`fg-simple-subgroups-of-local-embedding-free-closure-are-sofic`).

The import is from model theory, the method of *locally indicable* groups. Replace "`Q` never enters" by a
**subgroup-local invariant that a finitely generated simple nonsofic group cannot have** and that survives every
operation, including ultraproducts. The invariant is:

> **(LSI)** every nontrivial finitely generated subgroup has a nontrivial sofic quotient.

This is the indicability pattern with `Z` replaced by the class of sofic groups. Local indicability survives
ultraproducts because only the generators have to be tracked. The same holds here, and that is the step that
survives O3.

## 1. Conventions

- A group is *sofic* when every finitely generated subgroup is sofic. The class of sofic groups is closed under
  subgroups and under local embeddings: if every finite subset of `H` embeds as a partial multiplication table into a
  sofic group, then `H` is sofic. (A sofic approximation of the target restricted to the image of a finite set is an
  approximation of that set. Elek--Szabo 2006; Ceccherini-Silberstein--Coornaert, *Cellular automata and groups*,
  Chapter 7.)
- *Local embedding.* `H` is locally embeddable into a class `C` when for every finite `F ⊆ H` there are `C_F in C` and
  an injective `phi_F : F -> C_F` with `phi_F(xy) = phi_F(x) phi_F(y)` whenever `x, y, xy in F`.
- `S*` is the closure of `gottschalk-counterexamples-lie-outside-the-permanence-closure`: the smallest class that
  contains every sofic group and is closed under O1–O7. The kernels used are:
  - (O4) finitary split extensions: the kernel `N` is residually finite, since detection (A1) sends each nontrivial
    element nontrivially to a residually finite quotient;
  - (O5) graph folds `f : W -> G`, injective on vertex groups: `ker f` is free (below);
  - (O6) graph wreath products with LEF lamps: the kernel is a graph product of LEF groups, which is sofic
    (Ciobanu--Holt--Rees, *Sofic groups: graph products and graphs of groups*, Pacific J. Math. 271, 2014);
  - (O7) split extensions with finitely generated residually finite kernel.

Let `LSI` be the class of all groups with property (LSI). The trivial group has it vacuously.

## 2. Closure lemmas

**Lemma 2.1 (sofic groups).** Every sofic group lies in `LSI`.

*Proof.* A nontrivial finitely generated subgroup of a sofic group is sofic and is a quotient of itself. QED

**Lemma 2.2 (subgroups and unions).** `LSI` is closed under subgroups. A group all of whose finitely generated
subgroups lie in `LSI` lies in `LSI`.

*Proof.* (LSI) only refers to finitely generated subgroups. QED

**Lemma 2.3 (extensions).** Let `1 -> N -> E -> B -> 1` be exact with `N, B in LSI`. Then `E in LSI`.

*Proof.* Let `Q <= E` be nontrivial and finitely generated, and `pi : E -> B` the quotient.
- If `Q <= N`, then `Q` is a nontrivial finitely generated subgroup of `N`, so it has a nontrivial sofic quotient.
- Otherwise `pi(Q)` is a nontrivial finitely generated subgroup of `B`, with a nontrivial sofic quotient
  `pi(Q) ->> S`. The composite `Q ->> pi(Q) ->> S` is a nontrivial sofic quotient of `Q`. QED

No splitting, no action and no finiteness condition on the extension is used.

**Lemma 2.4 (ultraproducts).** Let `(H_i)_(i in I)` be groups in `LSI` and `U` an ultrafilter on `I`. Then
`H = prod_i H_i / U` lies in `LSI`.

*Proof.* Let `Q = <x_1, ..., x_m> <= H` be nontrivial, and choose representatives `x_k = [(x_(k,i))_i]`.
1. *Coordinate subgroups.* Put `Q_i = <x_(1,i), ..., x_(m,i)> <= H_i`. Every word `w` in the `x_k` is represented by
   `(w(x_(1,i), ..., x_(m,i)))_i`, so `Q <= prod_i Q_i / U`.
2. *Nontrivial coordinates.* Some `x_k != 1`, so `Q_i != 1` for `U`-almost every `i`. For those `i`, (LSI) gives a
   surjection `psi_i : Q_i ->> S_i` onto a nontrivial sofic group. Put `psi_i` trivial on the other coordinates.
3. *The limit map.* `psi = prod_i psi_i / U : prod_i Q_i / U -> prod_i S_i / U` is a homomorphism.
4. *Nontrivial on `Q`.* For `U`-almost every `i`, `psi_i` is nontrivial on `Q_i`, so it is nontrivial on one of the
   generators `x_(k,i)`. The set of such `i` splits into `m` pieces according to the first such `k`. One piece lies in
   `U`, and for that `k` we get `psi(x_k) != 1`.
5. *The image is sofic.* Let `F` be a finite subset of `psi(Q)`, with representatives. The finitely many equalities and
   inequalities of the partial multiplication table of `F` hold in `S_i` for `U`-almost every `i`. So `F` embeds as a
   partial table into a sofic group, `psi(Q)` is locally embeddable into sofic groups, and `psi(Q)` is sofic by
   Section 1.

So `psi|_Q` is a nontrivial sofic quotient of `Q`. QED

**Lemma 2.5 (local embeddings).** If `H` is locally embeddable into `LSI`, then `H in LSI`.

*Proof.* Let `J` be the set of finite subsets of `H`, and `U` an ultrafilter on `J` containing every cone
`{F' : F' ⊇ F}`. The cones have the finite intersection property, so `U` exists. Define `Phi(h) = [(phi_F(h))_F]`,
using any value where `h` is not in `F`.
- *Homomorphism.* For `x, y in H`, the cone of `{x, y, xy}` lies in `U`, and on it `phi_F(xy) = phi_F(x) phi_F(y)`.
- *Injective.* For `h != 1`, on the cone of `{1, h}` we have `phi_F(1) = phi_F(1)^2 = 1` and `phi_F(h) != phi_F(1)`.

So `H` embeds into `prod_F C_F / U`, which lies in `LSI` by Lemma 2.4, and `H in LSI` by Lemma 2.2. QED

**Lemma 2.6 (fold kernels).** Let `W` be the fundamental group of a graph of groups and `f : W -> G` a homomorphism
injective on every vertex group. Then `ker f` is free, and `W` is an extension of a free group by `f(W) <= G`.

*Proof.* `ker f` meets every conjugate of a vertex group trivially, since `f` is injective on it. So `ker f` acts on the
Bass--Serre tree with trivial vertex stabilizers. It acts without inversions, because `W` does, so it acts freely and
is free (Serre, *Trees*, I.3.3). QED

## 3. The theorem

**Theorem 3.1.** `S* ⊆ LSI`.

*Proof.* `LSI` contains every sofic group (Lemma 2.1). It is enough to show that it is closed under O1–O7.
- **O1, O2.** Lemma 2.2.
- **O3.** Lemma 2.5.
- **O4.** `N semidirect G` with `N` residually finite, hence sofic, and `G in LSI`. Lemma 2.3.
- **O5.** By Lemma 2.6, `W` is an extension of a free group, which is sofic, by `f(W)`. `f(W)` is a subgroup of a group
  in `LSI`. Lemmas 2.2 and 2.3.
- **O6.** The kernel is a graph product of LEF groups, which is sofic by Ciobanu--Holt--Rees. Lemma 2.3.
- **O7.** The kernel is residually finite. Lemma 2.3.

`S*` is the smallest class with these closure properties, so `S* ⊆ LSI`. QED

**Corollary 3.2.** Every finitely generated simple group in `S*` is sofic. So is every finitely generated simple
subgroup of a group in `S*`.

*Proof.* A nontrivial finitely generated simple `Q` in `LSI` has a nontrivial sofic quotient. The kernel is a proper
normal subgroup, hence trivial, so `Q` is sofic. `S*` is closed under subgroups. QED

**Corollary 3.3 (the negative answer).** No infinite finitely generated simple nonsofic group lies in `S*`. This
refutes `permanence-closure-contains-fg-simple-nonsofic-group`.

**Corollary 3.4 (evasion, general form).** Suppose a group `H` contains a nontrivial finitely generated subgroup with
no nontrivial sofic quotient. Then `H` is not in `S*`.

This contains both earlier evasion theorems:
- `gottschalk-counterexamples-lie-outside-the-permanence-closure`, with the finite presentation removed;
- `fg-simple-subgroups-of-local-embedding-free-closure-are-sofic`, with O3 restored.

It also covers nonsimple subgroups, for instance finitely generated nonsofic groups whose nontrivial quotients are all
nonsofic.

**Corollary 3.5 (the alternating full group candidate).** Suppose the alternating full group `A(Y)` of
`kun-thom-product-action-alternating-full-group-is-nonsofic` is finitely generated and simple, as recorded in the open
`kun-thom-product-action-alternating-full-group-is-fg-simple`. Then `A(Y)` is not locally embeddable into `S*`, so
`kun-thom-full-group-balls-embed-in-permanence-closure` is false.

*Proof.* `A(Y)` is nonsofic. If it were locally embeddable into `S*`, it would lie in `S*` by O3 and would be sofic by
Corollary 3.2. QED

## 4. What the obstruction kills, and exactly where

**Killed: every permanence theorem of extension or limit type.** Let `S+` be any enlargement of `S*` by further
operations, each of one of these shapes:
- an extension whose kernel lies in `LSI` (in particular any sofic, residually finite, LEF, amenable or free kernel),
  over a base in the class;
- subgroups, directed unions, local embeddings, marked limits or ultraproducts.

Then `S+ ⊆ LSI`, by the same lemmas, and `S+` still contains no finitely generated simple nonsofic group.

By `gottschalk-reduces-to-fg-simple-kazhdan-groups`, Gottschalk's conjecture is equivalent to surjunctivity of the
finitely generated simple Kazhdan groups. So **no permanence closure of this kind decides a single nonsofic case of
the conjecture in the class to which it reduces.** Among finitely generated simple groups, it reaches exactly the
sofic ones, which Gromov--Weiss already covers.

The step where every such method dies is Corollary 3.2: the simple group has no proper quotient in which to put the
sofic part.

**What escapes the invariant.** A future positive method on a simple nonsofic host must use an operation whose output
fails (LSI) even though its inputs satisfy it. The candidates are:
1. *Graphs of groups without a faithful fold.* General amalgams `A *_C B` and HNN extensions do not preserve (LSI) in
   any known way. Burger--Mozes lattices are finitely generated simple amalgams of free groups, so an amalgam
   permanence theorem is the natural place where simple groups can appear. The graph records such amalgams as not
   covered (`finitary-split-extension-surjunctivity-permanence`, scope paragraph).
2. *Non-extension constructions*: topological full groups, commutator subgroups of full groups, Leavitt-type unit
   groups. A surjunctivity permanence theorem stated directly for full groups of actions of surjunctive groups would
   escape. The alternating full group of Section 3.5 is simple, so no extension-type theorem reaches it.
3. *Direct methods* on the host: measure preservation, Rokhlin entropy lower bounds, or direct finiteness of the
   automaton monoid.

## 5. Calibration

- *Sofic simple groups.* Finite simple groups and LEF simple groups, such as the alternating full groups of minimal
  subshifts, lie in `S*` and are sofic. The theorem does not exclude them.
- *The known witnesses.* The Kun--Thom wreath `W = N semidirect G` lies in `S*` and in `LSI`. Every finitely generated
  subgroup `Q` of `W` either lies in `N`, which is residually finite, or maps nontrivially to the residually finite
  group `G`. `W` is nonsofic but not simple, and the invariant permits it.
- *A group outside `LSI`.* The binary Leavitt unit group is finitely generated, simple and nonsofic, so it is not in
  `LSI`. This agrees with `fixed-host-outside-sofic-permanence-closure`.
- *The invariant does not claim nonsurjunctivity.* (LSI) says nothing about surjunctivity outside `S*`. The theorem is
  about the reach of the landed methods, not about the groups.

## 6. Verification status

Proposed-established. The lemmas are elementary; each step is written out above. The external inputs are:
- local closure of soficity;
- Serre's theorem that groups acting freely on trees are free;
- Ciobanu--Holt--Rees for O6. A version of O6 whose kernel is only assumed to lie in `LSI` needs no import.
