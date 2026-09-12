# Direct completeness derivation for the rank-five family

Date: 2026-08-15 (late).  Working notes, not canonical.  Companion to
`ATLAS_RANK5_DICTIONARY_2026-08-15.md`.

> ## SUPERSEDED IN PART — read this first
>
> **Lemma X (§5) is PROVED**, in `notes/STEINBERG_SPARE_INDEX_2026-08-15.md`
> §6, as two instances of that note's `(Q′_t)`.  The stall recorded below was
> only apparent, and the fault is in **my Lemma 3.1: its hypotheses are too
> strong.**
>
> Lemma 3.1 assumes `T = [X,V]` commutes with `X`, `Y`, `V`, and its
> four-conjugation proof consumes `[T,X]` and `[T,Y]` at steps 2-4.  Those are
> same-length statements about the object being constructed, and that — not
> anything structural — is the whole source of the circularity diagnosed in
> §5.  The correct route uses the identity
>
> ```
> T = [X,V] = U V U^{-1} · [U,Z] · V^{-1}        (needs only [X,Z] = 1)
> ```
>
> then `[U,V] = 1` collapses `U V U^{-1}` to `V`, and `V` commuting with `U`
> and with `Z` makes it commute with `[U,Z]`, giving `T = [U,Z]`.  The
> hypothesis set is then `[X,Z] = [U,V] = [Z,V] = 1` — **all (St2) instances
> between strictly shorter objects at roots other than `(i,j)`**, exactly what
> my own Lemma 5.1 supplies with no spare-index clash.  `[Y,V] = 1` is not
> needed either.
>
> So the derived object's commutation is a *consequence*, not a hypothesis.
> The five routes I rejected in §5 were all attempts to supply a hypothesis
> that does not need supplying — a good illustration of how an over-strong
> lemma statement can manufacture an obstruction that is not there.
>
> What survives unchanged: §2 (bilinearity and context absorption), §4
> (split independence reduces to spare independence), the machine check of
> the transfer identity, and the length-two argument.  The one-sentence
> obstruction in §5 is a correct description of *my* Lemma 3.1's difficulty
> and an incorrect description of the problem.
>
> A separate, genuine gap was found in its place: the emitted family does not
> imply `x_ij(a)² = 1`, which additivity over `F₂` requires.  See §7 below.

**Target.**  Let `A = {1, e, f, e^*, f^*}` and

```
L = F2<e,f,e^*,f^*> / (e^*e = 1, f^*f = 1, e^*f = 0, f^*e = 0, ee^* + ff^* = 1).
```

Let `G_0` be the group presented by generators `X_ij(a)`, `1 <= i != j <= 5`,
`a in A`, subject to the emitted family: the full (St2) and (St3)
instantiation on `A`, together with the five lifted CK relations.  We want
`G_0 = St_5(L)`.

Throughout `[x,y] = x y x^{-1} y^{-1}`, and *root* `(i,j)` means the pair of
indices carried by a symbol.  `W` denotes the free monoid on `{e,f,e^*,f^*}`;
`L` is spanned over `F2` by the images of `W`.

---

## 1. What has to be produced

For each root `(i,j)` and each `c in L` we must define `Ehat_ij(c) in G_0` such
that (St1)-(St3) hold for **all** ring elements.  That gives a homomorphism
`St_5(L) -> G_0` inverse to the evident `G_0 -> St_5(L)`, hence the
isomorphism.

Definition proceeds in two stages: first on words `w in W`, by nesting (St3)
through spare indices, then on sums.  Write, for a spare index
`sigma notin {i,j}` and `w = a_1 w'` with `|w| >= 2`,

```
D^sigma_ij(w) := [ Ehat_i,sigma(a_1),  Ehat_sigma,j(w') ] .            (D)
```

Three things must be shown.

* **(I) Spare independence.**  `D^sigma_ij(w)` does not depend on `sigma`.
* **(II) Split independence.**  `[Ehat_ik(u), Ehat_kj(v)] = Ehat_ij(uv)` for
  every splitting, not only the leftmost letter.
* **(III) Ring consistency.**  The extension to sums is well defined, i.e.
  `Ehat_ij(u rho v) = 1` for each defining ring relation `rho` and all
  contexts `u, v`.

(III) is **closed** (§2).  (II) reduces to (I) (§4).  (I) is reduced to a
single commutator computation, which is carried out and verified (§3), but
its hypotheses cannot be supplied by the induction as organised here; that is
the stall, stated exactly in §5.

---

## 2. (III) Ring consistency: CLOSED

**Lemma 2.1 (commutator is bilinear on root subgroups).**  Let `P, Q` lie in
the root subgroup `U_kj` and `X in U_ik`, with `i, k, j` distinct.  Then
`[X, PQ] = [X,P][X,Q]`.  Symmetrically `[PQ, Z] = [P,Z][Q,Z]` for
`P,Q in U_kl`, `Z in U_lj`.

*Proof.*  `[X,PQ] = [X,P] · P[X,Q]P^{-1}`.  Now `[X,Q] in U_ij` and `P in U_kj`,
and the roots `(k,j)`, `(i,j)` satisfy the (St2) condition (`k != j` and
`i != j`), so `P` centralises `[X,Q]`.  The second statement is the same
computation with the roots `(k,l)`, `(k,j)`, whose (St2) condition is
`k != j` and `k != l`.  QED

**Lemma 2.2 (context absorption).**  Let `rho` be an `F2`-sum of words, and
suppose `Ehat_kl(rho) = 1` for every root `(k,l)`.  Then
`Ehat_ij(u rho v) = 1` for all words `u, v`.

*Proof.*  Choose `k, l` making `i, k, l, j` legal for the two nestings (four
indices suffice; `n = 5` has them).  By Lemma 2.1 the maps
`Ehat_kl(-) |-> [Ehat_kl(-), Ehat_lj(v)]` and
`Ehat_kj(-) |-> [Ehat_ik(u), Ehat_kj(-)]` are homomorphisms on the relevant
root subgroups, so

```
Ehat_kj(rho v) = [ Ehat_kl(rho), Ehat_lj(v) ] = [1, ...] = 1,
Ehat_ij(u rho v) = [ Ehat_ik(u), Ehat_kj(rho v) ] = [..., 1] = 1.
```
QED

The five hypotheses `Ehat_kl(rho) = 1` are exactly the lifted CK relations,
**all five of which the emitted family already contains** (`cuntz` for
`e^*e = f^*f = 1`, `zero` for `e^*f = f^*e = 0`, `partition` for
`ee^* + ff^* = 1`).  So (III) holds as soon as (I) and (II) do.

This also **explains the `n >= 4` threshold** of [KrM, Theorem 3]: the two
nestings in Lemma 2.2 need four distinct indices, and at `n = 3` they are
unavailable — matching the sharp `n = 3` failure of their Corollary 2.

---

## 3. The commutator transfer computation

This is the heart of (I).  It is stated as an implication because its
hypotheses are what §5 cannot supply.

**Lemma 3.1 (transfer).**  Let `i, j, k, l` be four distinct indices and let

```
X (root (i,l)),   Y (root (l,k)),   Z (root (k,j))
U := [X,Y]  (root (i,k)),   V := [Y,Z]  (root (l,j)),   T := [X,V].
```

Assume the (St2) instances `[X,Z] = 1` and `[Y,V] = 1`, and assume `T`
commutes with `X`, `Y` and `V`.  Then

```
[U, Z] = T ,     i.e.    [[X,Y],Z] = [X,[Y,Z]] .
```

*Proof.*  Four conjugations, innermost first.

1. `[Y,Z] = V` gives `Y Z Y^{-1} = V Z`.  Conjugating by `Y^{-1}` and using
   `[Y,V] = 1`: `Z = (Y^{-1}VY)(Y^{-1}ZY) = V (Y^{-1}ZY)`, so
   `Y^{-1} Z Y = V^{-1} Z`.
2. `T = [X,V]` gives `X V X^{-1} = T V`.  Conjugating by `X^{-1}` and using
   `[T,X] = 1`: `V = (X^{-1}TX)(X^{-1}VX) = T(X^{-1}VX)`, so
   `X^{-1} V X = T^{-1} V` and `X^{-1} V^{-1} X = V^{-1} T`.
   With `[X,Z] = 1`, `X^{-1}(V^{-1}Z)X = V^{-1} T Z = T V^{-1} Z`.
3. `Y (T V^{-1} Z) Y^{-1} = T · (Y V^{-1} Y^{-1}) · (Y Z Y^{-1})
   = T · V^{-1} · V Z = T Z`, using `[T,Y] = 1` and `[Y,V] = 1`.
4. `X (T Z) X^{-1} = T · X Z X^{-1} = T Z`, using `[T,X] = 1` and `[X,Z] = 1`.

Composing, `U Z U^{-1} = X Y X^{-1} Y^{-1} Z Y X Y^{-1} X^{-1} = T Z`, hence
`[U,Z] = U Z U^{-1} Z^{-1} = T`.  QED

**Machine check of the identity (MSI job 15862151, 43 s).**  Lemma 3.1 is a
statement about `G_0`, so evaluating in `Q` cannot prove it — but a slip in the
four-conjugation computation (wrong commutator convention, an inverted
conjugation, a mis-ordered product) would already show up in `Q`, where all the
hypotheses hold.  `experiments/atlas_relator_transfer_check.py` evaluates both
sides exactly, over every ordered quadruple of distinct indices and every
coefficient pair:

```
index quadruples x coefficient pairs checked:            3000
  [[X,Y],Z] = [X,[Y,Z]] in Q:                            3000
  both sides equal x_ij(ab) in Q:                        3000
roots x pairs with all three spare chains agreeing in Q:  500
roots x pairs where the canonical word matches every chain: 500
```

So the identity as written is right, and the three spare chains do agree in
`Q` — which is what makes them candidates to be equal in `G_0`.  Necessary
condition only, and labelled as such in the script.

`[U,Z]` is the spare-`k` definition of `Ehat_ij` and `T = [X,V]` is the
spare-`l` definition, so Lemma 3.1 *is* spare independence — modulo its
hypotheses.  Note it consumes exactly four distinct indices, again the
`n >= 4` threshold.

The three (St2) instances assumed for `T` are all legitimate:
`[T,X]` has roots `(i,j),(i,l)` (needs `i != l`, `i != j`);
`[T,Y]` has roots `(i,j),(l,k)` (needs `i != k`, `l != j`);
`[T,V]` has roots `(i,j),(l,j)` (needs `i != j`, `l != j`).

---

## 4. (II) reduces to (I)

**Lemma 4.1.**  Given (I) at all lengths `< t`, and Lemma 3.1, the identity
`[Ehat_ik(u), Ehat_kj(v)] = Ehat_ij(uv)` holds for every splitting with
`|uv| = t`.

*Proof.*  Induct on `|u|`.  `|u| = 1` is the definition (D).  For `|u| >= 2`
write `u = a_1 u'` and pick `l notin {i,j,k}`.  Then
`Ehat_ik(u) = [Ehat_il(a_1), Ehat_lk(u')]` by (I) at lower length, and with
`X = Ehat_il(a_1)`, `Y = Ehat_lk(u')`, `Z = Ehat_kj(v)` Lemma 3.1 gives

```
[Ehat_ik(u), Ehat_kj(v)] = [[X,Y],Z] = [X,[Y,Z]]
                         = [Ehat_il(a_1), Ehat_lj(u'v)] = Ehat_ij(a_1 u' v)
```

using the inductive hypothesis at total length `< t` for `[Y,Z]`.  QED

---

## 5. THE STALL, stated exactly

The induction that would prove (I) is:

> `H(t)`: for all `|w| <= t`, (a) `D^sigma_ij(w)` is `sigma`-independent;
> (b) `[Ehat_ij(w), Ehat_kl(v)] = 1` for every (St2) pair; (c) (St3) holds
> for total length `<= t`.

The (St2) half at length `t` is available **without circularity**:

**Lemma 5.1.**  For any spare `sigma` and any (St2) pair `(i,j), (k,l)` with
`sigma notin {k,l}`, `[D^sigma_ij(w), Ehat_kl(v)] = 1`, given `H(t-1)`.

*Proof.*  `D^sigma_ij(w) = [Ehat_i,sigma(a_1), Ehat_sigma,j(w')]` with both
factors of length `< t`.  Roots `(i,sigma), (k,l)` satisfy the (St2)
condition because `i != l` (given) and `k != sigma` (given).  Roots
`(sigma,j), (k,l)` satisfy it because `sigma != l` (given) and `k != j`
(given).  So both factors centralise `Ehat_kl(v)`.  QED

**The obstruction.**  Lemma 3.1 needs `[T,X] = 1` for `T` the spare-`l`
definition and `X` of root `(i,l)`.  Lemma 5.1 supplies exactly the instances
with `sigma notin {k,l}`; here `sigma = l` and the root pair is
`(i,j),(i,l)`, so the requirement is `sigma notin {i,l}`, which `sigma = l`
violates.  The same clash occurs for `[T,V]` (root pair `(i,j),(l,j)`).

This is not a shortage of indices — at `n = 5` a third spare `rho` is
available and Lemma 5.1 does supply all three commutations for `D^rho`.  It
is that Lemma 3.1's `T` is *by construction* the spare-`l` object, and its
own spare is the one the commutation instance forbids.  Comparing `D^k` and
`D^l` through the doubly-spare `D^rho` does not escape: each application of
Lemma 3.1 reintroduces the same clash one index over.

**Lemma X holds at length two.**  This is worth isolating, because it shows
the obstruction is genuinely inductive rather than a defect of the scheme.
For `|w| = 2`, `sigma`-independence is an EMITTED relation (the (St3) block
equates all three spare chains to one canonical right-hand side).  So `T` may
be represented by `D^sigma` for *whichever* spare is convenient.  Given
`X = X_il(a)` of root `(i,l)`, choose the representative with `sigma != l`
(three spares are available for `(i,j)` and only `l` is excluded).  Then

* `[X, X_i,sigma(a_1)] = 1` — roots `(i,sigma), (i,l)`, needing `i != l` and
  `i != sigma`;
* `[X, X_sigma,j(a_2)] = 1` — roots `(sigma,j), (i,l)`, needing `sigma != l`
  and `i != j`;

so `X` centralises both factors of `T`, hence `T`.  The same choice handles
`[T, V]`.  **So `H(2)` holds outright.**

The induction therefore has a genuine base, and what fails at `t >= 3` is only
that the convenient-representative trick needs `sigma`-independence at length
`t` — the very statement being proved.  At length two that independence is
supplied by the emitted relations; at higher length nothing supplies it.

**Minimal missing lemma.**

> **Lemma X.**  In `G_0`, for four distinct indices `i,j,l` and a word `w`
> with first letter `a`, the spare-`l` object `D^l_ij(w) = [Ehat_il(a),
> Ehat_lj(w')]` commutes with `Ehat_il(a)` and with `Ehat_lj(w')`.

Equivalently: each root subgroup, as generated by the nested commutators, is
abelian *for its own defining spare*.  Everything else in §§1-4 then closes
and `G_0 = St_5(L)`.

Lemma X is exactly the statement one expects to be the technical core of
[KrM, Theorem 3], and it is the single item to look for in that paper.

**The obstruction in one sentence.**  Bilinearity of the commutator in its
*second* argument is free (Lemma 2.1: it needs `[U_kj, U_ij] = 1`, which holds
on generators).  Bilinearity in the *first* argument needs `[U_il, U_ij] = 1`,
and Lemma 5.1 supplies exactly that — **but only when the element of `U_ij` is
presented with a spare index different from `l`.**  The commutator
`[U_il, U_lj]` lands, by construction, in the spare-`l` presentation of
`U_ij`.  So the one presentation the argument produces is the one presentation
whose commutation it cannot use.  Every reorganisation tried below reproduces
that clash one index over.

**Routes tried and rejected**, recorded so they are not retried:

* *Decompose `X` through a fourth index.*  `X = [Ehat_im(a), X_ml(1)]` or
  `[X_im(1), Ehat_ml(a)]` for a spare `m`.  Either way one factor carries root
  `(m,l)` or `(i,m)`, and the `(m,l)` factor collides with `V`'s root `(l,j)`
  at the shared index `l` — an (St3) situation, not (St2), so it does not
  commute.  Every decomposition of `X` reproduces this collision.
* *Decompose `V` instead.*  `V = [Ehat_lm(b_1), Ehat_mj(b_2)]` puts a factor at
  root `(l,m)`, which collides with `X`'s root `(i,l)` at `l`.  Symmetric
  failure.
* *Route through a third spare `rho notin {i,j,k,l}` (available at `n = 5`).*
  Lemma 5.1 does supply all three commutations for `D^rho`, but Lemma 3.1's
  `T` is by construction the spare-`l` object; comparing `D^k` and `D^l`
  through `D^rho` needs two applications of Lemma 3.1 and each reintroduces
  the same clash one index over.
* *Hall--Witt.*  With `[X,Z] = 1` the identity reduces to
  `[[X,Y^{-1}],Z]^Y = [X,[Y,Z^{-1}]]^Z`, which equates the two spare
  definitions only up to conjugation by `Y` and `Z` — and discharging those
  conjugations requires exactly the same length-`t` commutations.
* *Rewrite via the ring relation `e^*e = 1`* to express
  `Ehat_ij(w) = [Ehat_ik(w e^*), X_kj(e)]`.  This is available in our `L` and
  is a genuine de-nesting, but it raises the word length from `t` to `t+1`, so
  it cannot serve an induction on length.

---

## 6. Mitigation: widen the base of the induction (free, and done)

`H(t)` bottoms out at length two, which the emitted family already forces.
Because **enlarging `T_St` is always safe** — any word verified to lie in
`Rbar` keeps `<<T_St>> <= Rbar` and can only help reach `Nbar` — the base can
be widened at will by emitting the spare-index difference words

```
D^sigma_ij(w) · ( D^tau_ij(w) )^{-1}
```

for every root, every short word `w`, and every pair of spares.  All of these
are in `Rbar` (both sides have the same image in `Q`), so they are legal
additions, and each one discharges an instance of Lemma X's consequence
without proving Lemma X.

`experiments/atlas_relator_rank5_chain_differences.py` emits them; results in
`ATLAS_RANK5_DICTIONARY_2026-08-15.md`.  This does not prove completeness, and
it is not claimed to: an unbounded family of instances cannot be discharged by
finitely many.  Its value is that if Lemma X turns out to need only bounded
length — which the absorption argument of §2 makes plausible — the emitted
relators already cover that range.


---

## 7. The involutivity relators (added 2026-08-15, late)

`STEINBERG_SPARE_INDEX_2026-08-15.md` §8 shows the emitted family does **not**
imply `Ê_ij(a)² = 1`, which is required because `Ê_ij` must be a homomorphism
`(L,+) → G₀` and `a + a = 0` over `F₂`.  The obstruction is a clean lift: the
Leavitt path algebra `L_Z(1,2)` satisfies the same five Cuntz–Krieger relations
(they carry no characteristic assumption) and is a free `Z`-module, so
`St₅(L_Z)` receives a homomorphism from `G₀` under which `X_ij(1)²` maps to
`E_ij(2) ≠ 1`.  The lift is legitimate because the canonical two-letter words
are built by `root_word` as purely multiplicative nested commutators, with no
additive decomposition anywhere.

**Emitted and verified** (`experiments/atlas_relator_rank5_involutivity.py`):

```
involutivity relators considered:                      100
  reduce to the empty word in Pbar (already trivial):   12
  nontrivial words emitted:                             88
  verified to lie in Rbar:                        88 of 88
syllable length: min 8  max 33
X-length:        min 8  max 184  total 6,460
relators with nontrivial (p1,p2):                 0 of 88
```

Two things worth recording.

* The 12 vacuous ones are exactly the single-syllable dictionary words: a
  chart transvection is an involution in `GL_4(F₂)`, so its square already
  reduces to the empty word in `P̄` itself.  Those instances of `x_ij(a)² = 1`
  hold in the source group and need no relator.
* **None of the 88 escapes the cartesian subgroup.**  This is structural, not
  a coincidence and not a bug: checked directly, the factor projections
  `p_1`, `p_2` of every one of the 100 dictionary words have order 1 or 2 in
  `GL_4(F₂)`, so every square projects to the identity.  Consequently the
  involutivity family would FAIL screen (D) on its own.  That is expected — it
  is a supplement, not a candidate list — but it means the screen must be run
  on the merged `T_St`, never on this block alone, and a future audit that
  screens blocks separately will get a false alarm here.

**64 of the 88 were already in the family.**  Merging against the emitted
family reports `4,612 existing + 24 new (64 already present) = 4,636`.  That
was surprising enough to check rather than trust, and it is real: rebuilding
the family block by block and matching reduced free-product words shows all 64
collisions land in the cross-root (St2) `orth` block, e.g.

```
inv_12_e == orth_12_52_e1        inv_13_1 == orth_13_15_11
inv_12_f == orth_12_52_f1        inv_13_e == orth_13_15_e1
```

so `x_12(e)²` and `[x_12(e), x_52(1)]` are literally the same reduced word in
`A₈ * A₈`.  Note the two facts are consistent and must not be conflated:

* the `L_Z` counterexample is about the **abstract** `G₀` on the `X`
  generators, where all 100 relators are genuinely independent of (A)+(B)+(C);
* the coincidence is a phenomenon of the **atlas realisation**, where free
  reduction in `A₈ * A₈` identifies particular words.  The atlas presentation
  carries more relations than the abstract scheme, so it can already imply
  instances the abstract scheme does not.

Net effect on the deliverable: only **24 genuinely new words**, and
`|T_St| = 4,612 + 24 + 12` reverse-dictionary relators `= 4,648`.

Membership in `R̄` is not taken on trust: each square is evaluated exactly.
The reason it holds is that `x_ij(a) = 1 + m` with `m = d_{E_i} a d_{E_j}^*`
and `m² = 0`, because `E_i ≠ E_j` are distinct members of a prefix code so
`d_{E_j}^* d_{E_i} = 0`; hence `x_ij(a)² = 1 + m² = 1` over `F₂`.


### 7.1 Step-4 acceptance on the enlarged list (MSI job 15864167, 28 s)

```
relators loaded:                                     4,636
SCREEN (D)  72 of 4,636 escape ker(Pbar ->> A8 x A8)   passes
SCREEN (A)  0 survivors of 2 x 1,814,400 degree-10 pairs  passes
```

The (D) count is unchanged at 72 because no involutivity relator escapes; the
enlarged list passes on the strength of the original family's escapees, which
is exactly why the block must never be screened on its own.


---

## 8. Numerical witness for the (I2) route (MSI job 15865413, 109 s)

`experiments/atlas_relator_i2_route_check.py`.  Requested by the coordinator as
the one assertion in the corrected lemma lacking its own witness.

### Part A — exhaustive, over `S_4` and `S_5`

Every ordered triple `(X,Y,Z)` is classified by which of the three hypotheses
hold, and both `(I2)` and the conclusion are tested in every cell.  `S_5`:
`1,728,000` triples.

```
[X,Z] [U,V] [Z,V]        triples    (I2) ok   (I2) BAD   T=[U,Z]  T!=[U,Z]
T  T  T                    24960      24960          0     24960         0
T  T  .                    29040      29040          0     20640      8400
T  .  T                     4320       4320          0         0      4320
T  .  .                    42480      42480          0      8400     34080
.  T  T                   105600      21000      84600     21000     84600
.  T  .                   173520      12480     161040     12120    161400
.  .  T                   124320       3480     120840      2880    121440
.  .  .                  1223760      47040    1176720     27000   1196760
```

* **`(I2)` holds in every one of the 100,800 triples with `[X,Z] = 1`**, and
  fails in 1,543,200 of the 1,627,200 without it.  So `[X,Z] = 1` is exactly
  the right hypothesis for `(I2)`, and tight in both directions.
* **The conclusion `T = [U,Z]` holds in all 24,960 triples satisfying all
  three hypotheses, with zero violations.**
* **Each hypothesis is load bearing** — dropping one admits counterexamples:

  ```
  drop [X,Z] : 105,600 triples,  84,600 violate
  drop [U,V] :   4,320 triples,   4,320 violate   (every single one)
  drop [Z,V] :  29,040 triples,   8,400 violate
  ```

* **`[Y,V] = 1` is NOT needed**: 4,200 triples satisfy all three hypotheses
  while `[Y,V] != 1`, and **zero** of them violate the conclusion.  This is the
  direct witness for the claim that my Lemma 3.1's extra hypothesis was
  superfluous.

`S_4` (13,824 triples) shows the same pattern, with 168 `[Y,V]`-free witnesses
and zero violations.

### Part B — the intended root configuration, in `Q`

All 3,000 ordered index quadruples × coefficient pairs, with
`X = x_il(a)`, `Y = x_lk(1)`, `Z = x_kj(b)` from the verified dictionary:

```
[X,Z] = 1   holds in 3000 of 3000
[U,V] = 1   holds in 3000 of 3000
[Z,V] = 1   holds in 3000 of 3000
[Y,V] = 1   holds in 3000 of 3000
(I2)        holds in 3000 of 3000
T = [U,Z]   holds in 3000 of 3000
```

### The methodological point, which matters more than the counts

`[Y,V] = 1` **holds in the atlas configuration too** — 3,000 of 3,000.  So the
earlier check in `Q` could never have detected that my Lemma 3.1 carried a
superfluous hypothesis: the superfluous hypothesis is simply true there.  Only
an abstract test, in a group where the hypotheses can be violated
independently, separates a necessary hypothesis from an incidental one.

That generalises the trap already recorded: an over-strong lemma manufactures
a phantom obstruction, **and testing it only in the intended model will not
reveal that the extra hypothesis was never needed.**  Verification in the
target model confirms conclusions; it does not audit hypotheses.
