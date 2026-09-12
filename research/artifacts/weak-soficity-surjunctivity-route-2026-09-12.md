# Weak soficity as a supply of surjunctivity charts

Lane `gk-free-pos`, 2026-09-12. Supports the claims
`weakly-sofic-groups-are-surjunctive`,
`regular-action-makes-weak-sofic-defects-maximal` and
`simple-model-weak-soficity-with-small-defect-is-lef`.

## Why this approach

Every positive mechanism recorded in this corpus needs finite models with a
*Hamming* metric: Gromov--Weiss counting for sofic groups, dense periodic
points for residually finite groups, and the permanence theorems built on
them. `sofic-permanence-closure-omits-simple-fa-nonsofic-groups` shows that
iterating those permanence theorems never reaches a finitely presented simple
nonsofic group.

Weak soficity is the one approximation notion in this corpus that is
*strictly weaker than soficity and still supplies finite models*: by
`weakly-sofic-not-sofic` the Kun--Thom wreath is weakly sofic and not sofic.
If Gromov--Weiss counting ran on weakly sofic approximations, it would be a
positive mechanism that is not a permanence closure of the sofic groups, and
so not excluded by the closure obstruction. No lane has tested that, and this
artifact does.

The answer here is negative in the sharpest available form, and the negative
answer locates the exact missing ingredient.

## Conventions

A *length* on a finite group `H` is `l: H -> [0,1]` with `l(1) = 0`,
`l(x) = l(x^-1)`, `l(xy) <= l(x) + l(y)`, and `l(zxz^-1) = l(x)` for all `z`.
Lengths correspond exactly to bi-invariant metrics `d(x,y) = l(xy^-1)`.

A *weakly sofic approximation* of a group `G` with separation `c > 0` and
defect `eps` on a finite `F` in `G` is a finite group `H`, a length `l`, and a
map `phi: F -> H` with `phi(1) = 1`,

```text
l( phi(g) phi(h) phi(gh)^-1 ) <= eps     for g, h, gh in F,
l( phi(g) )                   >= c       for g in F, g != 1.
```

`G` is weakly sofic when such data exist for every `F` and every `eps > 0`.
Soficity is the special case `H = Sym(V)` with `l` the normalized Hamming
length. `G` is LEF when the defect can be taken to be exactly `0`.

For a finite `H`-set `V` write

```text
l_V(z) = 1 - fix(z)/|V|,     fix(z) = |{ v in V : zv = v }|.
```

**Lemma 0.** `l_V` is a length on `H`, and it is the normalized Hamming
length of the permutation action.

*Proof.* `l_V(1) = 0`; `fix(z) = fix(z^-1)`; `fix(zxz^-1) = fix(x)` because
`v -> zv` is a bijection of fixed sets; and if `xy` moves `v` then `x` or `y`
moves a point, giving subadditivity from
`{v : xyv != v}` contained in `{v : yv != v} u {w : xw != w}`. QED

## 1. What a Gromov--Weiss chart system consumes

Fix an injective cellular automaton `tau` over `G` with memory `M`, rule `mu`,
a local left inverse `sigma` with memory `N`, and a Garden-of-Eden pattern on a
window `Omega`. Put `K = N u M u N M u Omega Omega^-1`, a finite subset of `G`.

Given a finite `H`-set `V` and `phi: F -> H` with `F` symmetric and
`K K^-1` contained in `F`, transport the rules to `A^V` along
`psi(g) = phi(g^-1)`:

```text
tau_V(z)(v) = mu( ( z( psi(m) v ) )_{m in M} ),
sigma_V(w)(v) = nu( ( w( psi(n) v ) )_{n in N} ).
```

*Convention.* With the house convention `tau(x)(g) = mu((x(gm))_m)`, the
composite on `G` reads the coordinate `nm`, while the composite on `V` reads
the point `psi(m) psi(n) v`. Transporting along `phi` itself would model
`G^op`. Transporting along `psi` corrects the order, because
`psi(m)psi(n)psi(nm)^-1 = phi(m^-1)phi(n^-1)phi(m^-1 n^-1)^-1` is the
multiplicative defect of `phi` at the pair `(m^-1, n^-1)`, and separation is
unchanged because `F` is symmetric. The first version of this artifact
transported along `phi` directly; gk-vf-positive flagged the reversal
(Section 8 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).

**Lemma 1.1.** If `v` in `V` satisfies `psi(m) psi(n) v = psi(nm) v` for all
`n in N`, `m in M`, then `sigma_V tau_V (z)(v) = z(v)` for every `z in A^V`.

*Proof.* Put `x(g) = z(psi(g) v)` for `g` in `K`. Then
`sigma_V tau_V(z)(v) = nu( ( mu( ( z(psi(m)psi(n)v) )_m ) )_n )`. Under the
hypothesis this is `nu( ( mu( ( x(nm) )_m ) )_n ) = (sigma tau x)(1) = x(1)`,
because `sigma tau = id` is an identity of local rules, and `x(1) = z(v)`
because `psi(1) = 1`. QED

**Lemma 1.1 is only a sufficient condition.** At a vertex where a defect moves
`v`, the transported identity can still hold, for instance when the rules
ignore the moved coordinates. Below, a *bad* vertex is one where Lemma 1.1
gives no guarantee, not one where the identity is shown to fail.

So the counting argument needs the vertices where Lemma 1.1 applies to be
most of `V`. The bad set for one pair `(n,m)` is
`{v : psi(m)psi(n)psi(nm)^-1 v != v}`, whose normalized size is exactly `l_V`
of that defect. Summing over the finitely many pairs:

**Proposition 1.2.** If `l_V(phi(a)phi(b)phi(ab)^-1) <= delta` for all
`a, b, ab` in `F`, then Lemma 1.1 applies off a set of vertices of normalized
size at most `|N||M| delta`. If moreover `l_V(phi(g)) >= c'` for `g != 1` in
`F`, the charts `g -> psi(g)v` are injective on `K` for at least a

```text
1 - |K|^2 (1 - c' + 2 delta)
```

fraction of `v`.

*Proof.* The first half is Lemma 1.1 and a union bound. For the second, the
chart fails at `v` when `psi(a)v = psi(b)v` for some `a != b` in `K`, that is
when `v` is fixed by `psi(b)^-1 psi(a)`, a set of normalized size
`1 - l_V(psi(b)^-1 psi(a))`. Write `d = phi(b)phi(b^-1)`, the inversion defect
(`phi(1) = 1`), so `psi(b)^-1 = phi(b^-1)^-1 = d^-1 phi(b)`, and
`phi(b)phi(a^-1) = d' phi(b a^-1)` with `d'` a multiplicative defect. Then
`phi(b a^-1) = d'^-1 d psi(b)^-1 psi(a)`, and symmetry with subadditivity give
`l_V(psi(b)^-1 psi(a)) >= l_V(phi(b a^-1)) - 2 delta >= c' - 2 delta`, since
`b a^-1 != 1` lies in `F`. A union bound over the at most `|K|^2` ordered pairs
gives the displayed fraction. The first version stated `1 - |K|^2 (1 - c')`
and omitted the `2 delta`; corrected after gk-vf-positive's check. QED

**So the counting proof consumes exactly one thing: an `H`-set `V` whose
Hamming length `l_V` is small on the defects and bounded below on
`phi(F \ {1})`.** The given length `l` never enters the count. Soficity
supplies `V` by fiat. Weak soficity supplies `l`, and the question is whether
`l` forces such a `V` to exist.

## 2. The regular action is useless, and maximally so

The obvious candidate is `V = H` with left translation.

**Theorem A.** For `V = H` with the left translation action, `l_V` is the
discrete length: `l_V(z) = 1` for every `z != 1`, and `l_V(1) = 0`.

*Proof.* `zv = v` for some `v` forces `z = 1`. So `fix(z) = 0` for `z != 1`. QED

**Corollary A.1.** Let `(H, l, phi)` be a weakly sofic approximation and let
`V = H` carry the left translation action. Then Proposition 1.2's hypothesis
`l_V(defect) <= delta` with `delta < 1` holds if and only if every defect
`phi(a)phi(b)phi(ab)^-1` is trivial, that is if and only if `phi` is an exact
homomorphism on the relevant products.

*Corollary A.2.* Through the regular action, Lemma 1.1 applies at a positive
fraction of vertices exactly when the relevant defects are trivial, that is on
LEF data. No genuinely metric approximation survives as input to the counting
argument. This does not say that the transported identity fails: the rules may
ignore the moved coordinates.

This is the precise form of the folklore remark that not every bi-invariant
metric on a finite group restricts from a Hamming metric. The point for this
program is sharper: the regular action does not merely lose the metric, it
sends every nonzero defect to the *maximal* Hamming defect `1`, so no choice
of constants rescues the counting guarantee.

**Remark A.3 (the conjugation action pulls the other way).** For `V = H` with
the conjugation action, `l_V(z) = 1 - |C_H(z)|/|H| = 1 - 1/|z^H|`. Separation
is then automatic and strong on any family of finite simple groups whose
minimal nontrivial conjugacy class size `m(H)` tends to infinity, since
`l_V(z) >= 1 - 1/m(H)` for `z != 1`. But *the same bound applies to the
defects*: a nontrivial defect also has `l_V >= 1 - 1/m(H)`. So the conjugation
action makes separation free and near-multiplicativity impossible, exactly the
reverse of the regular action. The two natural actions fail for opposite
reasons, and that is the structural obstruction to running the count on a
bi-invariant metric.

## 3. Simple models force exactness

The failure above is not an artifact of choosing a bad action when the models
are simple. Simplicity bounds every length from below.

**Theorem B.** Let `H` be a finite simple group and `l` a length on `H` with
`l(x_0) >= c` for some `x_0 in H`. Then `l(k) >= c/|H|` for every `k != 1`.

*Proof.* Fix `k != 1`. Let `S_n` be the set of products of at most `n`
conjugates of `k` and of `k^-1`. Each `S_n` is symmetric and closed under
conjugation, `S_n` is contained in `S_{n+1}`, and `S = union_n S_n` is a
subgroup: it is closed under products by construction and under inverses by
symmetry. `S` is normal because each `S_n` is conjugation-closed, and it
contains `k != 1`, so `S = H` by simplicity.

The chain `S_1` in `S_2` in `...` is increasing inside `H`. If `S_n = S_{n+1}`
then `S_m = S_n` for all `m >= n`, so `S_n = H`. Since `|S_1| >= 1` and each
strict inclusion adds at least one element, `S_{|H|} = H`.

So every `x in H` is a product of at most `|H|` conjugates of `k^{+-1}`. By
subadditivity and conjugation invariance, `l(x) <= |H| l(k)`. Applying this to
`x_0` gives `c <= |H| l(k)`. QED

**Theorem C.** Let `G` admit, for every finite `F` in `G` and some fixed
`c > 0`, a weakly sofic approximation `(H_F, l_F, phi_F)` with separation `c`,
with `H_F` finite simple, and with defect

```text
eps_F < c / |H_F| .
```

Then `G` is LEF, hence sofic, hence surjunctive.

*Proof.* Fix `F`. Separation gives `l_F(phi_F(g)) >= c` for `g != 1`, so
Theorem B applies with `x_0 = phi_F(g)` for any such `g` (if `F = {1}` there is
nothing to prove). Let `k = phi_F(a)phi_F(b)phi_F(ab)^-1` be a defect. Then
`l_F(k) <= eps_F < c/|H_F|`, so `k = 1` by Theorem B. Hence `phi_F` is an exact
homomorphism on `F`, and it is injective on `F` because `l_F(phi_F(g)) >= c > 0`
for `g != 1`. That is a local embedding of `F` into a finite group, so `G` is
LEF.

LEF implies sofic: given the local embedding `phi_F: F -> H_F`, let `H_F` act
on itself by left translation. The induced map into `Sym(H_F)` is multiplicative
on `F`, and by Theorem A every nontrivial image has normalized Hamming length
`1`, so this is a sofic approximation with defect `0` and separation `1`.
Soficity gives surjunctivity by `sofic-groups-are-surjunctive`. QED

**What Theorem C does and does not say.** The hypothesis `eps < c/|H|` is
severe: weak soficity asks only for `eps -> 0` with `|H|` unconstrained, and
`c/|H|` shrinks with the model. So Theorem C does not collapse weak soficity to
LEF. What it does is locate the room: on simple models, *all* of the metric
content of a weakly sofic approximation lives in the window
`c/|H| <= eps -> 0`. Any proof that weakly sofic groups are surjunctive must
use approximations whose defect decays no faster than the reciprocal of the
model size, or must use models that are far from simple, where the length can
be small on a large normal subgroup.

## 4. Status

`weakly-sofic-groups-are-surjunctive` is open, and this artifact does not
decide it. What is settled here:

* the counting proof consumes an `H`-set, not a metric (Section 1);
* for the counting guarantee, the regular action accepts exactly LEF data and
  nothing weaker (Theorem A and its corollaries); it does not show that the
  transported identity fails;
* the conjugation action fails for the opposite reason (Remark A.3);
* on simple models the whole metric regime is confined to defects at least
  `c/|H|` (Theorems B and C).

The route stays open only through models with large normal subgroups on which
the length is small. That is the same place `glebsky-rivera-w-sofic-criterion`
locates the content of weak soficity, and it is where a future attempt should
start.

## 5. The chart search is a linear program over the subgroup lattice

Section 1 leaves the route needing a finite `H`-set `V`. That search can be
made finite and explicit.

**Lemma 5.1.** Let `V` be a finite `H`-set with orbits `V_1, ..., V_r` and
point stabilizers `L_i`. Then `l_V = sum_i p_i l_{H/L_i}` with
`p_i = |V_i|/|V|` a probability vector.

*Proof.* Orbits are invariant, so `fix_V(z) = sum_i fix_{V_i}(z)`. Each orbit
is `H`-isomorphic to `H/L_i`, and an isomorphism of `H`-sets preserves
fixed-point counts. Divide by `|V|` and regroup. QED

Conversely a rational convex combination is realized by a disjoint union of
coset spaces with the corresponding multiplicities. So the achievable Hamming
lengths on `H` are exactly the convex hull of `{ l_{H/L} : L <= H }`.

**Corollary 5.2.** A weakly sofic approximation `(H, l, phi)` supports a
Gromov--Weiss transport if and only if the linear program

```text
sum_L lambda_L l_{H/L}(k)      <= delta      for every defect k,
sum_L lambda_L l_{H/L}(phi(g)) >= c'         for every g != 1 in F,
lambda >= 0,  sum_L lambda_L = 1
```

is feasible over the subgroup lattice of `H`.

The two extreme points are the failures already recorded: `L = 1` gives the
discrete length, maximal on defects (Theorem A), and `L = H` gives the zero
length, which separates nothing. Feasibility asks for an intermediate mixture
that separates `phi(F)` while nearly fixing the defects. The given length `l`
enters only by declaring which elements are defects and which must be
separated, which is why no argument in Sections 2 and 3 could use `l` itself.

This is the same shape as the character-simplex linear program recorded for
the Hilbert-embeddable witness question, with coset lengths in place of
normalized characters, and it is the concrete form in which
`weakly-sofic-groups-are-surjunctive` should next be attacked.
