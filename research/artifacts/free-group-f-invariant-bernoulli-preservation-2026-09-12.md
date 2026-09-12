# Mass transport on trees: the f-invariant forces Bernoulli preservation over free groups

Lane `gk-p-bernoulli-mass`, 2026-09-12. Supports
`free-group-injective-ca-preserve-bernoulli-via-f-invariant` and records where
entropy transport stops for `every-injective-ca-preserves-uniform-bernoulli-measure`.

The theorem is not new as a surjunctivity statement, since free groups are residually
finite. What is new here is the mechanism: a proof that uses no finite model, only a
measure-conjugacy invariant with an Euler-characteristic formula and Shannon
submodularity. It shows what a transport invariant can do, and Section 5 shows the
exact points where the same argument cannot be run.

## 1. Setting

Let `G = F_r = <s_1, ..., s_r>`, `A` a finite alphabet with `q = |A|`, `mu` the
uniform product measure on `A^G`, and `tau` an injective cellular automaton with image
`Y`. Put `nu = tau_* mu`.

* `tau` is a continuous equivariant bijection `A^G -> Y`, so it is a measure
  conjugacy between `(A^G, mu)` and `(Y, nu)`.
* The coordinate partition `eta` (by the symbol at `e`) is generating on `Y`.
* For finite `S`, write `H(S)` for the Shannon entropy of `y|_S` under `nu`. Shift
  invariance gives `H(gS) = H(S)`.

`B_n` is the word-metric ball of radius `n`.

## 2. The functional and splitting monotonicity (elementary)

For a finite partition `alpha` put

    F(alpha) = (1 - 2r) H(alpha) + sum_i H(alpha v s_i alpha).

**Lemma 2.1.** For each generator `s` (and `s^-1`), `F(alpha v s alpha) <= F(alpha)`.

*Proof.* Write `beta = alpha v s alpha` and `d = H(alpha v s alpha) - H(alpha)`.
Submodularity, `H(X v Y) + H(X ^ Y) <= H(X) + H(Y)` for joins of translates, gives:

* `H(alpha v s alpha v s^2 alpha) <= 2 H(alpha v s alpha) - H(alpha)`. So the term
  for the generator `s` grows by at most `d`.
* For `s_i != s`, `H(alpha v s alpha v s_i alpha) <= H(alpha v s alpha) + H(alpha v s_i alpha) - H(alpha)`.
  Adding `s_i s alpha` costs at most `H(s_i alpha v s_i s alpha) - H(s_i alpha) = d`.
  So each such term grows by at most `2d`.

Hence

    F(beta) - F(alpha) <= (1 - 2r) d + d + 2(r - 1) d = 0.   QED

Along the ball refinements `eta^(B_n)`, obtained by successive splittings, `F` is
non-increasing. So `f(eta) = lim_n F(eta^(B_n))` exists and equals the infimum.

## 3. The one imported input

**Bowen (2010).** L. Bowen, *A measure-conjugacy invariant for free group actions*,
Ann. of Math. 171 (2010), 1387–1400. For a measure-preserving action of `F_r` and
finite generating partitions `alpha` and `beta`, `f(alpha) = f(beta)`. So `f` is a
measure-conjugacy invariant. The proof uses no sofic approximation; the later
identification with sofic entropy is not needed here.

For uniform Bernoulli with the coordinate partition, independence makes every
submodularity step an equality. So `F(eta^(B_n)) = log q` for all `n`, and `f(mu) = log q`.

## 4. The induction

By Section 3 and the conjugacy, `f(nu) = f(mu) = log q`. By Section 2,

    log q <= F(eta^(B_n))   for all n.                                   (4.1)

**Tree identities.** Put `T_{n,i} = B_n ∪ s_i B_n` and `D_{n,i} = B_n ∩ s_i B_n`.

* In a tree, the distances to the adjacent vertices `e` and `s_i` differ by exactly one.
  So `D_{n,i} = B_{n-1} ∪ s_i B_{n-1} = T_{n-1,i}`, and `D_{0,i}` is empty.
* A finite subtree has one more vertex than edges, and `B_n` has `|D_{n,i}|` edges
  labelled `s_i`. So

      |B_n| - sum_i |D_{n,i}| = 1,   sum_i |T_{n,i}| = (2r - 1)|B_n| + 1.   (4.2)

**Upper bound.** Submodularity and invariance give `H(T_{n,i}) <= 2H(B_n) - H(D_{n,i})`.
So

    F(eta^(B_n)) <= H(B_n) - sum_i H(D_{n,i}).                            (4.3)

**Claim.** For every `n`, `nu` is uniform on `B_n` and on every `T_{n,i}`.

*Proof by induction.*

1. *Base, the ball `B_0`.* By (4.1) and (4.3) with `D_{0,i}` empty,
   `log q <= H(B_0) <= log q`. So `y_e` is uniform.
2. *From `T_{n-1,i}` to `B_n`.* Suppose `nu` is uniform on every `T_{n-1,i} = D_{n,i}`.
   By (4.1), (4.3) and (4.2),
   `H(B_n) >= log q + sum_i |D_{n,i}| log q = |B_n| log q`. So `nu` is uniform on `B_n`.
3. *From `B_n` to `T_{n,i}`.* Suppose `nu` is uniform on `B_n`. By (4.1),
   `sum_i H(T_{n,i}) >= log q - (1 - 2r)|B_n| log q = sum_i |T_{n,i}| log q`, using (4.2).
   Each `H(T_{n,i}) <= |T_{n,i}| log q`, so every term is an equality, and `nu` is
   uniform on every `T_{n,i}`.

For `n = 0`, step 3 starts from step 1. QED

The balls exhaust `G`, so `nu = mu`. By `injective-measure-preserving-ca-is-surjective`,
`tau` is surjective.

## 5. Where entropy transport stops

The argument has exactly three ingredients:

* (a) a conjugacy invariant equal to `log q` at Bernoulli;
* (b) a formula expressing it as an Euler characteristic of coordinate windows, one
  vertex term and one term per edge orbit;
* (c) Shannon submodularity, which bounds each edge term above by its two endpoints
  minus their overlap.

Identity (4.2) is the mass-transport balance of the Cayley tree: `r` edges leave and
`r` edges arrive at every vertex, and each translation by a generator is a bijection
of the index set preserving `nu`.

**(i) Two-cells.** A group with relations has a Cayley 2-complex. An Euler functional
of the same shape needs face terms, and step (c) would need the three-set
inclusion–exclusion bound

    H(A ∪ B ∪ C) <= H(A) + H(B) + H(C) - H(A ∩ B) - H(B ∩ C) - H(A ∩ C) + H(A ∩ B ∩ C).

This bound is false. Take sites `a, b, c`, with `A = {a,b}`, `B = {b,c}`, `C = {a,c}`,
and one uniform bit copied to all three sites. The left side is `log 2`; the right side
is `3 log 2 - 3 log 2 + 0 = 0`. Duplicated coordinates are exactly the redundancy an
image measure of a strict automaton carries: siblings in the tree calibration. So the
face step fails precisely on the measures a proof must exclude. Shannon inequalities
supply only the two-set step, which is why the tree case goes through.

**(ii) Kazhdan hosts.** Gottschalk reduces to finitely generated simple Kazhdan groups
(`gottschalk-reduces-to-fg-simple-kazhdan-groups`). Such a group has property FA, so it
is not free and acts on no tree without a global fixed point. A subgroup `F_2 <= G`
does not help: the coordinate partition of `A^G` is not generating for the subaction,
whose base `A^(F_2 \ G)` is infinite. So no host of the reduction carries a
tree-transport functional of this kind.

**(iii) Unimodularity.** Step (b) uses `H(s_i S) = H(S)` for a bijective translation of
the index set. On the end-fixing tree the parent map is two-to-one, the per-vertex edge
count is unbalanced (one edge up, two down), and the functional has no invariant
normalization. The strict automaton of `end-fixing-tree-symmetries-carry-strict-automata`
lives exactly there.

**What a two-dimensional replacement would need.** Either an invariant whose face terms
have a valid upper bound on the image measure, or a proof that the image measure of an
injective automaton has no copied coordinates. The second is the conclusion itself.
