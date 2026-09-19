---
rg: 2
id: window-annihilators-force-infinitely-many-lamplighter-orbits
kind: claim
title: A lamplighter L wr Z has infinitely many orbits on any module containing a vector fixed by a half-line of lamps whose annihilator is generated inside a finite window of lamps
artifacts:
  - research/artifacts/commuting-conjugate-coset-switch-2026-09-16.md
distinct_from:
  finite-bi-index-forces-finite-index-in-metabelian-groups: that is Cornulier's Proposition 3.20, class two, where simple modules over the virtually polycyclic acting group are finite (Roseblade); this is class three, where the acting group L wr Z is not polycyclic, infinite simple modules exist, and finiteness of orbits has to be killed by an orbit invariant rather than by finite length.
  kms-natural-affine-actor-has-infinitely-many-orbits: that is the natural configuration module of one KMS machine group, with an abelian acting group, killed by the |w|_a filtration; this is an arbitrary module over the metabelian group L wr Z, the rank-one case of the section-module question that the KMS refinement leaves open.
  orbit-finite-affine-actions-are-type-a: that is the criterion turning an orbit-finite module into a type (A) actor; this kills one class of candidate orbit-finite modules. L wr Z is not finitely presented, so it enters only as the acting group R = S/A of step 1 of the A_p^2 A refinement, which needs R finitely generated only.
  normal-lamp-sums-do-not-force-finite-double-cosets: that concerns lamp sums as double-coset witnesses; this is an orbit invariant on modules over the lamplighter itself.
---

**ESTABLISHED** (lane proof, swarm-0917-w14-w14-bh-break; not reviewed; no
priority claimed). The proof is self-contained linear algebra over a field. No
external input is used except in the "Why it matters" paragraph, which quotes
Cornulier verbatim and proves nothing from him.

## Statement

Let `k` be any field and `L != 1` a finite abelian group. Put `R = L wr Z = B x| <t>`,
where `B = (+)_(i in Z) L_i`, `L_i = t^i L_0 t^-i`, and `L_0 = L`. For an interval `I`
of `Z`, write `B_I = (+)_(i in I) L_i`. For example, `B_(>=n)` and `B_([a,b))` are
of this form.

Let `V` be any `k[R]`-module; it need not be simple. For `0 != v` in `V`:

- `kappa(v) = min{ n : B_(>=n) fixes v }` in `Z u {+inf}`. Here `kappa(v) = -inf`
  exactly when `v` is in `V^B`.
- If `kappa(v)` is finite, put `A_v = k[B_(<kappa(v))]` and let
  `I(v) = { a in A_v : a v = 0 }` be the annihilator.
- For an integer `j <= kappa(v)`, call `v` **`j`-windowed** if
  `I(v) = A_v . ( I(v) cap k[B_([j, kappa(v)))] )`, i.e. the annihilator is generated
  by elements supported on lamps at positions in `[j, kappa(v))`.
  - Being `j`-windowed implies being `(j-1)`-windowed, because the window only grows.
  - If `I(v)` is a finitely generated ideal, then `v` is `j`-windowed for some `j`.

**Theorem.** Suppose some `0 != v` in `V` has finite `kappa(v)` and is
`j`-windowed for some `j`. Then `R`, and even `k^* x R`, has infinitely many
orbits on `V`.

**Corollary (trichotomy for simple modules).** Let `char k = p`, let `L` be a
`p`-group, and let `V` be an infinite simple `k[R]`-module with finitely many
`R`-orbits. Put `U_+ = union_n V^(B_(>=n))` and `U_- = union_n V^(B_(<n))`.

- `V^B = 0`.
- `U_+` and `U_-` are submodules, and at most one of them is nonzero.
- If `U_+ != 0`, then `U_+ = V`, and no nonzero vector of `V` is windowed.
- The mirror statement, with `t` replaced by `t^-1`, holds for `U_-`.

So a counterexample must have one of two forms:

- **Type (ii).** It is one-sided (say `U_+ = V`), and every annihilator
  `I(v) <= k[B_(<kappa(v))]` fails to be generated inside any finite window. In
  particular, no such annihilator is finitely generated.
- **Type (iii).** No nonzero vector is fixed by any half-line of lamps.

## Proof of the theorem

**Step 0 (a tensor fact).** Fix `q <= kappa` and put `W = B_([q,kappa))`. Then
`B_(<kappa) = B_(<q) x W`, and so
`k[B_(<kappa)] = k[B_(<q)] (x)_k k[W]`. For `x` in `k[B_(<q)]` and `y` in `k[W]`, the
product in the group algebra is `x (x) y`.

For a subspace `J'` of `k[W]`, the ideal it generates is
`k[B_(<kappa)] . J' = k[B_(<q)] (x) J'`. If `x != 0`, then `x (x) y` lies in it iff
`y` lies in `J'`.
- *If.* This is clear.
- *Only if.* Pick a functional `phi` with `phi(x) = 1`. Then `phi (x) id` maps
  `k[B_(<q)] (x) J'` into `J'` and sends `x (x) y` to `y`.

More generally, let `a = sum_beta beta (x) a_beta`, where `beta` runs over the
group elements of `B_(<q)`, which form a basis. Then `a` lies in
`k[B_(<q)] (x) J'` iff every `a_beta` lies in `J'`.

**Step 1 (transformation rules).** Write `J(v)` for the set of `j <= kappa(v)` at
which `v` is `j`-windowed.
- *Lamps.* For `b` in `B`, commutativity of `B` gives `kappa(bv) = kappa(v)` and
  `I(bv) = I(v)`, so `J(bv) = J(v)`.
- *Scalars.* The same holds for a scalar `lambda` in `k^*`: `J(lambda v) = J(v)`.
- *Shift.* Conjugation by `t^n` is an automorphism of `k[B]`. It carries `B_(>=m)`
  to `B_(>=m+n)` and the window `[j,kappa)` to `[j+n, kappa+n)`. So
  `kappa(t^n v) = kappa(v) + n`, `I(t^n v) = t^n I(v) t^-n`, and
  `J(t^n v) = J(v) + n`.

**Step 2 (the invariant).** Suppose `kappa(v)` is finite and `J(v)` is nonempty.
- `J(v)` lies in `(-inf, kappa(v)]` by definition and is downward closed.
- So `j(v) = max J(v)` is an integer.
- `delta(v) = kappa(v) - j(v) >= 0` is constant on `k^* x R`-orbits, by step 1.

**Lemma A (a fixed lamp caps `j`).** Let `w != 0` have finite `kappa = kappa(w)`,
and let `1 != b` in `L_q` with `q < kappa` fix `w`. Then `j <= q` for every `j`
in `J(w)`.

*Proof.* Take `q < j <= kappa` and split at `j` as in step 0.
- `b - 1` lies in `I(w)` and equals `(b - 1) (x) 1`, with `b - 1 != 0` in
  `k[B_(<j)]`.
- If `j` were in `J(w)`, step 0 would put `1` in `I(w)`, so `w = 0`, which is a
  contradiction. `QED`

**Step 3 (the construction).** Fix `v` as in the theorem. Put `kappa = kappa(v)`,
`j = j(v)`, `I = I(v)` and `I_j = I cap k[B_([j,kappa))]`, so that
`I = k[B_(<j)] (x) I_j` by step 0.

Fix `m >= 1` and put `q = j - 1 - m`, so `q <= j - 2`. Pick `1 != b` in `L_q`, let
`N = sum_(0 <= i < ord(b)) b^i`, and put `w = N v`.

(a) *`w != 0`.* `N = N (x) 1` in the splitting at `j`, and `N != 0`. If `N` were
in `I`, step 0 would give `1` in `I_j`, so `v = 0`.

(b) *`kappa(w) = kappa`.*
- `B_(>=kappa)` fixes `v` and commutes with `N`, so `kappa(w) <= kappa`.
- `B_(>=kappa-1) = L_(kappa-1) x B_(>=kappa)` does not fix `v`, so some `g` in
  `L_(kappa-1)` has `gv != v`, that is, `g - 1` is not in `I`. It remains to show
  that `(g - 1)N` is not in `I`.
  - *If `j <= kappa - 1`:* `g` lies in `B_([j,kappa))` and
    `(g - 1)N = N (x) (g - 1)`. By step 0, membership in `I` would put `g - 1` in
    `I_j`, which is contained in `I`. That is a contradiction.
  - *If `j = kappa`:* the window is empty and `1` is not in `I`, so `I_j = 0` and
    `I = 0`. Also `(g - 1)N` is nonzero. The lamps `g` and `b` lie in the distinct
    factors `L_(kappa-1)` and `L_q`, where `q <= kappa - 2`, so
    `(g - 1)N = (g - 1) (x) N` in `k[L_(kappa-1)] (x) k[L_q]`, and both factors
    are nonzero.
- In particular `A_w = A_v`.

(c) *`j(w) <= q`.* `bN = N`, so `b` fixes `w`, and `q < kappa`. Apply Lemma A.

(d) *`q` is in `J(w)`.* Split at `q` with `W = B_([q,kappa))`, and put
`I_W = I cap k[W]`.
- Because `I_j` lies in `I_W`, we get `I = A.I_j <= A.I_W <= I`. So
  `I = k[B_(<q)] (x) I_W`.
- Now `I(w) = { a : aN in I }`, and `N` lies in `k[W]` since `q` is in `[q,kappa)`.
  Write `a = sum_beta beta (x) a_beta`. Then `aN = sum_beta beta (x) a_beta N`.
- By step 0, `aN` lies in `I` iff every `a_beta N` lies in `I_W`. So
  `I(w) = k[B_(<q)] (x) (I_W : N)`, where `(I_W : N) = { y in k[W] : yN in I_W }`,
  and this colon ideal equals `I(w) cap k[W]`.
- So `I(w) = A_w . (I(w) cap k[B_([q,kappa))])`, and `q` is in `J(w)`.

By (b), (c) and (d), `j(w) = j - 1 - m` and
`delta(w) = kappa - j + 1 + m = delta(v) + 1 + m`.

**Step 4 (conclusion).** As `m` ranges over `m >= 1`, the vectors `w_m`, all
lying in `k[B]v`, take every value `delta >= delta(v) + 2`. By step 2, `delta`
is constant on `k^* x R`-orbits. So there are infinitely many orbits, already on
the cyclic submodule `k[R]v`. `QED`

## Proof of the corollary

Here `k` is finite of characteristic `p`, `L` is a `p`-group, and `V` is infinite,
simple, and has finitely many `R`-orbits.

**`V^B = 0`.**
- `V^B` is a submodule, because `B` is normal: `b(rv) = r(r^-1 b r)v`.
- If `V^B = V`, then `V` is a simple module over `k[R/B] = k[t, t^-1]`, a principal
  ideal domain. So `V` is `k[t,t^-1]/(f)` for some nonzero `f`. That is
  finite-dimensional over the finite field `k`, hence finite, which is a
  contradiction.

**`U_+` and `U_-` are submodules.**
- Each `V^(B_(>=n))` is `B`-stable, because `B` is abelian.
- `t V^(B_(>=n)) = V^(B_(>=n+1))`.
- The union over `n` is increasing, since `B_(>=n)` shrinks as `n` grows, and it is
  stable under `t^(+-1)`.
- The same holds for `U_-`.

So each of `U_+` and `U_-` is `0` or `V`.

**They are not both `V`.**
- Suppose they are, and fix `v != 0`. Then `v` is fixed by some `B_(>=n)` and some
  `B_(<n')`, with `n' <= n` since `V^B = 0`.
- So `X = k[B]v = k[B_([n',n))]v` is finite and nonzero. `B_(>=n)` and `B_(<n')`
  act trivially on it, since they commute with `B` and fix `v`.
- The finite `p`-group `B_([n',n))` fixes a nonzero vector of `X`: orbit sizes are
  powers of `p`, so the number of fixed points is `|X| = 0 mod p`, and `0` is one
  of them.
- That vector is fixed by all of `B`, which contradicts `V^B = 0`.

**No nonzero vector is windowed.** If `U_+ != 0`, then `U_+ = V`, and
`V^B = 0` makes `kappa` finite on `V \ 0`. The theorem then rules out a windowed
vector. `QED`

**Reduction of every rank-one group to this case.** Let `R'` be finitely
generated with an elementary abelian normal `p`-subgroup `B'` such that
`R'/B' = <t>` is infinite cyclic.
- **The group.** `B'` is a finitely generated `F_p[t^(+-1)]`-module. It is the
  `R'`-normal closure of finitely many elements, and it is abelian. Over this
  principal ideal domain, `B' = F (+) F_p[t^(+-1)]^r`, where the torsion
  submodule `F` is finite and characteristic in `B'`, hence normal in `R'`.
- **The module.** Let `V` be a simple `F_p[R']`-module.
  - Any `v` spans a finite `k[F]v`, which contains a nonzero `F`-fixed vector.
  - So `V^F` is a nonzero submodule, hence all of `V`.
- **Conclusion.** `V` is a simple module over
  `R'/F = F_p[t^(+-1)]^r x| Z = C_p^r wr Z`, and the corollary applies with
  `L = C_p^r`.
  - The extension splits because `Z` is free.
  - `t` acts on the free module `B'/F` as multiplication by `t`.
  - If `r = 0`, then `R'` is virtually cyclic, and Cornulier's Proposition 3.20
    already applies.

## Consistency check: the local-field model

`research/artifacts/commuting-conjugate-coset-switch-2026-09-16.md`, section 5
("a local-field model (proved here)"), has an infinite simple module with no
base-fixed vector:
- the acting group is `R = C_p wr Z = F_p[t,t^-1] x| <t>`;
- the module is `V = C_c^infty(F_p((t)), F_p)`.

**The model's vector is windowed.** Here `L_i = F_p t^i`, and `B_(>=0) = F_p[t]`
fixes `1_O`, while `t^-1` does not, so `kappa(1_O) = 0`. The translates `b + O`,
for `b` in `B_(<0) = t^-1 F_p[t^-1]`, are pairwise disjoint balls, so their
indicators are independent. Hence `I(1_O) = 0`, and `1_O` is `0`-windowed.

**So the theorem applies to the model.** It reproves that the model has
infinitely many orbits, independently of the diam/resolution invariant there.
The witnesses are `w_m = N_(t^(-1-m)) 1_O = 1_(F_p t^(-1-m) + O)`, with
`kappa = 0` and `j = -1-m`. So the only known infinite simple module over a
lamplighter with `V^B = 0` has the type the theorem excludes. A counterexample
to the rank-one question must be of type (ii) or (iii) above.

## Why it matters

Cornulier, arXiv:math/0509090v2, verbatim:
- **Proposition 3.23.** "The following are equivalent. (1) There exists a
  finitely generated n-solvable group without Property (BF). (2) ... without
  Property (LBF). (3) There exists a finitely generated (n − 1)-solvable group Γ,
  and an infinite Γ-module V, such that the action of Γ on V has finitely many
  orbits."
- **On the open range.** "For n ≥ 3, we leave as open whether the equivalent
  statements of Proposition 3.23 are true. For n ≤ 2, they are false as a
  consequence of Proposition 3.20."
- **Question 3.24.** "1) Does there exist a finitely generated, solvable group
  without Property (LBF)? ..."

Those quotations, and the other Cornulier quotations in this node, are copied
verbatim from the arXiv v2 text, read this session.

Two lanes need the class-three case of statement (3):
- **The swarm's A_p^2 A refinement.** In the artifact above (section 5, steps
  1--7), a finite-rank infinite transitive action of a KMS-type ambient needs:
  - a finitely generated metabelian `R`;
  - an elementary abelian normal `p`-subgroup `B` with `R/B` abelian;
  - an infinite simple `F_p[R]`-module with `V^B = 0` and finitely many orbits.
- **Affine type (A) actors of class three.** These go through
  `orbit-finite-affine-actions-are-type-a`.

**What this node settles.** It is the first genuinely class-three case: `R/B`
infinite cyclic, with the module in the characteristic of `B`. It gives this
case a precise decomposition, whose parts are independent:
1. **Killed here.** Some vector is fixed by a half-line and has a windowed
   annihilator. This covers every vector with a finitely generated annihilator,
   every permutation-module-like vector (annihilator `0`), and the local-field
   model.
2. **Open.** One-sided modules, `U_+ = V`, all of whose annihilators are
   generated in no finite window.
3. **Open.** Modules with no nonzero vector fixed by any half-line.
4. **Open, outside this node.** `R/B` of torsion-free rank `>= 2`, as for
   `F_p[x^(+-1), (1+x)^-1] x| Z^2`; and modules in a characteristic other than
   that of `B`. The theorem holds in any characteristic, but the trichotomy uses
   the `p`-group fixed-point count.

**What it does not do.** `L wr Z` is not finitely presented, so this gives no type
(A) actor and kills none directly. It narrows only the group-theoretic source
that the KMS refinement would need.

## Attempts

1. **Type (ii) by maximal stabilizers (2026-09-19, swarm-0917-w14-w14-bh-break).
   Stalls.**
   - **Proved reduction.** Assume `U_+ = V` and put
     `K_0 = V^(B_(>=0)) \ V^(B_(>=-1))`. By step 1, `kappa` shifts by `n` under
     `t^n` and is `B`-invariant. So `R`-orbits on `V \ 0` correspond bijectively
     to `B`-orbits on `K_0`, and orbit-finiteness means `K_0` has finitely many
     `B_(<0)`-orbits.
   - **Consequences.** There are finitely many stabilizers `H_1, ..., H_N`. By
     the fixed-point count of the corollary, together with `U_- = 0`, every one
     of these orbits is infinite.
   - **The idea.** Take `v` in `K_0` with a maximal stabilizer, and use the socle
     trick to enlarge it. For a finite `E <= B_(<-1)`, some `y` in `k[E]` makes
     `yv != 0` and `E`-fixed, with `B_(yv) >= B_v + E`. If `yv` stayed in `K_0`,
     maximality would give `B_(<-1) <= B_v`. Then `v` would lie in `U_-`, which
     is a contradiction.
   - **Where it dies.** `yv` can drop out of `K_0`: an `E`-fixed vector may be
     forced to be `L_(-1)`-fixed. In the cyclic module `k[E x L_(-1)]/(e - l)`,
     with `E = L_(-1) = C_p`, the `E`-fixed and `L_(-1)`-fixed vectors coincide.
     Normalizing by `t^(kappa)` then shifts the stabilizer by an uncontrolled
     amount.
   - **What the windowed hypothesis buys.** It is exactly what makes the norm
     `N_b` preserve `kappa` in step 3(b). Without it, only the lower bound
     `kappa(yv) <= 0` survives.
2. **Type (iii).** Not attacked beyond the trichotomy. The candidate invariant is
   the family of stabilizers `B_v`. It falls into finitely many shift classes,
   each proper and each containing finite subgroups of every size (step 7 of the
   artifact's refinement). No shift-normalization analogous to `kappa` is known,
   so the socle trick produces no contradiction.

