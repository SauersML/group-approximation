# Titz--Witzel soficity through isolation and the Radu sublattice (2026-09-11)

Lane `titz-witzel-csp`.  Everything below is either read from the cited PDFs
(page numbers given) or proved here.  The randomized and level computations
are sanity checks, not proofs; the scripts and their raw output are
`titz-witzel-radu-projections.py`, `titz-witzel-radu-robust-lemma-check.py`
and `titz-witzel-radu-projections-output-2026-09-11.txt` in this directory.

## Sources read from the PDFs

* T. Titz Mite, S. Witzel, *Non-residually finite `C~_2`-lattices*,
  arXiv:2509.05054v2.
  * p. 9: Example 3.3 (Radu's BMW complex `S_R`, four vertices, `D_2`-action),
    Proposition 3.4(1) the presentation
    `<a,b,c,x,y,z | a^2,b^2,c^2,x^2,y^2,z^2, axax, ayay, azbz, bxbx, bycy, cxcz>`
    of the BMW group `Gamma_R`, the extension of `pi_1(S_R)` by `D_2`;
    3.4(2) irreducible and not residually finite.
  * p. 10: 3.4(3) "The element `xz` lies in the profinite closure of
    `A := <a,b,c>`"; 3.4(4) "At least one of the following elements is in the
    finite residual of `Gamma_R`: `[y(xz)^2y, xz]`, `[y(xz)^2y, xzb]`", with
    proof deferred to [Rad20, Proposition 5.4]; Lemma 3.5, "`(xz)^4` lies in
    the finite residual of `Gamma_R`", with the relations
    `delta a = b delta`, `delta b = a delta`, `delta c = c delta^(-1)` and
    `(*) y delta^2 y b = b y delta^(-2) y`; Remark 3.6 (`delta^(+-4)` are the
    shortest elements of the finite residual, via a representation of the
    index-8 derived subgroup into `SL_2(Q(sqrt(-15), sqrt(17)))`).
  * p. 12: Theorem 4.1, "`Gamma_1^2` does not have any finite index subgroups".
  * p. 15, proof of Theorem 4.1 Part 1: subdividing `S_R` along the diagonals
    gives a `C~_2`-GAB embedding in `Y_1^2` via
    `v00->v, v11->w, v10->u1, v01->u2, a->f4, b->f5, c->f6, x->f1, y->f2,
    z->f3, a'->e4, b'->e5, c'->e6, x'->e1, y'->e2, z'->e3, s_i->g_i`;
    "In particular, `pi_1(S_R)` embeds into `Gamma_1^2` by Lemma 2.2".
* Y. Cornulier, *A sofic group away from amenable groups*, arXiv:0906.3374
  (Math. Ann. 2011).
  * pp. 2--3: elementary sofic groups = the smallest class containing `{1}`
    and closed under subgroups, direct limits, marked limits of finitely
    generated groups, and extensions with amenable quotient;
    Question 5: "Is there any sofic group that is not elementary sofic?"
  * p. 3, Lemma 7 and Proposition 8: "Let `G` be a finitely presented group.
    Assume that `G` is not residually finite, and that for some finite normal
    subgroup `Z` of `G`, the group `G/Z` is hereditary just infinite (every
    proper quotient of any finite index subgroup, is finite).  Then `G` is
    isolated, and if moreover `G` is not amenable, then it is not elementary
    sofic."
  * p. 4: "... Burger-Mozes' groups [BM], which are amalgams of free groups.
    Accordingly, these groups are not elementary sofic; it is unknown if they
    are sofic."

## 1. The smallest Titz--Witzel kernel is isolated and not elementary sofic

Let `K = Gamma_1^2`.  It is finitely presented, infinite, simple and Kazhdan
(`titz-witzel-simple-kazhdan-cat0-lattices-exist`), and by Theorem 4.1 it has
no proper finite-index subgroup.  Take `Z = 1`: every finite-index subgroup of
`K` is `K`, and every proper quotient of `K` is trivial.  So `K` is hereditarily
just infinite, not residually finite, and not amenable.  Proposition 8 makes
`K` isolated and not elementary sofic.  The same holds for the index-two
overgroup `barGamma_1^2`: its finite-index subgroups are `K` and itself, and
its proper quotients are `C_2` or trivial.

Consequences.

* No finite composition of the four elementary permanence operations can
  produce a sofic approximation of `K`.  This turns the informal list in
  `titz-witzel-sofic-structure-audit-2026-08-26.md` into a theorem.
* `K` is isolated: it is not a nontrivial marked limit of groups, so a
  positive answer cannot come from approximating `K` by other marked groups.
* A proof that `K` is sofic gives an explicit finitely presented, torsion-free,
  simple, Kazhdan CAT(0) answer to Cornulier's Question 5, as well as
  Alekseev--Thom Open Problem 6.1 (already recorded in the goal node).

## 2. The Radu sublattice gate

`pi_1(S_R)` embeds in `K` and has index four in `Gamma_R`.  Soficity passes to
subgroups and to finite extensions, so

```text
K sofic  ==>  Gamma_R sofic,          Gamma_R nonsofic  ==>  K nonsofic.   (RS1)
```

Cornulier records the soficity of Burger--Mozes groups as unknown; `Gamma_R`
is a non-residually-finite irreducible lattice in the same class of
BMW groups.  The positive horn of the Titz--Witzel gate therefore contains
the soficity of an explicit non-residually-finite BMW lattice.

**Four-involution presentation.**  The relators `azbz` and `bycy` solve
`b = zaz` and `c = yby = yzazy` (all generators being involutions), after
which `b^2, c^2` are consequences and

```text
Gamma_R = <a,x,y,z | a^2, x^2, y^2, z^2, (ax)^2, (ay)^2, (zazx)^2,
                     yzazy x yzazy z>,          mark (xz)^4.            (RS2)
```

A sofic approximation of `Gamma_R` in particular separates `(xz)^4` from the
identity.

**Automaton form.**  Writing each square relation as `h v = v' h'` for a
horizontal letter `h` and a vertical letter `v` gives the complete table

```text
(h,v) -> (v',h'):  (a,x)->(x,a)  (a,y)->(y,a)  (a,z)->(z,b)
                   (b,x)->(x,b)  (b,y)->(y,c)  (b,z)->(z,a)
                   (c,x)->(z,c)  (c,y)->(y,b)  (c,z)->(x,c)        (RS3)
```

Inverting, `v h = h' v'`.  The vertical letters act on the horizontal tree
(reduced words in `a,b,c`) as transducers: `y` is the global substitution
`b<->c`; `x` outputs its input unchanged and switches to state `z` on reading
`c`; `z` swaps `a<->b` and switches to `x` on reading `c`.  The horizontal
letters act on reduced words in `x,y,z` as `a,b` (identity outputs) and `c`
(swap `x<->z`), with states updated by `z: a<->b`, `y: b<->c`.

## 3. Robust Lemma 3.5

**Theorem.**  Let `a,b,c,x,y,z` be involutions in a group with a bi-invariant
metric `d`.  Let `e1,...,e6` be the defects `d(w,1)` of
`axax, ayay, azbz, bxbx, bycy, cxcz`.  Put `delta = xz`, `u = y delta^2 y` and

```text
kappa1 = d(u delta, delta u),        kappa2 = d(u delta b, delta b u).
```

Then

```text
d(delta^4,1) <= 2 kappa1 + 3e1 + 2e2 + 4e3 + e4 + 2e5 + 4e6,           (RL1)
|kappa1 - kappa2| <= 3e1 + 2e2 + 4e3 + e4,                              (RL2)
d(delta^4,1) <= 2 kappa2 + 9e1 + 6e2 + 12e3 + 3e4 + 2e5 + 4e6.         (RL3)
```

*Proof.*  Bi-invariance gives `d(g,h) = d(1, g^(-1)h)`, invariance under
conjugation and inversion, and `d(g1 g2, h1 h2) <= d(g1,h1) + d(g2,h2)`.
Rotations of a relator are conjugates, so they have the same defect.

1. `d(za, bz) = e3` and `d(zb, az) = e3` (from `azbz` and its rotation
   `bzaz`); `d(xb, bx) = e4`, `d(xa, ax) = e1`, `d(ya, ay) = e2`;
   `d(yb, cy) = d(yc, by) = e5`; `d(xc, cz) = d(zc, cx) = e6`.
2. Hence `d(delta a, b delta) <= e3 + e4`, `d(delta b, a delta) <= e1 + e3`,
   `d(delta c, c delta^(-1)) <= 2e6`, `d(delta^2 c, c delta^(-2)) <= 4e6`,
   `d(delta^2 a, a delta^2) <= e1 + 2e3 + e4`.
3. `(*)`: `d(u b, b u^(-1)) <= eta := 2e5 + 4e6`, by conjugating step 2's
   `delta^2 c` estimate with `y` and using `yb ~ cy`, `yc ~ by`.
4. `d(au, ua) <= lambda := e1 + 2e2 + 2e3 + e4`, from `ay ~ ya` and step 2.
5. Conjugate `ub ~ bu^(-1)` by `delta`.  Using `delta u ~ u delta` and
   `delta u^(-1) ~ u^(-1) delta` (each `kappa1`) and `delta b ~ a delta`
   (twice `e1 + e3`), obtain `d(ua, a u^(-1)) <= eta + 2 kappa1 + 2e1 + 2e3`.
6. Then `d(delta^4,1) = d(u^2,1) = d(au, au^(-1)) <= d(au,ua) + d(ua,au^(-1))`,
   which gives `(RL1)`.
7. With `w = delta b` one has `d(delta, a w) = d(delta b, a delta) <= e1 + e3`.
   So `kappa1 <= d(u a w, a w u) + 2(e1+e3) <= lambda + kappa2 + 2e1 + 2e3`.
   The symmetric estimate gives `(RL2)`, and `(RL1)` then gives `(RL3)`.  []

In the exact case the two commutators of Proposition 3.4(4) vanish
together, and either one kills the mark.  The randomized check (2000 random
involution tuples on 8 to 128 points, half with `azbz` and `bycy` exact) found
no violation of `(RL1)--(RL2)`; the largest observed ratio of the mark to the
right side of `(RL1)` was `0.14`.

**Consequence.**  A marked approximate solution of `(RS2)` must keep the
single commutator `[y(xz)^2y, xz]` macroscopically nontrivial:
`limsup d_H([u,delta],1) >= limsup d_H((xz)^4,1)/2`.  Conversely the negative
horn at BMW level reduces to one commutator collapse: if
`d_H([y(xz)^2y, xz],1) -> 0` along every approximate solution, then
`(xz)^4` lies in the sofic radical of `Gamma_R` and both `Gamma_R` and `K` are
nonsofic.  In Radu's argument this collapse is supplied, for exact finite
quotients only, by the profinite statements 3.4(3)--(4); everything else in
Lemma 3.5 is robust.

## 4. The horizontal projection kills `delta^2`

`Gamma_R` acts simply transitively on the vertices of `T_h x T_v`.  The
stabilizer of the root of the horizontal tree `T_h` is `V = <x,y,z>`, and
`T_h` is `Gamma_R / V`, whose vertices are the reduced words in `a,b,c`.  By
`(RS3)`, the action of a vertical letter on a coset `hV` is its transducer
output.  On a reduced word `h_1...h_n`:

* `x` leaves the letters of the even `c`-blocks unchanged (before the first
  `c`, between the second and third, ...) and swaps `a<->b` in the odd blocks;
* `z` does the opposite.

Neither changes the positions of the letter `c`.  So `x` and `z` commute on
`T_h`, `delta = xz` acts there as the global substitution `a<->b`, and
`delta^2` acts trivially.  Thus

```text
delta^2 in Lambda_v := ker(Gamma_R -> Aut(T_h)).                        (HK1)
```

`Lambda_v` is a normal subgroup contained in `V = C_2*C_2*C_2`.  It contains no
conjugate of `x,y,z` (each acts nontrivially on `T_h`), so by Kurosh it is
torsion-free, hence free.  The mark `(xz)^4` lies in this free normal
subgroup.  In particular every almost action of `Gamma_R` obtained by pulling
back an action of the horizontal tree group `Gamma_R/Lambda_v` collapses the
mark, however rich that quotient's finite models are.

Computed level data (reduced words of length `n`, `sympy` orders for `n<=8`):

* `G_h = V/Lambda_v` on `T_h`: `|G_n| = 6, 48, 192, 1536, 12288, 98304,
  786432, 6291456`.  This is `6 * 8^(n-1) = |PGL_2(Z/2^n)|` for `n = 1, 2` and
  exactly half of it for `3 <= n <= 8`.  `xy` has order `2^n` at level `n`; the
  reduced words of length at most 10 trivial on level 10 include `(xz)^2` and
  `(xyz)^3`.  With `s = xz`, `u = xyx` one has `z = xs`, `y = xux`, `xyz = us`,
  so `<x,y,z | x^2,y^2,z^2,(xz)^2,(xyz)^3>` is the Coxeter group
  `<x,u,s | x^2,u^2,s^2,(xs)^2,(us)^3>`, which is `PGL_2(Z)`.  Hence `G_h` is a
  quotient of `PGL_2(Z)` as soon as `(xyz)^3` acts trivially on every level.
  `(xz)^2` is proved on all levels in `(HK1)` above; `(xyz)^3` is only verified
  through level 10.
* `G_v = A/Lambda_h` on `T_v`: `|G_n| = 2, 4, 16, 32, 64, 128, 512, 1024`;
  no reduced word of length at most 10 is trivial on level 10.

These are observations about tree quotients, not claims about the abstract
groups.

## 5. Where the gate now stands

* Positive horn.  Any construction must be non-elementary (Section 1).  It
  must keep `[y(xz)^2y, xz]` macroscopically nontrivial (Section 3) and must
  not factor through the horizontal tree quotient (Section 4).  It also
  contains soficity of `Gamma_R` (Section 2).
* Negative horn.  A robust version of Proposition 3.4(4), namely collapse of
  `[y(xz)^2y, xz]` along every approximate solution of the four-involution
  system, suffices.  It needs no property `(T)`.  The published proof of
  3.4(3)--(4) is [Rad20, Proposition 5.4] in the Titz Mite--Witzel
  bibliography and was not read for this artifact; it is the next source to
  read.
