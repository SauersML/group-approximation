# Compressor conjugation of root pairs, and why scalar rank data cannot bridge the gate

Lane `gk-gate-compress` (family R), 2026-09-12. Supports
`compressors-conjugate-leak-free-root-pairs` and
`scalar-two-root-rank-data-cannot-force-the-identity`, and adds Attempts material to
`rank-models-of-el3-satisfy-the-two-root-identities`. It uses
`research/artifacts/el3-rank-ring-rigidity-2026-09-12.md` ([RR], Lemma 13).

Notation. `R = L_(F_2)(1,2)`. `EL_3(R) = GL_3(R)` acts on column vectors in `R^3`,
`e_i r` the `i`-th coordinate. `x_ab(a) = 1 + a E_ab`. `e_0 = s_0 t_0`, `e_1 = s_1 t_1`,
`s_w`, `t_w` the usual words; the adjoint of `s_1 s_0` is `T[10] = t_0 t_1`, so `T[10] s_1 s_0 = 1`.
(Corrected after `gk-vf-linear`'s Section 48: the first landing wrote `t_1 t_0` where `T[10]` is
meant, and read one leak entry of `c'` literally. See the correction note at the end of Section 1.)
For a rank model `sigma` in characteristic two put
`n_ab(a) = sigma(x_ab(a)) - 1` and

```text
delta(a, b) = rk( n_23(b) n_12(a) ) .
```

The gate is `delta(1,1) = 0`. By the defect factorization of
`el3-two-root-violation-splits-over-leavitt-branches`,
`delta(a,b) = rk( n_13(ab) - n_12(a) n_23(b) )`.

## 1. Two explicit compressors and their leak-free root pairs

Fix the isomorphism `psi : R -> R^3`, `psi(r) = (t_0 r, t_0 t_1 r, t_1 t_1 r)`, with inverse
`(x, y, z) -> s_0 x + s_1 s_0 y + s_1 s_1 z`. (Check: `t_0 s_0 = t_0 t_1 s_1 s_0 = t_1 t_1 s_1 s_1 = 1`,
the cross terms vanish, and `s_0 t_0 + s_1 s_0 t_0 t_1 + s_1 s_1 t_1 t_1 = s_0 t_0 + s_1 t_1 = 1`.)

**The compressor `c` on coordinates `{1,2}`.** This is [RR] Lemma 13 with the complement
made explicit:

```text
c(e_1 r) = e_1 s_0 r ,   c(e_2 r) = e_2 s_0 r ,
c(e_3 r) = e_1 s_1 t_0 r + e_2 s_1 t_0 t_1 r + e_3 t_1 t_1 r .
```

Its image is `e_1 s_0 R + e_2 s_0 R + (e_1 s_1 R + e_2 s_1 R + e_3 R)`, which is all of `R^3`, and
`c` is injective, so `c` is a unit.

**The compressor `c'` on coordinates `{2,3}`.** With the reordered isomorphism
`v -> (t_1 t_1 v, t_0 v, t_0 t_1 v)`, inverse `(x, y, z) -> s_1 s_1 x + s_0 y + s_1 s_0 z`:

```text
c'(e_2 r) = e_2 s_0 r ,   c'(e_3 r) = e_3 s_0 r ,
c'(e_1 v) = e_1 t_1 t_1 v + e_2 s_1 t_0 v + e_3 s_1 t_0 t_1 v .
```

It is a unit for the same reason.

**Lemma 1 (conjugation formulas).** For all `a, b` in `R`:

```text
c  x_12(a) c^-1  = x_12(s_0 a t_0) ,
c  x_23(b) c^-1  = 1 + E_2(b),   E_2(b) has only row 2 nonzero, with entries
                   (s_0 b s_0 t_1 ,  s_0 b s_1 s_0 t_1 ,  s_0 b s_1 s_1) ;
c' x_23(b) c'^-1 = x_23(s_0 b t_0) ,
c' x_12(a) c'^-1 = 1 + F_2(a),   F_2(a) has only column 2 nonzero, with entries
                   (t_1 t_1 a t_0 ,  s_1 t_0 a t_0 ,  s_1 t_0 t_1 a t_0) .
```

*Proof.* `g x g^-1` fixes `g(u)` exactly when `x` fixes `u`, and sends `g(u)` to `g(x u)`.
* `c x_23(b) c^-1 - 1` vanishes on `c(e_1 R) + c(e_2 R)` and sends `c(e_3 r)` to
  `c(e_2 b r) = e_2 s_0 b r`. Writing `e_1 v = e_1 s_0 t_0 v + e_1 s_1 t_1 v`, the vector
  `e_1 s_1 t_1 v` is `c(e_3 s_0 t_1 v)`, since `psi(s_0 t_1 v) = (t_1 v, 0, 0)`. So the `(2,1)`
  entry is `s_0 b s_0 t_1`. Likewise `e_2 s_1 t_1 v = c(e_3 s_1 s_0 t_1 v)` gives
  `s_0 b s_1 s_0 t_1`, and `e_3 v = c(e_3 s_1 s_1 v)` gives `s_0 b s_1 s_1`.
* `c x_12(a) c^-1` is [RR] Lemma 13; on `c(e_3 R)` both sides are the identity because
  `s_0 a t_0 s_1 = 0`.
* `c' x_23(b) c'^-1 - 1` vanishes on `c'(e_1 R) + c'(e_2 R)` and sends `e_3 s_0 r = c'(e_3 r)` to
  `c'(e_2 b r) = e_2 s_0 b r`. Since `e_3 s_1 R` lies in `c'(e_1 R)`, the column-3 entry is
  `s_0 b t_0`.
* `c' x_12(a) c'^-1 - 1` vanishes on `c'(e_1 R) + c'(e_3 R)` and sends `e_2 s_0 t_0 v = c'(e_2 t_0 v)`
  to `c'(e_1 a t_0 v)`, whose coordinates are the three listed entries. QED

**Lemma 2 (leak-free root pairs).** Put `e_11 = s_1 s_1 t_1 t_1`.
* `c x_23(b) c^-1` is a root element iff `b s_0 = 0` and `b s_1 s_0 = 0`, iff `b` lies in
  `R t_1 t_1`. Then, for `b = b' t_1 t_1`, it equals `x_23(s_0 b')`.
* `c' x_12(a) c'^-1` is a root element iff `t_0 a = 0` and `t_0 t_1 a = 0`, iff `a` lies in
  `s_1 s_1 R`. Then, for `a = s_1 s_1 a''`, it equals `x_12(a'' t_0)`.

*Proof.* First bullet: the conjugate is a root element iff the `(2,1)` and `(2,2)` entries vanish.
`s_0 b s_0 t_1 = 0` iff `b s_0 t_1 = 0` (cancel `s_0` on the left by `t_0`) iff `b s_0 = 0`
(multiply by `s_1` on the right). Similarly `s_0 b s_1 s_0 t_1 = 0` iff `b s_1 s_0 = 0`. If both
hold, `b = b (s_0 t_0 + s_1 t_1) = b s_1 t_1 = b s_1 (s_0 t_0 + s_1 t_1) t_1 = b e_11`, so `b` lies in
`R t_1 t_1`; the converse is direct. The surviving entry is `s_0 b' t_1 t_1 s_1 s_1 = s_0 b'`.
Second bullet: the entries `s_1 t_0 a t_0` and `s_1 t_0 t_1 a t_0` vanish iff `t_0 a t_0 = 0` and
`t_0 t_1 a t_0 = 0` (cancel `s_1` by `t_1`), iff `t_0 a = 0` and `t_0 t_1 a = 0` (multiply by `s_0` on
the right). Then `a = s_1 t_1 a` and `t_1 a = s_1 t_1 t_1 a`, so `a = s_1 s_1 t_1 t_1 a` lies in
`s_1 s_1 R`; conversely `t_0 s_1 = 0` gives both vanishings. The surviving entry is
`t_1 t_1 s_1 s_1 a'' t_0 = a'' t_0`. QED

**Corollary 3 (simultaneous conjugacy).** For all `a, a', b, b'` in `R`:

```text
(x_12(a),       x_23(b' t_1 t_1))   ~   (x_12(s_0 a t_0),  x_23(s_0 b'))       via c ,
(x_12(s_1 s_1 a''), x_23(b))        ~   (x_12(a'' t_0),    x_23(s_0 b t_0))    via c' .
```

So in every characteristic-two rank model

```text
delta(a, b' t_1 t_1) = delta(s_0 a t_0, s_0 b') ,     delta(s_1 s_1 a'', b) = delta(a'' t_0, s_0 b t_0) .
```

*Consistency check.* Conjugation is a homomorphism, so the commutators must match.
* Via `c`: `[x_12(s_0 a t_0), x_23(s_0 b')] = x_13(s_0 a b')`, and by the same computation as
  Lemma 1, `c x_13(beta) c^-1 - 1` has row 1 equal to `(s_0 beta s_0 t_1, s_0 beta s_1 s_0 t_1, s_0 beta s_1 s_1)`.
  For `beta = a b' t_1 t_1` the first two entries vanish and the third is `s_0 a b'`.
* Via `c'`: `[x_12(a'' t_0), x_23(s_0 b t_0)] = x_13(a'' b t_0)`, and `c' x_13(beta) c'^-1 - 1`
  has column 3 equal to `(t_1 t_1 beta t_0, s_1 t_0 beta t_0, s_1 t_0 t_1 beta t_0)`, which for
  `beta = s_1 s_1 a'' b` is `(a'' b t_0, 0, 0)`.

*Correction note (gk-gate-compress, after `gk-vf-linear` Section 48).* The first landing stated the
`c'` half with leak-free set `s_1 R` and `delta(s_1 a', b) = delta(t_1 a' t_0, s_0 b t_0)`. That is
false: for `a = s_1`, `c' x_12(s_1) c'^-1 - 1` has entry `(3,2)` equal to `s_1 t_0 t_0 != 0`, a leak
into the `32` root. The error was reading the third leak entry literally as `s_1 t_1 t_0 a t_0`
instead of `s_1 T[10] a t_0 = s_1 t_0 t_1 a t_0`. The `c` half was computed with the adjoint reading
and was correct. The corrected `c'` half above mirrors the `c` half (`R t_1 t_1` versus `s_1 s_1 R`).
Nothing downstream consumed the false half; Section 2 needs only that both moves need and produce
non-units, which holds for the corrected form.

## 2. Where the compressor bridge fails

**Unit moves.** For units `g_1, g_2, g_3` of `R`, `diag(g_1, g_2, g_3)` conjugates
`(x_12(a), x_23(b))` to `(x_12(g_1 a g_2^-1), x_23(g_2 b g_3^-1))`. So
`delta(a, b) = delta(g_1 a g_2^-1, g_2 b g_3^-1)`, and `delta(u, v) = delta(1,1)` for all units `u, v`.

**Lemma 4 (the compressor moves never meet the unit pair).** Call the moves of Corollary 3 and the
unit moves *elementary*. Under elementary moves the pair `(1,1)` is equivalent only to pairs of
units.

*Proof.* Unit moves send units to units.
* **`c` needs a non-unit input.** It applies to `b = b' t_1 t_1`. Such a `b` satisfies
  `b s_0 = 0`, so it is not a unit.
* **`c` produces non-units.** Its outputs are `s_0 a t_0`, killed on the right by `s_1`, and
  `s_0 b'`, killed on the left by `t_1`.
* **`c'` is the same.** It applies to `a = s_1 s_1 a''`, which satisfies `t_0 a = 0`. Its outputs
  `a'' t_0` and `s_0 b t_0` are both killed on the right by `s_1`.

So no chain of elementary moves starting from a unit pair can use a compressor move. QED

**Subadditivity.** Root subgroups are abelian and `n^2 = 0` in characteristic two, so
`n_12(a + a') = X + X' + X X'` with `X = n_12(a)`, `X' = n_12(a')` commuting. Hence, with `Y = n_23(b)`,

```text
Y n_12(a+a') = Y X (1 + X') + Y X' ,          so  delta(a + a', b) <= delta(a, b) + delta(a', b) ,
n_23(b+b') X = Y X + (1 + Y) n_23(b') X ,      so  delta(a, b + b') <= delta(a, b) + delta(a, b') .
```

The Cuntz relation `1 = e_0 + e_1` therefore gives only upper bounds such as
`delta(1,1) <= delta(e_0, 1) + delta(e_1, 1) = 2 delta(e_0, 1)`. Here a unit swapping `e_0` and `e_1`
gives the last equality.

**Proposition 5 (scalar calibration).** Let `Delta : R x R -> [0,1]` satisfy:
* (i) `Delta(a,b) = Delta(a',b')` whenever some `g` in `GL_3(R)` conjugates `(x_12(a), x_23(b))` to
  `(x_12(a'), x_23(b'))`;
* (ii) subadditivity in each argument;
* (iii) `Delta(0,b) = Delta(a,0) = 0`.

Then `Delta_eps(a,b) = eps [a != 0][b != 0]` satisfies (i)–(iii) for every `eps` in `[0,1]`. So
`Delta(1,1) = 0` does not follow from (i)–(iii).

*Proof.* Conjugation sends a nontrivial root element to a nontrivial one, which gives (i). If
`a + a' != 0` then `a != 0` or `a' != 0`, which gives (ii), and similarly in `b`. (iii) is immediate.
QED

**Consequence.** The moves of Section 1, unit invariance, Weyl symmetry, and the Cuntz decomposition
of the root elements all produce relations of type (i)–(iii) among delta-values. None of them can
bridge `delta(1,1)` to the isometry-coefficient values `delta(t_i, s_i)`, or force `delta(1,1) = 0`.
Compressor conjugacies preserve rank, so compression never shrinks a size. A contraction needs a
**lower** bound, superadditivity of `delta` over an orthogonal decomposition, which is exactly the
orthogonality that block (matrix-unit) models have and free-type models lack. A proof of the gate
must use operator identities beyond scalar rank data. Examples:
* the joint isometry commutator relations of `leavitt-isometry-commutators-constrain-el3-rank-models`;
* the operator-level defect factorization;
* an additive size conserved on invariant subspaces.

This agrees with the landed calibrations `finite-subgroup-rank-data-cannot-force-two-root-identity`,
`sofic-subgroups-carry-rank-models-violating-two-root-identity` and
`dyadic-root-displacement-data-admit-trivial-plus-free-models`.
