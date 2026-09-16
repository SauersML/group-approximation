# Frobenius spectra and holonomy for Kazhdan SL_2 root triangles (2026-09-16)

Supporting artifact for:
- `sl2-root-triangle-char2-frobenius-spectrum-transport`, abbreviated FST;
- `sl2-root-triangle-2dim-iff-zero-frobenius-holonomy`, abbreviated HOL;
- `sl2-root-triangle-tensor-vertex-reps-force-2hol-zero`, abbreviated TVR (section 5a);
- `sl2-root-triangle-tensor-reps-iff-zero-holonomy`, abbreviated TRI (section 5b).

All four serve the open hole `sl2-root-kazhdan-triangle-without-finite-quotients`. The routes of FST, HOL,
TVR and TRI contain complete proofs. This file records:
- worked examples that calibrate the definitions;
- the computation and its outputs;
- a sharper open sub-question (Steinberg gluing);
- the literature check.

## 1. Setup recap

`q = 2^f >= 8`, `k = F_q ⊂ F = F_{q^2}`, `s ∈ F \ k`. The vertices are:
- `A_1 = SL_2(k)`, with `E_12 ↦ u(k)` and `E_13 ↦ v(k)`;
- `A_2 = SL_2(k)`, with `E_12 ↦ u(k)` and `E_23 ↦ v(k)`;
- `A_3 = SL_2(F)`, with `E_13 ↦ u(k)` and `E_23 ↦ v(sk)`.

The gluings `α_i^e ∈ GL_f(F_2)` enter only through the relative twists `φ_e = α_j^e (α_i^e)^{-1}`. Changing
`α_i^e` and `α_j^e` by a common automorphism of `E_e` gives an isomorphic colimit. Write `ψ_e = φ_e^{-1}` and
`supp(ψ)` for the set of Frobenius exponents in its linearized polynomial.

## 2. Worked examples of the Frobenius expansion

The expansion `ρ(u(y)) = Π_a (1 + y^{2^a} X_a)` holds for any representation of `SL_2(k)` in characteristic 2.
- **Natural module `V`.** `u(y) = 1 + y E_12`, so `X_0 = E_12`, the other `X_a = 0`, and `S = {0}`.
- **Frobenius twist `V^{(c)}`.** `u(y^{2^c}) = 1 + y^{2^c} E_12`, so `S = {c}`.
- **Twisted tensor product `L(T) = ⊗_{c ∈ T} V^{(c)}`.**
  `⊗_{c ∈ T}(1 + y^{2^c} E_12) = Π_{c ∈ T}(1 + y^{2^c} N_c)`, where `N_c` is `E_12` in slot `c`. So `S = T`.
  - For `T = Z/f` this is the Steinberg module, of dimension `q`, with `S = Z/f`.
  - By Steinberg's tensor product theorem the `L(T)` are the irreducible modules. That fact is classical
    and is used here only as orientation, not in any proof.
- **Direct sums.** The `X_a` add blockwise, so `S(M ⊕ M') = S(M) ∪ S(M')`.
- **Non-split extensions.** Off-diagonal blocks of `X_a` can be nonzero even when the diagonal blocks
  vanish. So `S` need not be the union of the spectra of the composition factors. FST uses only the bound
  `|S| <= d(d-1)/2` and never a formula for `S`.

**Why the transport is exact for semilinear twists.** If `ψ(y) = c y^{2^b}`, then
`ρ(p(ψ(y))) = Π_a(1 + c^{2^a} y^{2^{a+b}} X_a)` is already a Frobenius product. By uniqueness,
`X'_{a+b} = c^{2^a} X_a` exactly, and not only modulo `𝔞^2`.

For a non-semilinear `ψ`, the linear coefficients mix, and exactly as described by the matrix
`[X'_c] = Σ_a c_{c-a}^{2^a} [X_a]`. That is where the support `supp(ψ)` enters.

**Why the holonomy is the only obstruction in dimension 2.** With `|S_i| = 1`, the spectrum is one point
per vertex. The transport shifts it by `-a_e` along each edge, and going around the triangle shifts it by
`-hol`. So a one-point set comes back to itself only if `hol = 0`. In the other direction, the explicit
configuration of HOL realizes every zero-holonomy semilinear gluing.

## 3. The explicit configuration, and why it is forced

For semilinear twists `φ_e(x) = λ_e x^{2^{a_e}}`, any 2-dimensional configuration has the form
`ρ_i = conj_{g_i} ∘ σ_i`. Here `σ_i` is a field embedding, by `sl2-root-triangle-2dim-reps-force-semilinear-gluing`,
Step 2, or independently by FST, since `S_i = {b_i}` means `X_{b_i}` is the only nonzero coefficient.

**Frobenius exponents.** The edge conditions force `b_1 - b_3 = a_13` and `b_2 - b_3 = a_23` (mod `f` on
`k`-points), and `b_1 - b_2 = a_12`. This is solvable iff `hol = 0`. HOL takes `b_3 = 0`.

**Scalars.**
- `g_3 = d_τ` absorbs `λ_13`.
- `g_1 = h` turns `v`-type into `u`-type on edge 13.
- `g_2 = h u(1/P) d_ω` is lower triangular. It keeps `v`-type on edge 23 and matches `u`-type with `g_1` on
  edge 12.
- The only real constraint is the scale on edge 23, and it is solved by `P^2 = μ_12/ν`.

## 4. Computation

The script is `experiments/sl2-root-triangle-frobenius-holonomy-2026-09-16/holonomy.py`: pure python3,
single-threaded, finite fields by log tables.
- `F_64` uses `x^6 + x + 1`; `F_256` uses `x^8 + x^4 + x^3 + x^2 + 1`.
- `s` is the primitive element, which is not in `k`.

### (A) Sufficiency check

For random `λ_e ∈ k^*`, random exponents with `a_13 = a_12 + a_23`, and random `α_i^e ∈ GL_f(F_2)`, the
script builds the configuration of HOL. It then checks `ρ_i(ι_i(x)) = ρ_j(ι_j(x))` for every `x ∈ k` and
every edge.

```text
python3 holonomy.py 3 80 11    (A) q=8:  80/80
python3 holonomy.py 4 40 3     (A) q=16: 40/40
```

### (B) Counts of relative-twist triples

```text
(B) q=8:  |GL_f(F_2)|^3 = 4741632,     semilinear triples = 9261,   zero holonomy = 3087,  nonzero holonomy semilinear = 6174
(B) q=16: |GL_f(F_2)|^3 = 8193540096000, semilinear triples = 216000, zero holonomy = 54000, nonzero holonomy semilinear = 162000
```

### (C) Calibration of necessity over `K = F_64`, `q = 8`

After a global conjugation we may take `g_3 = I`, since `PGL_2(F) = SL_2(F)` in characteristic 2, so
`ρ_3 = Frob^{b_3}`.
- The fixed-line conditions then force `g_1 e_2 ∈ <e_1>` and `g_2 e_2 ∈ <e_2>`.
- The script enumerates all `b_3 ∈ Z/6`, all `b_1, b_2 ∈ Z/3`, and all such `g_1, g_2 ∈ SL_2(F_64)`.
- It counts configurations satisfying all three edge conditions.

```text
(C) exponents (a12,a13,a23)=(1, 0, 2) holonomy=0: 6
(C) exponents (a12,a13,a23)=(0, 1, 0) holonomy=2: 0
(C) exponents (a12,a13,a23)=(0, 2, 2) holonomy=0: 6
(C) exponents (a12,a13,a23)=(2, 0, 0) holonomy=2: 0
(C) exponents (a12,a13,a23)=(0, 2, 2) holonomy=0: 6
(C) exponents (a12,a13,a23)=(2, 1, 0) holonomy=1: 0
(C) exponents (a12,a13,a23)=(0, 1, 1) holonomy=0: 6
(C) exponents (a12,a13,a23)=(2, 0, 1) holonomy=0: 6
(C) non-semilinear twist on E_12 only, identity elsewhere: 0
```

The count `6` matches the prediction: one configuration per `b_3 ∈ Z/6`, since the centralizer of
`ρ_3(A_3)` in `PGL_2` is trivial. The run takes about 17 s.

This part is a calibration only. The proofs of FST and HOL do not depend on it.

## 5. The next open sub-question: Steinberg gluing

For `f` prime, FST shows that a member with `H ≠ 0` has every spectrum equal to `Z/f`. That covers the
non-semilinear members and the semilinear members with `hol ≠ 0`. The smallest natural modules with
spectrum `Z/f` are Steinberg-type, of dimension `q`:
- `St = V ⊗ V^{(1)} ⊗ ... ⊗ V^{(f-1)}` at `A_1` and `A_2`;
- at `A_3 = SL_2(F)`, some `L(T)` with `T ⊆ Z/2f` meeting every residue class mod `f` exactly once.

**Question.** Does a nonzero-holonomy semilinear member (for `q = 8`: 6174 triples) have a nontrivial
`q`-dimensional representation whose vertex restrictions are Steinberg-type?

What is known:
- **Common tensor decompositions give nothing new.** Suppose the three vertex restrictions are
  factorwise, `⊗_c conj_{g_{i,c}} ∘ Frob^{c}`, for one common decomposition `M = ⊗_c W_c`. For semilinear
  twists the edge operators `X_a` are transported exactly (Section 2), and `N_c` acting in slot `c` is not
  equal to `N'_{c'}` acting in another slot. So the edge conditions force slot `c` at `A_1` to match slot
  `c - a_12` at `A_2`, and so on around the triangle, and the loop closes only if `hol = 0`.
- **Products of 2-dimensional representations give nothing new.** Any homomorphism `Λ -> SL_2(K)^f ⋊ S_f`
  lands in `SL_2(K)^f`, because `Λ` is generated by perfect vertex groups. Each coordinate is then a
  2-dimensional representation, trivial by HOL.
- **Different decompositions at different vertices are excluded when `2·hol ≠ 0`.** This is
  `sl2-root-triangle-tensor-vertex-reps-force-2hol-zero`, added later the same day; see section 5a. The
  bilinear-system count below was the earlier, inconclusive approach to the same question.
- **The expected dimension is negative.**
  - Fix `ρ_1 = St`. Then `ρ_2 = conj_{c_12 Q_12^{-1}} ∘ St` and `ρ_3 = conj_{St(w) c_13 Q_13^{-1}} ∘ L(T)`, where:
    - `Q_e` are explicit monomial matrices, absorbing the semilinear twist by a slot permutation and a torus
      element;
    - `c_12, c_13` range over the units of the 8-dimensional algebra `K[u(k)]` (the commutant of a regular
      `(Z/2)^f`-module).
  - The edge-23 condition asks a bilinear system of `64 - 8 = 56` equations in `(c_12^{-1}, c_13)` to have
    an invertible solution. The expected dimension is `14 - 56 < 0`.
  - Deciding solvability over `F̄_2` needs elimination (Gröbner bases), which is not available here.

## 5a. The commutant argument (answers section 5 when `2·hol ≠ 0`)

The elimination is unnecessary. Only the commutation pattern between the coefficient operators of different
edges matters.

**Three families of operators.** Put:
- `y_c = X^u_c` at `A_1`, which is `E_12` in slot `c` of `St`;
- `x_c = X^v_c` at `A_1`, which is `E_21` in slot `c`;
- `z_d = X^v_d` at `A_2`.

For semilinear twists the transport is exact, so every coefficient operator at `A_2` or `A_3` is a multiple of one
of the `x_c`, `y_c` or `z_d`.

**The commutation graph.** Its vertices are the `3f` operators, and its edges join non-commuting pairs:
- `y_c — x_c`, from the slot structure at `A_1`;
- `y_{d + a_12} — z_d`, from the pairing at `A_2`;
- `x_{d + a_13 - a_23} — z_d`, from the pairing at `A_3`.

When `hol = 0` it is `f` disjoint triangles `{y_c, x_c, z_{c - a_12}}`: one `M_2` per slot, containing three
root elements. When `hol ≠ 0` the triangles open up. For `f` prime it becomes one `3f`-cycle.

**Why the open cycle cannot be realized.**
- `z_d` commutes with every slot other than `c_1 = d + a_12` and `c_1 - hol`. It also commutes with `x_{c_1}` and
  `y_{c_1 - hol}`.
- So `z_d ∈ span{1, x_{c_1}} ⊗ span{1, y_{c_1 - hol}}`, a 4-dimensional commutative algebra, and square-zero
  kills the scalar.
- The next operator `z_{d + hol}` lives in slots `c_1 + hol` and `c_1`. Its `y_{c_1}`-part meets the `x_{c_1}`-part
  of `z_d`, and the commutator `[x_{c_1}, y_{c_1}] ⊗ A ⊗ B` is nonzero in three distinct slots.

**The case `2·hol = 0 ≠ hol`.** Here the slots `c_1 ± hol` coincide and the argument stops. Part (3) of
`tensor_gluing.py` exhibits the commuting pair `z = x_0 + y_2`, `z' = x_2 + y_0` for `f = 4`. It commutes because
`[E_21, E_12] = 1` in characteristic 2, so the two slot commutators cancel. For representations that are
twisted tensor modules at all three vertices, the exact commutator scalars close this case; see section 5b.

**Checks.**

```text
python3 tensor_gluing.py
(1) f=3 h=1: centralizer dimension 4; 1, x_c1, y_c2, x_c1*y_c2 lie in it: True; independent: True
(1) f=3 h=2, f=4 h=1, f=4 h=3: the same
(2) f=3,4,5, all h with 2h != 0: distinct nonzero entries of [P,Q] mod 2 = {b g', b d', d g', d d'}: True
(3) f=4 h=2: P = x_0 + y_2, Q = x_2 + y_0 commute mod 2: True; P y_0 != y_0 P: True; P x_2 != x_2 P: True
```

The full output is in `out-tensor-gluing.txt`.

**What remains for `q = 8`.** Nonzero-holonomy semilinear members have:
- no representation of dimension `< 4` (FST);
- no representation that is `L(T)` at `A_1` and slot-diagonal at `A_2, A_3` (TVR).

The remaining representations are those that are not twisted-tensor-irreducible at any vertex, or not
slot-diagonal. An example of a vertex module that is neither is the symmetric square `S^2 V`. There `u(t)` sends `xy ↦ xy + t x^2` and
`y^2 ↦ y^2 + t^2 x^2`, so `X_0` and `X_1` both map onto the line `K x^2`, and `X_0 X_1 = 0`. For these, exact transport still holds, but the
commutant argument needs the tensor model.

## 5b. Exact commutator scalars (TRI: the case `hol = f/2`)

Assume the representation is a twisted tensor module at all three vertices, with `T_3` injective mod `f`. Then
condition (P) of TVR sharpens to exact scalars:
- at `A_2`, `[X^u_e, X^v_e] = 1`;
- at `A_3`, `[X^u_e, X^{v(s·)}_e] = s^{2^{t_e}}`, with `t_e ∈ T_3` the lift of `e`.

Exact transport multiplies the operators only by scalars in `k^*`.

**The computation for `hol = h = f/2`.** The commutant step of TVR still gives
`z_d ∈ span{1, x_{c_1}} ⊗ span{1, y_{c_1 + h}}`.
- The `A_2` scalar kills the `x_{c_1} y_{c_1+h}` term and fixes `β ∈ k^*`.
- The `A_3` scalar fixes `γ = s^{2^{t}} · (k^*)`.
- Commutativity of `z_d` with `z_{d+h}` then says `s^{2^{t'}} / s^{2^{t}} ∈ k^*` with `t' - t ∈ {h, h + f}`.
- With `w = s^{2^t}` and `r = sqrt(q)`, that means `w^{r-1}` or `w^{rq-1}` lies in `k^*`. Both exponents are
  coprime to `q + 1`, so `w ∈ k`, contradicting `s ∉ k`.

**Why the scalar matters.** For `hol = 0` the corresponding equations sit inside one slot and are solvable:
`z = [[p, a], [b, p]]` with prescribed `a, b` and `p^2 = ab`. This matches the realized configuration of HOL composed with `L_F(T_3)`.
For `hol = f/2` the two slots of a pair exchange their roles, and the Frobenius power of `s` that moves
between them is not in `k`.

**Result (TRI).** For semilinear twists, a tensor-type representation exists iff `hol = 0`. For `q = 16` this
adds the 54,000 triples with `hol = 2` to the 108,000 with `hol ∈ {1, 3}` covered by TVR.

**Checks.**

```text
python3 scalar_pairing.py
(1) f=4,6,8,10,12: gcd(e(q-1), q^2-1) = q-1 for all four exponents: True
(2) f=4: |k| = 16; 7680 ratios tested, 0 lie in k
(3) [y_a, z] = B + D y_b: True
(3) [x_b, B x_a + G y_b] = G: True
(3) [B x_a + G y_b, B2 x_b + G2 y_a] = B G2 + G B2: True
```

The full output is in `out-scalar-pairing.txt`.

## 6. Literature check (2026-09-16)

- **WebSearch unavailable.** Two WebSearch calls were refused, because the session's budget was exhausted.
- **arXiv API queries.** Three queries through `export.arxiv.org/api/query`, sorted by submission date:
  - `all:"triangles of groups"` (20 newest). Only Artin-group, Coxeter and unrelated entries, the newest
    `2609.00273` (2026-08-31). Nothing on triangles of finite simple groups or their representations.
  - `abs:"hyperbolic" AND abs:"virtually torsion-free" AND abs:"finite quotient"`. 0 results.
  - `abs:"not residually finite" AND abs:"hyperbolic group"` (15 newest). No construction of a hyperbolic
    group without finite quotients. `2509.21566` (2025-09) proposes a probabilistic route to a non-sofic
    hyperbolic group, conditional on a cocycle-stability statement. That is gist level only; the paper was
    not read.

  No source was found that classifies the linear representations of `SL_2` root triangles by the gluing
  type. The gate is bounded and abstract-level, so absence is not evidence of novelty.
- **Classical facts used, standard, not re-fetched.**
  - Lucas's theorem mod 2.
  - Linearized-polynomial normal form of `F_2`-linear maps of `F_q`.
  - Simultaneous triangularization of commuting nilpotent matrices.
  - Steinberg's tensor product theorem (orientation only, unverified here).
  - Hua's identity, in `sl2-root-triangle-2dim-reps-force-semilinear-gluing`.
- **In-graph sources.**
  - `kazhdan-hyperbolic-sl2-root-triangles` (data, `(K1)`, `(K2)`);
  - `triangle-of-groups-half-girth-structure` (iv);
  - `sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2`;
  - `sl2-root-triangle-2dim-reps-force-semilinear-gluing`.
