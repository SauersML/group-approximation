# Constant-symbol pullbacks need at most one extra colour (2026-09-16)

Swarm artifact for `stw99-problem-lxxxiii-graph-nuclear-dimension`.  It holds
the full proofs behind

* `stw83-constant-symbol-pullback-one-extra-colour` (Theorem 1);
* `stw83-circle-ideal-cuntz-quotient-dimension-two-bound` (Corollary 5);
* the alternative route into `stw83-canonical-circle-toeplitz-dimension-two-bound`
  (Corollary 7);

together with the split-extension observation (Proposition 6) and the colour
count that shows where a dimension-one proof has to do more (Section 8).

## 0. Conventions and imported facts

`H` is a separable infinite-dimensional Hilbert space, `K=K(H)`, and
`q:B(H)->B(H)/K` is the Calkin map.  "cpc" means completely positive
contractive.  Nuclear dimension is as in Winter--Zacharias [WZ10, Definition
2.1]: `dim_nuc(A)<=m` if every finite set can be approximated through
`psi:A->L^(0)+...+L^(m)` (cpc) and `phi:L^(0)+...+L^(m)->A`, where each
`L^(k)` is finite dimensional and each `phi|L^(k)` is cpc order zero.

Imported facts, with where the statement was checked.

* (F1) Ideals, hereditary subalgebras and quotients do not raise nuclear
  dimension: [WZ10, Proposition 2.3] (quotients) and [WZ10, Proposition 2.5]
  (hereditary subalgebras).  The numbers were checked against citations in the
  TeX source of Evington, arXiv:2012.03650v3.  WZ10 itself was not fetched.
* (F2) `dim_nuc(C(X))=dim X` for compact metrizable `X`: [WZ10, Proposition
  2.4].  Checked against the citation in the ENSW TeX source,
  arXiv:2409.12872v2.
* (F3) Nuclear dimension is invariant under stable isomorphism: [WZ10,
  Corollary 2.8(i)].  Checked against the ENSW TeX source.  In particular
  `dim_nuc(M_R(C(X)))=dim_nuc(C(X) tensor K)=dim X`.
* (F4) Order-zero lifting [Wi09, Proposition 1.2.4].  Let `kappa:E->E/I` be a
  surjective *-homomorphism, `F` finite dimensional, and `eta:F->E/I` cpc order
  zero.  Then there is a cpc order-zero `hat(eta):F->E` with
  `kappa hat(eta)=eta`.  The statement was checked verbatim in the Evington TeX
  source, which cites Winter, *Covering dimension for nuclear C\*-algebras II*,
  Trans. AMS 361 (2009).  The underlying reason is projectivity of
  `C_0(0,1] tensor F` (Loring).
* (F5) Choi--Effros lifting.  A cpc map from a separable nuclear C\*-algebra
  into a quotient `D/K` lifts to a cpc map into `D`.  Finite nuclear dimension
  implies nuclearity (WZ10).
* (F6) A separable nuclear `O_infinity`-stable C\*-algebra has nuclear
  dimension one: Bosa--Gabe--Sims--White, arXiv:1906.02066, Theorem A.  This
  is as cited in the Evington TeX source; BGSW itself was not fetched here.
* (F7) `O_n tensor O_infinity` is isomorphic to `O_n` (Kirchberg's
  `O_infinity`-absorption for Kirchberg algebras).  Standard; not fetched,
  unverified.
* (F6') `dim_nuc(O_n)=1` for `n=2,3,...`: [WZ10, Theorem 7.4], checked by the
  referee on 2026-09-16 in the TeX source of arXiv:0903.4914v1 (the statement
  there reads "dim_nuc O_n = 1 for n=2,3,... and dim_nuc O_infinity <= 2").
  This replaces the chain (F6)+(F7) wherever only `dim_nuc(O_n)=1` is needed;
  the journal numbering was not checked.
* (F8) The gauge-invariant uniqueness theorem for finite graphs (an
  Huef--Raeburn; Bates--Pask--Raeburn--Szymanski).  Standard; the exact theorem
  number is not verified.
* (F9) Evington, arXiv:2012.03650v3, Theorem 1 (checked verbatim in the TeX
  source).  Let `0->J->A->B->0` be a full extension, `J` separable and stable,
  and `B` separable, nuclear and `O_infinity`-stable.  Then
  `1<=dim_nuc(A)<=dim_nuc(J)+1`.  The same source remarks that when `B` is
  simple, every unital extension is full.

Graph convention, as in ENSW: `s_e^*s_e=p_(r(e))`, `s_es_e^*<=p_(s(e))`, and
`p_w=sum_(s(e)=w) s_es_e^*` for every vertex that emits edges.  A set is
hereditary when it is closed forward along edges.

## 1. The theorem

Let `X` be a compact metrizable space with `n:=dim X<infinity`.  Let
`K subseteq D subseteq B(H)` be a separable C\*-algebra, and let `B:=D/K`
have `d:=dim_nuc(B)<infinity`.  Put

```text
A_X(D) := C(X,K) + D tensor 1   inside C(X,B(H))   (norm-continuous maps).
```

**Theorem 1.**  `max(n,d) <= dim_nuc(A_X(D)) <= max(n,d)+1.`

For comparison, the generic extension estimate [WZ10, Proposition 2.9] gives
only `n+d+1`.

`A:=A_X(D)` is a C\*-algebra, since it is the sum of a closed ideal `J:=C(X,K)`
of `C(X,B(H))` and a C\*-subalgebra.  The map

```text
pi:A->B,     pi(c + x tensor 1) = q(x)     (c in J, x in D)
```

is well defined: if `(x-x') tensor 1` lies in `C(X,K)`, then `x-x'` is in `K`.
It is a surjective *-homomorphism with kernel `J`.  So

```text
0 -> C(X,K) -> A_X(D) -> D/K -> 0.
```

**Lower bound.**  By (F1), (F2) and (F3),
`dim_nuc(A)>=dim_nuc(J)=dim_nuc(C(X) tensor K)=n` and `dim_nuc(A)>=dim_nuc(B)=d`.

The upper bound occupies Sections 2--4.

## 2. A nested finite-rank quasicentral approximate unit

**Lemma 2.**  There are finite-rank positive contractions `e_1,e_2,...` in `K`
and finite-rank projections `Q_1<=Q_2<=...` such that:

1. `Q_i e_i = e_i` and `e_(i+1) Q_i = Q_i`, hence `e_(i+1)e_i=e_i`;
2. `||e_i k - k|| -> 0` for every `k` in `K`;
3. `||[e_i,x]|| -> 0` for every `x` in `D`.

*Proof.*
1. *Weak convergence.*  Fix an orthonormal basis, and let `P_j` be the
   projection onto its first `j` vectors.  Let `x_1,x_2,...` be dense in `D`.
   For `x` in `B(H)`, `[P_j,x]` is compact with norm at most `2||x||`.  For
   every trace-class `T`, `Tr([P_j,x]T)=Tr(P_j xT)-Tr(P_j Tx)` tends to
   `Tr(xT)-Tr(Tx)=0`.  So `[P_j,x]->0` weakly in the Banach space `K`, whose
   dual is the trace class.
2. *Choice of `e_i`.*  Suppose `M_(i-1)` is chosen (`M_0:=1`), and put
   `m_i:=M_(i-1)+i`.  The tuples `([P_j,x_1],...,[P_j,x_i])` tend weakly to
   `0` in `K^i` as `j->infinity`.  By Mazur's lemma, `0` is in the norm closure
   of the convex hull of the tuples with `j>=m_i`.  So there is a finite
   convex combination `e_i=sum_(j=m_i)^(M_i) c_j P_j` with
   `||[e_i,x_l]||<1/i` for all `l<=i`.  Put `Q_i:=P_(M_i)`.
3. *Item 1.*  `Q_ie_i=e_i` is clear.  Every `j` used in `e_(i+1)` satisfies
   `j>=m_(i+1)>M_i`, so `P_jQ_i=Q_i` and hence `e_(i+1)Q_i=Q_i`.  Then
   `e_(i+1)e_i=e_(i+1)Q_ie_i=Q_ie_i=e_i`.
4. *Item 2.*  `e_iP_(m_i)=P_(m_i)` and `m_i->infinity`.  So
   `||e_ik-k|| <= ||e_i(1-P_(m_i))k|| + ||(1-P_(m_i))k|| <= 2||(1-P_(m_i))k||`,
   which tends to `0`.
5. *Item 3.*  Follows from density of the `x_l`.  QED.

**Consequences.**
* `e_i` and `e_(i+1)` commute (take adjoints in item 1), and so do `Q_i` and
  `e_(i+1)`.
* `e_(i+1)-e_i=Q_i(1-e_i)Q_i+(1-Q_i)e_(i+1)(1-Q_i)`, which is a positive
  contraction supported under `Q_(i+1)`.
* For continuous `f` on `[0,1]`, `f(e_(i+1))Q_i=f(1)Q_i`.  In particular
  `(1-e_(i+1))^(1/2)Q_i=0`.

Put `h_i:=e_i tensor 1` in `J`, and write `R_i:=rank Q_i`.

**Lemma 2'.**
1. `(h_i)` is an approximate unit for `J`.
2. `||[h_i,a]||->0` for every `a` in `A`.
3. If `t_i` are positive contractions with `||[t_i,a]||->0`, then
   `||[f(t_i),a]||->0` for every continuous `f` on `[0,1]`.

*Proof.*
1. For an elementary tensor `f tensor k`,
   `||h_i(f tensor k)-f tensor k|| = ||f|| ||e_ik-k||`.  Elementary tensors
   span a dense subspace of `C(X) tensor K=C(X,K)`, and the `h_i` are uniformly
   bounded.
2. Write `a=c+x tensor 1` with `c` in `J` and `x` in `D`.  Then
   `[h_i,c]=(h_ic-c)-(ch_i-c)`, which tends to `0` by item 1 applied to `c` and
   `c^*`.  Also `[h_i,x tensor 1]=[e_i,x] tensor 1`, which tends to `0` by
   Lemma 2(3).
3. Approximate `f` uniformly by polynomials.  QED.

## 3. The three-piece decomposition with constant band and outer piece

Fix a cpc lift `sigma:B->D` of `q|D` (F5), and put `mu(b):=sigma(b) tensor 1`,
which lies in `A`.  Define cpc maps

```text
alpha_i(a) = h_i^(1/2) a h_i^(1/2),
beta_i(b)  = (h_(i+1)-h_i)^(1/2) mu(b) (h_(i+1)-h_i)^(1/2),
gamma_i(b) = (1-h_(i+1))^(1/2) mu(b) (1-h_(i+1))^(1/2),
```

for `a` in `A` and `b` in `B`.  The unit is that of `C(X,B(H))`.

**Lemma 3.**
1. `alpha_i(A)` lies in `E_i:=C(X,Q_iB(H)Q_i)`.  `E_i` is a C\*-subalgebra of
   `J` isomorphic to `M_(R_i)(C(X))`.
2. `beta_i(B)` lies in `(Q_(i+1)B(H)Q_(i+1)) tensor 1`, a finite-dimensional
   C\*-subalgebra of `A` isomorphic to `M_(R_(i+1))`.
3. `gamma_i(B)` lies in `D tensor 1` and in
   `C_i:={y in A : y(Q_i tensor 1)=0=(Q_i tensor 1)y}`.  `C_i` is a hereditary
   C\*-subalgebra of `A`, and `C_iE_i=E_iC_i=0`.
4. For every `a` in `A`,
   `||a-alpha_i(a)-beta_i(pi(a))-gamma_i(pi(a))|| -> 0`.

*Proof.*
1. `h_i^(1/2)=e_i^(1/2) tensor 1` and `e_i^(1/2)=Q_ie_i^(1/2)Q_i`.  So
   `alpha_i(a)=(Q_i tensor 1)alpha_i(a)(Q_i tensor 1)`, a continuous function
   with values in `Q_iB(H)Q_i`, which is contained in `K`.
2. `beta_i(b)=((e_(i+1)-e_i)^(1/2)sigma(b)(e_(i+1)-e_i)^(1/2)) tensor 1`, and
   `e_(i+1)-e_i` is supported under `Q_(i+1)`.  This is the one place where the
   constant symbol matters: the band never leaves one fixed matrix algebra of
   constants.
3. *Values in `D`.*  `(1-e_(i+1))^(1/2)` lies in `C1+K`, so
   `gamma_i(b)=((1-e_(i+1))^(1/2)sigma(b)(1-e_(i+1))^(1/2)) tensor 1` has
   values in `D`.
   *Values in `C_i`.*  `(1-e_(i+1))^(1/2)Q_i=0` gives `gamma_i(b)` in `C_i`.
   *`C_i` is hereditary.*  It is a closed *-subalgebra.  If
   `0<=y<=z` with `z` in `C_i`, then
   `||y^(1/2)(Q_i tensor 1)||^2=||(Q_i tensor 1)y(Q_i tensor 1)|| <= ||(Q_i tensor 1)z(Q_i tensor 1)||=0`.
   *Orthogonality.*  Every element of `E_i` equals
   `(Q_i tensor 1)(.)(Q_i tensor 1)`.
4. By Lemma 2'(2,3), the commutators of `a` and of `mu(pi(a))` with `h_i`,
   `h_(i+1)-h_i`, `1-h_(i+1)` and with their square roots tend to `0`.  Hence,
   up to a norm error tending to `0`,

   ```text
   alpha_i(a)+beta_i(pi a)+gamma_i(pi a)
       ~ h_i a + (h_(i+1)-h_i) mu(pi a) + (1-h_(i+1)) mu(pi a)
       = a - (1-h_i)(a - mu(pi a)).
   ```

   Since `a-mu(pi(a))` lies in `J`, Lemma 2'(1) makes the last term tend to
   `0`.  QED.

## 4. Exact order-zero outer colours, and assembly

**Lemma 4.**  Let `F` be finite dimensional, `eta:F->B` cpc order zero, and
`hat(eta):F->D` a cpc order-zero lift (F4).  Put

```text
theta_i(y) := (1-h_(i+1))^(1/2) (hat(eta)(y) tensor 1) (1-h_(i+1))^(1/2),
```

a cpc map `F->C_i` (Lemma 3(3)).  Then there are cpc order-zero maps
`tilde(theta)_i:F->C_i` with `||tilde(theta)_i-theta_i||->0`.

*Proof.*
1. *A cpc map into the quotient.*  Let `P:=prod_i C_i` (bounded sequences),
   let `I:=sum_i C_i` (null sequences), and let `kappa:P->P/I` be the
   quotient map.  Then `Theta:=kappa((theta_i)_i):F->P/I` is cpc.
2. *`Theta` is order zero.*  Take orthogonal positive `y,y'` in `F`, and put
   `Y=hat(eta)(y) tensor 1`, `Y'=hat(eta)(y') tensor 1` and
   `t=(1-h_(i+1))^(1/2)`.  Then

   ```text
   || theta_i(y)theta_i(y') - t Y Y' t^3 || = || t Y [t^2 , Y'] t || <= ||[h_(i+1),Y']|| -> 0,
   ```

   and `YY'=(hat(eta)(y)hat(eta)(y')) tensor 1=0`.  So `Theta(y)Theta(y')=0`.
3. *Lift.*  By (F4) applied to `kappa`, there is a cpc order-zero
   `tilde(Theta)=(tilde(theta)_i)_i:F->P` with `kappa tilde(Theta)=Theta`.
   The coordinates `tilde(theta)_i:F->C_i` are cpc order zero, and
   `||tilde(theta)_i(y)-theta_i(y)||->0` for every `y`.  This convergence is
   uniform on the unit ball, because `F` is finite dimensional.  QED.

**Proof of the upper bound in Theorem 1.**  Put `m:=max(n,d)`, and fix a
finite set `S` of contractions in `A` and `eps>0`.

1. *Quotient approximation.*  Choose a cpc map
   `psi_B:B->F^(0)+...+F^(d)` and cpc order-zero maps `eta^(k):F^(k)->B` with
   `||sum_k eta^(k)psi_B^(k)(pi a)-pi a||<eps` for `a` in `S`.
2. *Lifts and compact defects.*  Lift each `eta^(k)` to a cpc order-zero
   `hat(eta)^(k):F^(k)->D` (F4).  Since `q` has quotient norm, for each `a` in
   `S` there is `k_a` in `K` with
   `||sum_k hat(eta)^(k)psi_B^(k)(pi a)-sigma(pi a)-k_a||<eps`.
3. *Exact outer colours.*  Lemma 4 gives cpc order-zero maps
   `tilde(theta)^(k)_i:F^(k)->C_i` with `||tilde(theta)^(k)_i-theta^(k)_i||->0`.
4. *Choice of `i`.*  Fix `i` so large that, for all `a` in `S`:
   * `||a-alpha_i(a)-beta_i(pi a)-gamma_i(pi a)||<eps` (Lemma 3(4));
   * `sum_k ||tilde(theta)^(k)_i-theta^(k)_i||<eps`;
   * `||(1-e_(i+1))^(1/2)k_a(1-e_(i+1))^(1/2)||<eps` (Lemma 2(2)).
5. *Inner approximation.*  `E_i` is isomorphic to `M_(R_i)(C(X))`, which has
   nuclear dimension `n` by (F2) and (F3).  So choose a cpc map
   `psi_E:E_i->G^(0)+...+G^(n)` and cpc order-zero maps `zeta^(k):G^(k)->E_i`
   with `||sum_k zeta^(k)psi_E^(k)(alpha_i a)-alpha_i a||<eps` for `a` in `S`.
6. *Colours.*  Put `G^(k)=0` for `k>n` and `F^(k)=0` for `k>d`.

   ```text
   L^(k)     := G^(k) + F^(k)                 (k = 0,...,m),
   L^(m+1)   := Q_(i+1)B(H)Q_(i+1)  = M_(R_(i+1)),

   psi(a)    := ( psi_E(alpha_i a) , psi_B(pi a) , (e_(i+1)-e_i)^(1/2)sigma(pi a)(e_(i+1)-e_i)^(1/2) ),
   phi(g,y)  := zeta^(k)(g) + tilde(theta)^(k)_i(y)          on L^(k), k<=m,
   phi(z)    := z tensor 1                                     on L^(m+1).
   ```

7. *`psi` and `phi` have the required form.*
   * `psi` is cpc.
   * On `L^(m+1)`, `phi` is a *-homomorphism into `A`, by Lemma 3(2).
   * On `L^(k)` with `k<=m`, the ranges of `zeta^(k)` (in `E_i`) and of
     `tilde(theta)^(k)_i` (in `C_i`) are orthogonal (Lemma 3(3)).
   * Hence, for orthogonal positive `(g,y)` and `(g',y')`, all four cross
     products vanish.  So `phi|L^(k)` is order zero.  It is contractive,
     because the two summands are orthogonal.
8. *Error estimate.*  For `a` in `S`:

   ```text
   phi psi(a) = sum_k zeta^(k)psi_E^(k)(alpha_i a) + sum_k tilde(theta)^(k)_i psi_B^(k)(pi a) + beta_i(pi a)
        ~_2eps alpha_i(a) + sum_k theta^(k)_i psi_B^(k)(pi a) + beta_i(pi a)
        ~_eps  alpha_i(a) + gamma_i(pi a) + ((1-e_(i+1))^(1/2) k_a (1-e_(i+1))^(1/2)) tensor 1 + beta_i(pi a)
        ~_eps  alpha_i(a) + beta_i(pi a) + gamma_i(pi a)
        ~_eps  a.
   ```

   This uses `m+2` colours, so `dim_nuc(A)<=m+1`.  QED.

**What made the count drop.**
* The quotient colours are placed in the outer corner `C_i`, which is exactly
  orthogonal to the inner matrix-over-`C(X)` corner.
* The transition band is exactly finite dimensional, because it is made of
  constants.  This needs the symbol to be constant; for a general Busby
  invariant, `beta_i` has values in a corner that is not finite dimensional.
* Nothing about `B` beyond `dim_nuc(B)<infinity` is used.  In particular
  `B` need not be `O_infinity`-stable and the extension need not be full,
  unlike (F9).

## 5. The circle-ideal / Cuntz-quotient models `F_(n,k)`

Fix `n>=2` and `k>=1`.  Let `F=F_(n,k)` be the finite graph with:

* vertices `u,v`;
* loops `e_1,...,e_n` at `u`;
* one loop `f` at `v`;
* edges `g_1,...,g_k` with `s(g_j)=u` and `r(g_j)=v`.

With the forward-closed convention of Section 0, `{v}` is the only nontrivial
saturated hereditary set.  So `C*(F)` has exactly one nontrivial
gauge-invariant ideal, `I_{v}`.  The subgraph over `{v}` is a cycle without
exit, and the complementary subgraph over `{u}` has `n` loops, so it has a
cycle with an exit.  This is the entry "`E_0` cycle with exit, `E_1` cycle
without exit" in the table of Evington--Ng--Sims--White, arXiv:2409.12872v2,
remark after Proposition 5.1 (checked in the TeX source).  That entry is
marked unknown there.  `F_(2,1)` is its smallest model.

**A remark on the ENSW pictures (checked in the TeX source of v2).**  The
second picture draws two loops at `x`, one loop at `y`, and an edge from `y`
to `x`.  With the paper's own convention (`s_e^*s_e=p_(r(e))`, hereditary
means forward closed), `{x}` is the hereditary set.  So the ideal is the
Kirchberg component and the quotient is the circle, which is the entry the
paper settles by its Corollary.  The unknown entry needs the connecting edge
to point from the two-loop vertex to the one-loop vertex, as in `F_(2,1)`.
The pictures match the table under the opposite (Raeburn) edge convention.
The first picture is symmetric under that change, so it is unaffected.  This
is recorded only so that nobody attacks the wrong graph.

### 5.1 A concrete pullback model

Let `P` be the set consisting of the symbol `v` and all words `w g_j`, where
`w` is a (possibly empty) word in `e_1,...,e_n` and `1<=j<=k`.  Put
`H=l^2(P)` with basis `delta_x`, and define bounded operators:

```text
E_v   := |delta_v><delta_v|,
G_j   := |delta_(g_j)><delta_v|,
T_i delta_(w g_j) := delta_(e_i w g_j),         T_i delta_v := 0.
```

For `t` in `T`, put

```text
Pi_t(p_v)=E_v,  Pi_t(p_u)=1-E_v,  Pi_t(s_f)=t E_v,  Pi_t(s_(g_j))=G_j,  Pi_t(s_(e_i))=T_i.
```

**Relations.**
* `T_i` is an isometry on `(1-E_v)H` and kills `delta_v`, so
  `T_i^*T_i=1-E_v`.
* The ranges of the `T_i` are orthogonal, because the first letters differ.
* `G_j^*G_j=E_v`, `(tE_v)^*(tE_v)=E_v=(tE_v)(tE_v)^*`, and
  `G_jG_j^*=|delta_(g_j)><delta_(g_j)|<=1-E_v`.
* *Cuntz--Krieger relation at `u`.*  Every basis vector `delta_(w g_j)` is
  either `delta_(g_j)` (empty `w`) or `delta_(e_i w' g_j)` for exactly one
  `i`.  Hence `sum_i T_iT_i^* + sum_j G_jG_j^* = 1-E_v`.
* *Cuntz--Krieger relation at `v`.*  `s_fs_f^*` maps to `E_v`.
* All range projections of distinct edges are orthogonal.

So each `Pi_t` is a Cuntz--Krieger `F`-family.  The generators vary
norm-continuously in `t`, so the universal property gives a *-homomorphism

```text
Pi: C*(F) -> C(T,B(H)),       Pi(x)(t)=Pi_t(x).
```

**The range is `A_T(D_0)`.**  Put `D_0:=C*(1,E_v,G_1,...,G_k,T_1,...,T_n)`,
a separable unital C\*-algebra.
1. *`K` is contained in `D_0`.*  For a word `w=e_(i_1)...e_(i_l)`, put
   `T_w=T_(i_1)...T_(i_l)`.  Then `T_wG_j=|delta_(w g_j)><delta_v|`, and
   `E_v` is in `D_0`.  So every `|delta_x><delta_v|` is in `D_0`, and their
   products `|delta_x><delta_v|(|delta_y><delta_v|)^*=|delta_x><delta_y|`
   give all matrix units.
2. *`Pi(C*(F))` contains `A_T(D_0)`.*  It contains `D_0 tensor 1`, because it
   contains the unit `Pi(p_u+p_v)` and the constant generators.  It also
   contains `E_v tensor z`, where `z` is the coordinate function.
   Conjugating by the constant partial isometries `|delta_x><delta_v|` gives
   `|delta_x><delta_y| tensor z`.  Together with `K tensor 1` and adjoints,
   this gives `K tensor p` for every trigonometric polynomial `p`, hence
   `C(T,K)`.
3. *`Pi(C*(F))` is contained in `A_T(D_0)`.*  `A_T(D_0)` is a C\*-algebra
   containing every generator image, since `E_v tensor z` lies in `C(T,K)`.

**Injectivity (F8).**  `Pi(p_u)` and `Pi(p_v)` are nonzero.  Define the length
by `|v|=0` and `|w g_j|=|w|+1`.  For `lambda` in `T`, let `U_lambda` be the
diagonal unitary `U_lambda delta_x=lambda^|x| delta_x`, and put

```text
beta_lambda(Phi)(t) := U_lambda Phi(lambda t) U_lambda^*       (Phi in C(T,B(H))).
```

1. *`beta` is an action.*  Each `beta_lambda` is a *-automorphism of
   `C(T,B(H))`, and `beta_lambda beta_mu=beta_(lambda mu)`.
2. *Values on generators.*  `U_lambda T_i U_lambda^*=lambda T_i`, because
   `T_i` raises length by one and kills `delta_v`.  Likewise
   `U_lambda G_j U_lambda^*=lambda G_j`, `U_lambda E_v U_lambda^*=E_v`, and
   `beta_lambda(E_v tensor z)=lambda(E_v tensor z)`.
3. *Consequences.*  `beta_lambda` maps the range onto itself, and
   `beta_lambda Pi=Pi gamma_lambda` on generators, hence everywhere.  Here
   `gamma` is the gauge action.
4. *Strong continuity.*  The set of `Phi` in the range for which
   `lambda |-> beta_lambda(Phi)` is norm continuous is a closed *-subalgebra,
   since every `beta_lambda` is isometric, and it contains the generators.
   So `beta` is strongly continuous on the range.

By the gauge-invariant uniqueness theorem, `Pi` is injective.  Hence

```text
C*(F_(n,k)) = A_T(D_0) = C(T,K) + D_0 tensor 1.                (5.1)
```

Under (5.1), `I_{v}` is the ideal generated by `E_v tensor 1`, which is
`C(T,K)` by step 2 above.

**The quotient.**  `E_v` and `G_j` are compact.  So `D_0/K` is generated by
`q(T_1),...,q(T_n)`.  These satisfy `q(T_i)^*q(T_i)=1` and
`sum_i q(T_iT_i^*)=q(1-E_v-sum_j G_jG_j^*)=1`.  So `D_0/K` is a quotient of
`O_n`.  It is nonzero, since `D_0` is unital and `H` is infinite dimensional.
`O_n` is simple, hence

```text
D_0/K = O_n.                                                    (5.2)
```

**Corollary 5.**  `1 <= dim_nuc(C*(F_(n,k))) <= 2` for all `n>=2` and `k>=1`.

*Proof via Theorem 1.*  Take `X=T`, so `n_X=1`, and `D=D_0`.  By (F6'),
`d=dim_nuc(O_n)=1` (alternatively by (F6) and (F7)).  Apply (5.1), (5.2) and
Theorem 1.  QED.

*Independent proof via (F9).*
1. *The extension.*  `0->C(T,K)->C*(F)->O_n->0` by (5.1) and (5.2).
   `J=C(T,K)` is separable and stable.  `O_n` is separable, nuclear and
   `O_infinity`-stable by (F7).
2. *`J` is essential.*  If `Phi` in `A` satisfies `Phi C(T,K)=0`, then
   `Phi(t)K=0` for all `t`, so `Phi=0`.
3. *Fullness.*  `A` is unital, so its Busby invariant `tau:O_n->Q(J)` is
   unital and injective.  For `b!=0`, the ideal of `Q(J)` generated by
   `tau(b)` contains `tau` of the ideal generated by `b`, which is `tau(O_n)`
   and so contains `1`.  So the extension is full.
4. *Conclusion.*  (F9) gives `1<=dim_nuc(A)<=dim_nuc(C(T) tensor K)+1=2`, by
   (F2) and (F3).  QED.

So the upper bound for this ENSW entry is already a formal consequence of
Evington's theorem.  What is new here is only the explicit model (5.1) and
the second, `O_infinity`-free proof.  The entry "?" in the table is the choice
between `1` and `2`.

## 6. Which models split

**Proposition 6.**  The extension `0->C(T,K)->C*(F_(n,k))->O_n->0` admits a
*-homomorphic splitting if and only if `k=n-1`.  For `k=n-1` there are
Cuntz isometries `W_1,...,W_n` in `D_0` with `W_i-T_i` of rank one, so that

```text
C*(F_(n,n-1)) = C(T,K) + rho(O_n) tensor 1,      rho(S_i)=W_i.
```

In particular the ENSW minimal model `F_(2,1)` is a split extension.

*Proof.*
1. *Index of the row.*  Let `R=[T_1 ... T_n]:H^n->H`.
   * `ker R` is the direct sum of the `n` lines `C delta_v`, since the `T_i`
     are injective off `delta_v` with orthogonal ranges.
   * `ran R` is the closed span of all `delta_(e_i w g_j)`, whose orthogonal
     complement is spanned by `delta_v,delta_(g_1),...,delta_(g_k)`.
   * So `R` is Fredholm with index `n-(k+1)=n-k-1`.
2. *Necessity.*
   * Let `sigma:O_n->A` be a *-homomorphism splitting the quotient map.  Put
     `p=sigma(1)` and `W_i=sigma(S_i)`, where `S_i` are the Cuntz generators,
     identified with `q(T_i)` by (5.2).
   * `1-p` lies in `C(T,K)`, so for each `t` the projection `1-p(t)` has some
     finite rank `r`.
   * Write `W_i=c+x tensor 1` with `c` in `C(T,K)` and `x` in `D_0`.  Then
     `q(x)=q(T_i)`, so `W_i(t)-T_i` is compact.
   * The `W_i(t)` are isometries from `p(t)H` onto mutually orthogonal ranges
     that sum to `p(t)`, and they vanish on `(1-p(t))H`.  So
     `[W_1(t) ... W_n(t)]` has kernel of dimension `nr` and cokernel of
     dimension `r`, hence index `(n-1)r`.
   * Compact perturbations do not change the index, so `n-k-1=(n-1)r`, that
     is, `k=(n-1)(1-r)`.  Since `k>=1`, this forces `r=0` and `k=n-1`.
3. *Sufficiency.*  Let `k=n-1`, and put `xi_i=delta_(g_i)` for `i<n` and
   `xi_n=delta_v`.  Define `W_i=T_i+|xi_i><delta_v|`, which lies in `D_0`.
   * *Isometries.*  `xi_i` is orthogonal to the range of `T_i`, and
     `T_i delta_v=0`.  So
     `W_i^*W_i=T_i^*T_i+|delta_v><delta_v|=1`.
   * *Range projections.*  `W_iW_i^*=T_iT_i^*+|xi_i><xi_i|`.
   * *Cuntz relation.*  By the Cuntz--Krieger relation at `u`,
     `sum_i W_iW_i^*=(1-E_v-sum_(j<n) G_jG_j^*)+sum_(j<n)|delta_(g_j)><delta_(g_j)|+E_v=1`.
   * *The splitting.*  So `S_i |-> W_i` defines a unital *-homomorphism
     `rho:O_n->D_0` with `q rho=id`.  Every `x` in `D_0` satisfies
     `x-rho(q(x))` in `K`, and `b |-> rho(b) tensor 1` splits (5.1).  QED.

*Finite sanity check.*  The script
`experiments/stw99-constant-symbol-pullback-2026-09-16/check_fnk.py` truncates
`P` to words of length at most `L`.  It verifies exactly, with integer
matrices, for `2<=n<=4`, `1<=k<=3` and `L` in `{2,3}`:
* the Cuntz--Krieger relations of Section 5.1;
* the matrix units `T_wG_j`;
* gauge covariance;
* the kernel and cokernel counts `n` and `k+1` used in step 1;
* for `k=n-1`, the Cuntz relations for `W_i`.

It passed on 2026-09-16.  This is evidence against slips only; the proofs
above do not depend on it.

**Consequences for the dimension problem.**
* The split models are not easier in any way I could use.  The section
  `rho(O_n) tensor 1` does not commute with `C(T,K)`, so centralizing-section
  arguments do not apply.
* `C(T,K)` is stably finite, so `A` is not `O_infinity`-stable (ideals of
  `O_infinity`-stable algebras are `O_infinity`-stable), and (F6) does not
  apply.
* The six-term boundary maps vanish for every `k`: `K_1(O_n)=0` and
  `K_0(O_n)` is torsion, while `K_0` and `K_1` of `C(T) tensor K` are `Z`.
  But `K`-theory is not blind to `k`.  (Referee correction, 2026-09-16.)  The
  standard graph formula gives `K_0(C*(F_(n,k)))=Z^2/<(n-1,k)>` and
  `K_1=Z`, and the resulting group extension
  `0->Z[p_v]->K_0(A)->Z/(n-1)->0` has class `k mod (n-1)` up to sign in
  `Ext(Z/(n-1),Z)=Z/(n-1)`.  A *-homomorphic splitting splits this sequence.
  So `K_0` already forces `k = 0 mod (n-1)`.  The index in step 2 is finer:
  it separates `k=n-1` from the other multiples of `n-1`, and for `n=2` it is
  the only obstruction.  (Standard `K`-groups of `O_n` and the graph
  `K`-theory formula; computed by hand, not re-fetched.)

## 7. The canonical circle-by-circle family

For `N>=1`, let `S` be the unilateral shift, `T_N:=C*(S^N,K)`, and

```text
A_N=C*(S^N tensor 1, K tensor C(T)).
```

The established claim `stw83-canonical-circle-is-constant-symbol-pullback`
identifies `A_N` with `{x in C(T,T_N) : q_N(x(t)) independent of t}`.  This
set equals `A_T(T_N)`:
* if `q_N(x(t))=b` for all `t`, pick `y` in `T_N` with `q_N(y)=b`; then
  `x-y tensor 1` is a norm-continuous `K`-valued function;
* the reverse inclusion is clear.

Moreover:
* `K subseteq T_N subseteq B(l^2)`, and `T_N` is separable and unital, since
  `(S^N)^*S^N=1`.
* `T_N/K` is generated by the unitary `q(S^N)`, so it is isomorphic to
  `C(sigma_ess(S^N))`.
* `S^N` is unitarily equivalent to `N` copies of `S`, so
  `sigma_ess(S^N)=T` and `T_N/K=C(T)`.

**Corollary 7.**  `1<=dim_nuc(A_N)<=2`.  This is Theorem 1 with `X=T` and
`d=dim C(T)=1` (F2).  It recovers
`stw83-canonical-circle-toeplitz-dimension-two-bound` without the
connector-corner claim and without the Brake--Winter normal-lifting step.

## 8. The colour ledger and the common hinge

Let `n=dim X` and `d=dim_nuc(B)`.

| scheme | inner corner | band | outer quotient | colours |
| --- | --- | --- | --- | --- |
| generic [WZ10, 2.9] | `n+1` | (absorbed) | `d+1`, separate | `n+d+2` |
| Evington (F9), `J` stable, `B` `O_infinity`-stable | total only (internal split not audited here) | | | `dim_nuc(J)+2` |
| Theorem 1, constant symbol | `n+1` in `E_i` | one *-homomorphism colour | `d+1` in `C_i`, merged | `max(n,d)+2` |

For both unknown ENSW entries, `n=d=1`.
* The generic scheme gives four colours.
* Theorem 1 gives three colours for both entries.
* Evington's theorem also gives three, but only for entry (i).  For entry (ii)
  the quotient `C(T)` is not `O_infinity`-stable.

In the constant-symbol scheme the position is the same in both cases:

* The outer colours live in `C_i`, which is orthogonal to the inner corner
  `E_i=M_(R_i)(C(T))`.  This merge is exact and costs nothing.
* The band colour lives in `M_(R_(i+1)) tensor 1`, which meets both `E_i`
  (through `Q_i(1-e_i)Q_i`) and `C_i` (through
  `(1-Q_i)e_(i+1)(1-Q_i)`).  So it is orthogonal to neither.
* In the scalar Toeplitz case `X=point` (Brake--Winter, as recorded in the
  route `stw83-coefficient-toeplitz-three-colour-proof`), the band is merged
  with one quotient colour, and the whole inner corner, which is finite
  dimensional and needs one colour, goes into the other quotient colour.
* For `X=T`, the inner corner needs two colours (F2, F3), and only one of
  them can be pushed away from the band.

So this three-piece scheme, with the colours merged as above, spends three
colours and does not by itself give nuclear dimension one for either entry.
A two-colour version of the scheme would have to recolour coefficient information across the band.  This is a
heuristic reading of the colour count, not a no-go theorem.  (Referee
softening, 2026-09-16.)  For the circle-by-circle family
this is exactly the support condition in `stw83-plateau-buffer-recolouring-hinge`,
with the no-go results `stw83-circle-unitary-order-zero-plus-constants-gap`
and `stw83-commuting-cone-two-colour-firewall`.  The present count shows that
the Kirchberg-quotient entry meets the same hinge.  Replacing `C(T)` by `O_n`
in the quotient changes only the outer colours of this scheme.
No new obstruction or recolouring is claimed here.
