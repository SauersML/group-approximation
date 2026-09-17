---
rg: 2
id: sp4-parabolic-theorem-c-every-lambda-proof
kind: route
title: Levi-coset counting makes the stabilizer field central, then commutator cocycles plus CFW, or finite restriction kernels plus compact coboundaries
target: sp4-parabolic-theorem-c-data-dies-for-every-lambda
requires: [sp4-parabolic-radical-theorem-c-data-dies]
---

**Setup.**  The notation is that of `sp4-parabolic-radical-theorem-c-data-dies-proof`.

- Fix a Borel pointwise model of `sigma`.  We have the twisted group ring over
  `L^0(X,T)`, with `u_g f u_g^{-1} = sigma_g(f)` and `u_g u_h = c(g,h) u_{gh}`.
  It is a free left `L^0`-module on the basis `{u_g}`.
- `L = P/R`.  `V = R` in the Siegel case and `V = R/Z_R` in the Klingen case.
  `V` is a torsion-free lattice, and `L` acts on it.
- The kernel of the `L`-action on `V` is `L cap {+-I_4}`.
  - Siegel: `g` acts by `S -> g S g^T`, and `g S g^T = S` for all `S` iff
    `g = +-I_2`.
  - Klingen: `(epsilon, h) in {+-1} x SL_2(Z)` acts on `V ~ Z^2` by
    `epsilon h`, and `epsilon h = I` iff `(epsilon,h) in {(1,I), (-1,-I)}`,
    that is, `+-I_4`.
- `-I_4` is central in `Sp_4(Z)`.  So it acts trivially on `R` by conjugation.
- `Z_R` is central in `P` (Klingen; see the wave-4 route).

**Hypotheses used.**

- `(P, Lambda)` has relative (T).
- `sigma|Lambda` is ergodic, hence `sigma` is `P`-ergodic.
- `c_n -> 1` pointwise in `L^2`.

**Step 0 (Lambda is virtually in R).**  The image of `Lambda` in `L` has
relative (T) in `L`.  `L` is virtually free, hence a-T-menable, so that image is
finite.  This is the same input as Consequence 1 of the wave-4 route.  Put
`Lambda_0 = Lambda cap R`; its index `d` is finite.  `Lambda_0` is finitely
generated nilpotent, so `Lambda` is amenable.

**Step 1 (radical trichotomy).**  This is Step 0 of the wave-4 route verbatim.
It uses only that `sigma` is `P`-ergodic, not that `Lambda <= R`.  So
`K_x = Stab_R(x)` is a.e. one of:

- (a) `K_x = 1`;
- (b) Klingen only, `K_x = mZ_R` with `m >= 1` constant;
- (c) `[R : K_x] < infinity`.

**Step 2 (counting lemma: in types (a) and (b) the P-stabilizers are central).**
Assume type (a) or (b).  Put `K = 1` or `K = mZ_R`, so `K_x = K` a.e.  Let
`S_x = Stab_P(x)`.  For `g in P` put `Fix(g) = {x : g in S_x}`.  It is Borel,
and `mu(Fix(p g p^{-1})) = mu(p Fix(g)) = mu(Fix(g))`.

*(i) One `K`-coset per `R`-coset.*  If `h, h' in S_x cap gR` then
`h^{-1} h' in S_x cap R = K`.  So, off a null set, `S_x cap gR` is empty or a
single coset `hK`.  Since `K <= S_x` a.e., `Fix(h) = Fix(hk)` a.e. for
`k in K`.  Hence for `K`-cosets `hK != h'K` inside `gR`, `Fix(h)` and
`Fix(h')` are a.e. disjoint.

*(ii) Infinite conjugation orbits.*  Let `l` be the image of `g` in `L`, and
suppose `l` acts nontrivially on `V`.  For `r in R`,
`r g r^{-1} = (r . Ad_g(r)^{-1}) g`.  Modulo `Z_R` (Klingen), or exactly
(Siegel, `Z_R := 1`), `r . Ad_g(r)^{-1}` is `(1 - l)v_r`, where `v_r` is the
image of `r` in `V`.  Choose `r` with `(1-l)v_r = v != 0`.  Then
`r^j g r^{-j}` has `V`-coordinate `j v`, and these are pairwise distinct since
`V` is torsion-free.  Because `K <= Z_R`, the cosets `r^j g r^{-j} K`
(`j in Z`) are pairwise distinct `K`-cosets inside `gR`.  By (i) the sets
`Fix(r^j g r^{-j})` are a.e. pairwise disjoint and all have measure
`mu(Fix(g))`, so `mu(Fix(g)) = 0`.  `P` is countable, so a.e.
`S_x <= ker(L -> Aut V)`-preimage `= R . (P cap {+-I_4})`.

*(iii) The `-I_4`-coset.*  Let `g = r_0 (-I_4) in S_x`.  Since `-I_4` is
central of order 2, `g^2 = r_0^2 in S_x cap R = K <= Z_R`.  The image of `r_0`
in `V` then satisfies `2 v_{r_0} = 0`, so `r_0 in Z_R`; in the Siegel case
`2 r_0 = 0` gives `r_0 = 0`.  Moreover `S_x cap R = K`.  Therefore

```text
S_x <= Z_R . {1, -I_4}   (Klingen),      S_x <= {1, -I_4}   (Siegel),   a.e.
```

Both groups are central in `P`, because `Z_R` is central in `P_K`.

*(iv) Constancy.*  `S_{px} = p S_x p^{-1} = S_x` for `p in P`, so
`x -> S_x` is `P`-invariant.  It takes countably many values (subgroups of the
countable group `Z_R x Z/2`).  By `P`-ergodicity it is a.e. equal to a fixed
central subgroup `S`.  Put `W = S cap Lambda`.  Then `Stab_Lambda(x) = W`
a.e., `W` acts trivially on `X`, and `W` is a finitely generated abelian group
`Z^a x (Z/2)^b` with `a, b <= 1`.

**Step 3 (types (a), (b): central isotropy dies).**  Let `W` be as in Step 2(iv).
If `W = 1`, then `Lambda` is amenable (Step 0) and acts essentially freely and
ergodically.  ISW (arXiv:2006.01874, p. 3) state verbatim:
"`H^2(Gamma,L^0(X,T))=0`, for any free ergodic p.m.p. action
`Gamma ~> (X,mu)`, if `Gamma` is an amenable group [CFW81]".  So `c_n|Lambda`
is a coboundary for every `n`.  Otherwise fix a basis `w_1, ..., w_s`
(`s <= 2`) of `W ~ Z^a x (Z/2)^b`.

1. *Commutator cocycles.*  Each `w = w_i` is central in `P` and acts trivially
   on `X`.  The wave-4 route, Case (b), steps 1 and 2, use only these two
   facts, together with relative (T) of `(P,Lambda)` and ergodicity of
   `sigma|Lambda`.  So `gamma^i_n(g) = c_n(w_i,g) c_n(g,w_i)^{-1}` is a
   1-cocycle on `P`.  For `n` outside a finite set `J_i`, there are
   `eta_i in L^0(X,T)` with `gamma^i_n(l) = eta_i sigma_l(eta_i)^{-1}` for all
   `l in Lambda`.
2. *Centralize.*  For `n` outside `J_1 u ... u J_s`, put
   `w_i' = eta_i^{-1} u_{w_i}`.  As in the wave-4 route, `w_i'` commutes with
   `L^0` and with every `u_l`, `l in Lambda`.  Since `w_j' in L^0 u_{w_j}`, the
   `w_i'` commute pairwise.
   - If `w_i` has order 2, then `f = w_i'^2 in L^0` is central in the
     `Lambda`-ring.  So `sigma_l(f) = f` for all `l in Lambda`, and `f` is a
     constant by ergodicity.  Replace `w_i'` by `f^{-1/2} w_i'` (a constant
     square root) to get `w_i'^2 = 1`.
   - For `w = prod w_i^{j_i}` (normal form) put `V_w = prod w_i'^{j_i}`.  Then
     `V_w V_{w'} = V_{ww'}` and `V_w in L^0 u_w`.
3. *Descend.*  Let `Q = Lambda/W`, choose a section `s : Q -> Lambda`, and
   write `l = s(q) w` uniquely.  Put `U_l = u_{s(q)} V_w in L^0 u_l`.  So
   `U_l = b(l) u_l` for some `b(l) in L^0(X,T)`, and the cocycle of `U` is
   `c_n|Lambda . db`.
   - Write `s(q)s(q') = s(qq') a(q,q')` with `a in W`.  Then
     `u_{s(q)} u_{s(q')} = c_n(s(q),s(q')) u_{s(qq') a}`.
   - Both `u_{s(qq')a}` and `u_{s(qq')} V_a` lie in `L^0 u_{s(qq')a}`, so they
     differ by a factor in `L^0`.
   - The `V`'s are central in the `Lambda`-ring and multiplicative.  Hence
     `U_l U_{l'} = F_n(q,q') U_{ll'}` with `F_n(q,q') in L^0(X,T)` depending
     only on `(q,q')`.
   - Associativity of the free `L^0`-module ring makes `F_n` a 2-cocycle of `Q`
     with coefficients in `L^0(X,T)`.  The action of `Q` is well defined
     because `W` acts trivially.
4. *CFW.*  `Q` is amenable and acts ergodically.  It acts essentially freely,
   since `Stab_Lambda(x) = W` a.e.  By the CFW statement above,
   `F_n = d beta_n`.  The inflation of `F_n` to `Lambda` is the cocycle of `U`,
   so it is a coboundary.  Hence `c_n|Lambda` is a coboundary for every `n`
   outside `J_1 u ... u J_s`.

**Step 4 (type (c): finite orbits die).**

*Reduction to one point.*  `Lambda_0 cap K_x` has finite index in `Lambda_0`,
and `[Lambda : Lambda_0] < infinity`.  So every `Lambda`-orbit is finite, and an
ergodic p.m.p. action with finite orbits is a single orbit with uniform measure.
Thus `X = Lambda x_0`, and `P x_0 = X` since `P` preserves `mu`.

Put `P_1 = Stab_P(x_0)`, `N_1 = R cap P_1`, `Lambda_1 = Lambda cap P_1` and
`M_1 = Lambda_1 cap R = Lambda_1 cap N_1`.  `M_1` is normal in `Lambda_1`, and
`C = Lambda_1/M_1` embeds in the finite image of `Lambda` in `L` (Step 0).

*(i) Radical restriction dies.*  `c'_n = c_n(.,.)(x_0)|P_1 in Z^2(P_1,T)` and
`c'_n -> 1` pointwise.  The wave-4 route, Case (c), uses only this, `N_1` and the
`P_1`-action.  It shows the class of `c'_n|N_1` is a `P_1`-invariant character
of `H_2(N_1,Z)` lying in a finite set, hence trivial for large `n`.  So
`c'_n|M_1` is a coboundary for `n >= n_0`.

*(ii) The restriction kernel is finite.*  Consider
`res : H^2(Lambda_1,T) -> H^2(M_1,T)` (trivial coefficients).  By
Lyndon--Hochschild--Serre, `ker(res) = F^1 H^2`.  Here `F^2 H^2` is a quotient of
`E_2^{2,0} = H^2(C,T)`, and `F^1/F^2` embeds in
`E_2^{1,1} = H^1(C, Hom(M_1,T))`.

- `H^2(C,T) ~ H^3(C,Z)` is finite, since `C` is finite.
- `Hom(M_1,T) = Hom(M_1^{ab},T)` is a compact abelian Lie group `A`.  Its
  identity component `A^0 ~ T^r` is `C`-invariant, and `A/A^0` is finite.
- From `0 -> Z^r -> R^r -> T^r -> 0` and `H^i(C,R^r) = 0` for `i >= 1`, we get
  `H^1(C,T^r) ~ H^2(C,Z^r)`, which is finite.
- The long exact sequence for `A^0 -> A -> A/A^0` makes `H^1(C,A)` finite.

So `ker(res)` is finite.

*(iii) Coboundaries are open.*  Give `Z^2(Lambda_1,T)` the pointwise topology,
a closed subgroup of the compact group `T^{Lambda_1 x Lambda_1}`.
`B^2(Lambda_1,T) = d(T^{Lambda_1})` is the continuous image of a compact group,
so it is compact.  The same holds for `B^2(M_1,T)`.  Hence
`Z_0 = {z in Z^2(Lambda_1,T) : z|M_1 in B^2(M_1,T)}` is a closed subgroup.
`Z_0/B^2(Lambda_1,T) = ker(res)` is finite, so `B^2(Lambda_1,T)` is a closed
subgroup of finite index in `Z_0`, hence open in `Z_0`.  For `n >= n_0`,
`c'_n|Lambda_1 in Z_0` and `c'_n|Lambda_1 -> 1 in B^2`.  Therefore
`c'_n|Lambda_1 in B^2(Lambda_1,T)` for all large `n`.

*(iv) Shapiro.*  As a `Lambda`-module, `L^0(X,T) = Coind_{Lambda_1}^{Lambda} T`.
The map `[c] -> [c(.,.)(x_0)|Lambda_1]` is an isomorphism
`H^2(Lambda, L^0(X,T)) -> H^2(Lambda_1,T)` (wave-4 route, Case (c)).  So
`c_n|Lambda` is a coboundary for all large `n`.

**Conclusion.**  By Step 1, one of types (a), (b), (c) holds a.e.  Steps 3 and 4
give `(TC-P)` in every case.  No hypothesis on `Lambda cap R` (ergodicity,
index, torsion of the class) was used beyond Step 0.  So the torsion-Levi residue
of `sp4-parabolic-radical-theorem-c-data-dies` is empty.

**Sanity check against ISW's positive examples.**  The mechanism correctly does
not fire where ISW succeed.

- In `Z^2 x| SL_2(Z)` with `Lambda = Z^2` and a point `X`, `H_2(Z^2) = det` is the
  trivial `SL_2`-module.  So the invariant characters form a whole circle, and
  Step 4(i) fails.  That is exactly ISW's scalar family `omega_t`.
- The Sp4 radicals have `H_2 = Sym^2 (x) det` or `V`, with no coinvariants, and
  that is where finiteness comes from.
- Step 2 needs the Levi kernel on `V` to be central.  It uses the integral
  structure of the parabolic, not property (T) of `Sp_4(Z)`.
