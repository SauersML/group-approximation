---
rg: 2
id: amenable-fixed-projection-not-in-adjoint-corona-proof
kind: route
title: Embed the conjugation representation on l^2 of an infinite L-class into the ultraproduct, push Folner sets forward to get almost-invariant vectors orthogonal to Fix(L), and contradict the saturation gap
target: amenable-subgroup-fixed-projection-is-never-in-adjoint-corona
requires:
  - corona-fixed-projection-membership-is-finite-markov-gap
---

Notation is that of the target and of
`corona-fixed-projection-membership-is-finite-markov-gap`. `tr` is the
normalized trace on `M_(d_n)` and `||x||_2=tr(x^*x)^(1/2)`. `U^omega_l` is
`pi_omega(sigma~(l))`, which acts on `[x_n]_omega` by
`[V_n(l) x_n V_n(l)^*]_omega`, up to `o(1)` coming from the replacement of
`V_n(l)^(-1)` by `V_n(l)^*`.

## Step 1: the isometric equivariant embedding of l^2(O)

Fix a free ultrafilter `omega`. For `o in O` put `iota(delta_o)=[V_n(o)]_omega`.
This is a bounded sequence in `(M_(d_n),||.||_2)`, since `||V_n(o)||_op` is
bounded.
- *Isometry.* For `o,o' in O`,
  `<[V_n(o)],[V_n(o')]> = lim_omega tr(V_n(o')^* V_n(o))`. By operator-norm
  asymptotic multiplicativity, `||V_n(o')^*V_n(o) - V_n(o'^(-1)o)||_op -> 0`,
  and `|tr x| <= ||x||_op`. So the inner product is
  `lim_omega tr V_n(o'^(-1)o)`. Now `o'^(-1)o in <L,g>`, so by (A3) this is
  `1` if `o=o'` and `0` otherwise. So `iota` extends to an isometry
  `l^2(O) -> H_omega`.
- *Equivariance.* For `l in L`,
  `||V_n(l)V_n(o)V_n(l)^* - V_n(lol^(-1))||_op -> 0`. So
  `U^omega_l iota(delta_o) = iota(delta_(lol^(-1)))`. Hence `iota` intertwines
  the conjugation representation `gamma`, with
  `(gamma(l)f)(o)=f(l^(-1)ol)`, and `U^omega|L`.
  As `L`-sets, `O` and `L/C_L(g)` are isomorphic, so `gamma` is the
  quasi-regular representation `lambda_(L/C_L(g))`.

## Step 2: iota(l^2(O)) is orthogonal to Fix(L)

`M=iota(l^2(O))` is closed and invariant under every unitary `U_l`, `l in L`.
Since `L` is a group, it is also invariant under `U_l^*=U_(l^(-1))`. So the
projection `P_M` commutes with every `U_l`, and hence with `P_L`. Then
`P_M P_L` is the projection onto `M cap Fix(L)`, and
`M cap Fix(L) = iota(l^2(O)^gamma)`.

A `gamma`-invariant `f` is constant on the single `L`-orbit `O`. An `l^2`
constant on an infinite set is `0`, by (A2). So `P_M P_L=0`, that is,
`M subset Fix_omega(L)^perp`. Because
`Fix(L)=direct_sum_omega Fix_omega(L)` (Step 0 of the saturation proof), `M`
is also orthogonal to `Fix(L)` inside `H_B`.

## Step 3: Folner pushforward

Let `(Phi_k)` be a left Folner sequence of `L`: finite nonempty sets with
`|l Phi_k Delta Phi_k| / |Phi_k| -> 0` for every `l in L`.
- Let `p:L->O`, `p(l)=lgl^(-1)`. It is surjective and equivariant:
  `p(l'l)=l' p(l) l'^(-1)`.
- Put `f_k = p_*(1_(Phi_k))`, that is, `f_k(o)=|Phi_k cap p^(-1)(o)|`. Then
  `f_k>=0`, `||f_k||_1=|Phi_k|`, and `gamma(l)f_k=p_*(1_(l Phi_k))`.
- Since `p_*` is an `l^1` contraction on nonnegative functions,
  `||gamma(l)f_k - f_k||_1 <= |l Phi_k Delta Phi_k|`.
- Put `h_k = (f_k/|Phi_k|)^(1/2)`, a unit vector of `l^2(O)`. Since `gamma(l)`
  permutes coordinates, `gamma(l)h_k=(gamma(l)f_k/|Phi_k|)^(1/2)`. By
  `|a^(1/2)-b^(1/2)|^2 <= |a-b|` for `a,b>=0`,

```text
||gamma(l)h_k - h_k||_2^2 <= ||gamma(l)f_k - f_k||_1 / |Phi_k|
                         <= |l Phi_k Delta Phi_k| / |Phi_k| -> 0 .
```

So `gamma` has almost-invariant unit vectors. Only amenability of the
`L`-set `O` was used, which follows from (A1).

## Step 4: the contradiction

Put `xi_k=iota(h_k) in H_omega subset H_B`. By Steps 1 and 2, `xi_k` is a unit
vector in `Fix(L)^perp`. For every finite `F subset L`,
`max_(f in F)||U_f xi_k - xi_k|| = max_(f in F)||gamma(f)h_k-h_k|| -> 0`.
So condition (2) of `corona-fixed-projection-membership-is-finite-markov-gap`
fails for every finite `F` and every `kappa>0`. By (1) implies (2) of that
theorem, `P_L notin pi(B)`. This proves the first two assertions of
Theorem A.

*General form, without (A1).* Suppose `P_L in pi(B)`, and let `F` and `kappa`
be as in (2). Let `c=kappa^2/(2|F|)`. For every `g'` with
`tr V_n -> delta_e` on `<L,g'>` and infinite `L`-class `O'`, Steps 1-2 place
`l^2(O')` isometrically in `Fix(L)^perp`. The computation of Step 2 of the
saturation proof gives

```text
<gamma_(O')(h_F)xi, xi> <= (1-c)||xi||^2   for all xi in l^2(O'),
```

so `sup sp(lambda_(L/C_L(g'))(h_F)) <= 1-c`. The pair `(F,c)` is the same for all such `g'`: the
conjugation action is uniformly non-amenable on its infinite classes.

## Step 5: Corollary B (the Jacobson column)

In `M_5(J)`, with `e_13 e_21=0`, `e_21 e_13=e_23`, `e_13^2=0`,

```text
(1+a e_13)(1+e_21)(1-a e_13) = (1+e_21+a e_13)(1-a e_13)
                              = 1 + e_21 - a e_23
                              = (1+e_21)(1-a e_23)   (as e_21 e_23 = 0),
```

that is, `x_13(a) x_21(1) x_13(a)^(-1) = x_21(1) x_23(-a)`. In characteristic
`2`, `-a=a`. The matrices `x_21(1)x_23(a)` are pairwise distinct for distinct
`a in J`, and `J` is infinite. So the `N`-class of `g=x_21(1)` is infinite.

`N=X_13(J)X_23(J)` is abelian, because `[x_13(a),x_23(b)]=1` (the product
`e_13 e_23=e_23 e_13=0`), and is isomorphic to `J^2`. So `N` is amenable. Also
`<N,g> subset K`. Under the hypothesis `tr V_n -> delta_e` on `K`,
(A1)-(A3) hold, and `P_N notin pi(B)`. This holds in particular under
(K1)-(K3) of `root-column-fixed-projection-is-not-in-root-pair-cstar`, whose
hypotheses include this profile on `K`. So the prerequisite "`P_N in B`" in
that node's What-is-left is false, not merely unproved.

## Step 6: Corollary C (all infinite amenable subgroups of EL_5(J))

*(a) `Z(J)=F_2`.*
- The rewriting system `TS -> 1` on words in `S,T` has no overlaps, since
  no proper suffix of `TS` is a prefix of `TS`. By the diamond lemma,
  `{S^i T^j : i,j>=0}` is an `F_2`-basis of `J`.
- Let `z=sum c_(ij) S^iT^j` be central. The products are
  `S*S^iT^j=S^(i+1)T^j`, `S^iT^j*S=S^iT^(j-1)` for `j>=1`, and
  `S^i*S=S^(i+1)`.
- Compare the coefficients of `S^aT^b` in `Sz=zS`:
  - for `b>=1`: `c_(a-1,b)=c_(a,b+1)`, where `c_(-1,*)=0`;
  - for `b=0`: `c_(a-1,0)=c_(a,1)+c_(a-1,0)`, so `c_(a,1)=0` for every `a>=0`.
- The first relation gives `c_(a,j)=c_(a-1,j-1)` for `j>=2`. Iterating
  reaches either `c_(-1,*)=0` or some `c_(*,1)=0`. So `c_(a,j)=0` for all
  `j>=1`, and `z=sum_i c_(i0) S^i`.
- In `Tz=zT`: `zT=sum c_(i0) S^iT`, while
  `Tz=c_(00)T+sum_(i>=1) c_(i0) S^(i-1)`. The basis elements `S^(i-1)` do not
  occur in `zT`, so `c_(i0)=0` for `i>=1`. Hence `z=c_(00) in F_2`.

*(b) `Z(EL_5(J))=1`.* Let `z in EL_5(J) subset GL_5(J)` be central. It commutes
with `x_ij(1)=1+e_ij`, hence with every `e_ij`, `i != j`. So `z=lambda I` is
scalar. Commuting with `x_ij(a)=1+a e_ij` gives `lambda in Z(J)=F_2`, and
invertibility gives `lambda=1`.

*(c) Finite generation.* `x_ij(a+b)=x_ij(a)x_ij(b)`. For distinct `i,j,k`,
`[x_ij(u),x_jk(v)]=x_ik(uv)`, and there are three distinct indices in rank 5.
By induction on the word length, every `x_ij(w)` with `w` a monomial in
`S,T` lies in the subgroup generated by the finite set
`Sigma={x_ij(1),x_ij(S),x_ij(T)}`. By additivity, every `x_ij(a)` does too.
So `E=<Sigma>`.

*(d) An infinite class.* Let `L<=E` be infinite. If every `s in Sigma` had a
finite `L`-class, then `L'=cap_(s in Sigma) C_L(s)` would have finite index in `L`
and centralize `E`. By (b), `L'=1`, so `L` would be finite, a contradiction.
So some `s in Sigma` has an infinite `L`-class.

*(e) Conclusion.* Suppose `L` is also amenable and `tr V_n -> delta_e` on all of `E`.
Then Theorem A applies with `G=E` and `g=s`, so `P_L notin pi(B)`. `QED`

## Remarks on scope

- (A3) is used only on `<L,g>`. It enters only through the isometry of Step 1.
- Nothing is assumed about the model beyond operator-norm asymptotic
  multiplicativity and the trace profile. In particular, the result is
  independent of `root-column-fixed-projection-is-not-in-root-pair-cstar`,
  whose (K1)-(K3) it does not need, and it gives a second proof of that node's
  theorem in the `delta_e`-profile case. `P_N notin pi(B)` implies
  `P_N notin pi(A_K)`.
- Mere existence of the models is not asserted. Their existence is exactly the
  open hole `jacobson-regular-character-not-mf-without-property-t`.
