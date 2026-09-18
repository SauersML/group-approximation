---
rg: 2
id: root-column-fixed-projection-is-not-in-root-pair-cstar-proof
kind: route
title: Realize a tempered quasi-regular representation exactly on Fix(N) by centralizing root vectors and weakly on its complement through the trace, then use centrality of P_N to split the algebra
target: root-column-fixed-projection-is-not-in-root-pair-cstar
requires:
  - steinberg-group-homology-gives-k2-and-k3
  - elementary-linear-semidir-pair-relative-t
---

Notation is that of the target. All representations of a discrete group
`K` are also representations of the full algebra `C*(K)`. Write
`Sigma:C*(K)->A_K` for the surjection with `u_k -> sigma~(k)`. We say `rho` is
**weakly contained** in `pi`, written `rho << pi`, if
`ker pi subset ker rho` in `C*(K)`.

## Step 0: two standard lemmas

**Lemma F (Fell's inequality).** Let `rho` be a representation of `K` with
cyclic unit vector `xi`, and let `pi` be a representation. Suppose unit
vectors `eta_k` satisfy
`<pi(g)eta_k,eta_k> -> <rho(g)xi,xi>` for every `g in K`. Then `rho << pi`.

*Proof.*
- For `a in C[K]`, `||rho(a)xi||^2 = <rho(a^*a)xi,xi> = lim ||pi(a)eta_k||^2`.
  The coefficients converge pointwise and `a^*a` has finite support.
- For `a,b in C[K]`:
  `||rho(a)rho(b)xi|| = lim||pi(a)pi(b)eta_k|| <= ||pi(a)|| lim||pi(b)eta_k||
  = ||pi(a)|| ||rho(b)xi||`.
- The vectors `rho(b)xi` are dense, so `||rho(a)|| <= ||pi(a)||` on
  `C[K]`. By continuity this holds on `C*(K)`, so `ker pi subset ker rho`.
  `QED`

**Lemma Q (amenable stabilizers are tempered).** If `C<=K` is amenable,
then `lambda_(K/C) << lambda_K`.

*Proof.*
- Let `F_k subset C` be Folner sets for `C`, and put
  `eta_k = 1_(F_k)/sqrt|F_k|` in `l^2(K)`.
- For `g notin C`, `gF_k cap F_k subset gC cap C = empty`.
- For `g in C`, `|gF_k cap F_k|/|F_k| -> 1`.
- So `<lambda_K(g)eta_k,eta_k> -> 1_C(g) = <lambda_(K/C)(g)delta_C,delta_C>`.
  The vector `delta_C` is cyclic, so Lemma F applies. `QED`

## Step 1: the exact summand on Fix(N)

Fix a free ultrafilter `omega` and put `eta=[V_n(y)]_omega in H_omega`,
a unit vector for the normalized Hilbert--Schmidt norm.

- *Coefficients.* For `k in K`, `V_n(k)V_n(y)V_n(k)^*V_n(y)^*` is within
  `o(1)` in operator norm of `V_n([k,y])`. Since `[k,y] in <K,y>`, (K3) gives

  ```text
  <pi_omega(sigma~(k))eta,eta> = lim_omega tr V_n([k,y]) = 1_(C_K(y))(k).
  ```

- *Fixed by `N`.* Let `n in N` and `k in K`, and put `n'=k^(-1)nk in N` by (K1).
  Then `pi_omega sigma~(n) pi_omega sigma~(k) eta = pi_omega sigma~(k)
  [V_n(n')V_n(y)V_n(n')^*]`. This equals `pi_omega sigma~(k) eta`, because
  `n'yn'^(-1)=y` by (K2) and asymptotic multiplicativity holds in operator norm.
- So the cyclic subspace of `eta` under `sigma~(K)` lies in `H_1=Fix(N)`.
  By uniqueness of the GNS construction it carries `lambda_(K/C_K(y))`.
- Writing `sigma_1`, `sigma_2` for the representations of `C*(K)` given by
  `pi o Sigma` restricted to `H_1` and `H_2`, we get

  ```text
  ker sigma_1  subset  ker lambda_(K/C_K(y)).                      (E1)
  ```

  Both subspaces reduce `sigma~(K)` because `N` is normal in `K`.
  Here `H_omega` is a summand of `H_B` that reduces `B`. So
  `Fix(N) cap H_omega` is the `H_omega` part of `H_1`.

## Step 2: the trace sees lambda_K

Let `tau = lim_omega tr` on `B`. Normalized traces vanish on sequences
whose norm tends to zero, so `tau` is a tracial state on `B`. Moreover
`tau(sigma~(k)) = lim_omega |tr V_n(k)|^2 = delta_e(k)` for `k in K`, by (K3).

Let `(pi_tau, L^2(B,tau), xi)` be the GNS triple and put `M=pi_tau(B)''`.
- *The vector state is tracial and faithful on `M`.* It is tracial on
  `pi_tau(B)` and extends to `M` by weak continuity.
  - If `x in M` and `x xi=0`, then for `w in M`
    `||x w xi||^2 = <w^*x^*xw xi,xi> = <x w w^* x^* xi,xi> <= ||w||^2 <x x^* xi,xi>`.
  - By traciality the right side is `||w||^2 ||x xi||^2 = 0`.
  - Since `xi` is cyclic for `M`, `x=0`.
- Put `M_K=pi_tau(A_K)''` and `L_xi = closure(M_K xi)`. The state
  `phi=<.xi,xi>` is a faithful normal trace on `M_K`.
  - So `M_K` acts faithfully on `L_xi`: if `x|L_xi=0` then `x xi=0`, so `x=0`.
  - `M_K` is the strong closure of `span pi_tau sigma~(K)`, so `xi` is cyclic
    for `pi_tau sigma~(K)` on `L_xi`.
  - The coefficient there is `delta_e`, so this representation is `lambda_K`.
- Hence, for `x in C*(K)`:
  `lambda_K(x)=0` iff `pi_tau Sigma(x)|L_xi=0` iff `pi_tau Sigma(x)=0`. So

  ```text
  ker(pi_tau o Sigma) = ker lambda_K,     pi_tau(A_K) = C*_r(K)  via u_k -> lambda_K(k).   (E2)
  ```

## Step 3: if P_N in A_K, the trace kills P_N and lives on H_2

Assume `P_N in A_K`.
- *`P_N` is central in `A_K`.* `N` is normal in `K`, so `H_1` reduces every
  `pi sigma~(k)`, and `P_N` commutes with `sigma~(K)`.
- *`pi_tau(P_N)=0`.* Let `p` be the image of `pi_tau(P_N)` in `C*_r(K)` under (E2).
  - Since `sigma~(n)P_N=P_N` for `n in N`, we get `lambda_K(n)p=p`, so the range
    of `p` consists of left-`N`-invariant vectors of `l^2(K)`.
  - Such a vector is constant on each coset `Nk`. These cosets are infinite
    by (K1), so the vector is `0`.
  - Hence `p=0` and `pi_tau(P_N)=0`.
- *`lambda_K << sigma_2`.* Let `x in C*(K)` with `sigma_2(x)=0`.
  - Then `Sigma(x)(1-P_N)` acts as zero on `H_1` and on `H_2`, so it is `0` in `B`.
  - So `Sigma(x)=Sigma(x)P_N` and `pi_tau Sigma(x) = pi_tau Sigma(x) pi_tau(P_N) = 0`.
  - By (E2), `lambda_K(x)=0`. Thus

  ```text
  ker sigma_2  subset  ker lambda_K  subset  ker lambda_(K/C_K(y)),     (E3)
  ```

  where the second inclusion is Lemma Q together with (K2).

## Step 4: the contradiction

Choose `p in C*(K)` with `Sigma(p)=P_N`. Then:
- `sigma_1(1-p)=0`, because `P_N` is the identity on `H_1`;
- `sigma_2(p)=0`, because `P_N` vanishes on `H_2`.

By (E1) and (E3), both `1-p` and `p` lie in `ker lambda_(K/C_K(y))`.
Hence `1` does too. That is absurd, since `lambda_(K/C_K(y))` is a nonzero
unital representation. So `P_N notin A_K`. `QED`

*Remark (what the argument does not reach).*
- If only `P_N in B` is assumed, Step 3 still gives `pi_tau(P_N)=0`: use the
  trace-preserving conditional expectation onto `M_K`, which is an
  `M_K`-bimodule map.
- But nothing forces `ker sigma_1 + ker sigma_2 = A_K`, and the argument stops there.
- Elements of `B` outside every such `A_K` are untouched.

## Step 5: facts about the Jacobson ring J

Let `J=F_2<S,T|TS=1>`, `Q=1-ST`, and `V=F_2^(N)` with basis `e_0,e_1,...`.

- *Normal form and a faithful action.* Using `TS=1`, every word reduces to
  some `S^aT^b` with `a,b>=0`. Let `S e_k=e_(k+1)`, `T e_(k+1)=e_k`, `T e_0=0`.
  - Then `S^aT^b e_k = e_(k-b+a)` for `k>=b`, and `S^aT^b e_k = 0` for `k<b`.
  - Suppose `sum c_(ab) S^aT^b = 0` with some `c_(ab)` nonzero. Let `b_0` be the
    least `b` with some `c_(ab)!=0`, and apply the sum to `e_(b_0)`. This gives
    `sum_a c_(a b_0) e_a = 0`, a contradiction.
  - So the `S^aT^b` form a basis of `J`, and `J` acts faithfully on `V`.
- *Matrix units.* `Q` is the projection onto `F_2 e_0`. Put `e_ij=S^iQT^j`.
  - `e_ij` sends `e_j` to `e_i` and kills the other basis vectors.
  - `I=span{e_ij}` is the ideal of finite-rank elements. It is the ideal
    generated by `Q`, because `TQ=0=QS`.
  - `J/I = F_2[z,z^(-1)]` via `S->z`, `T->z^(-1)`: modulo `Q` we have `ST=1=TS`.
- *Every nonzero ideal contains `I`.* Let `x!=0`. By faithfulness some
  `x e_k` has coefficient `1` at some `e_i`. Then `e_(0i) x e_(k0) = e_00 = Q`,
  so the ideal contains `Q` and hence `I`.
- *`J` embeds in `L=L_(F_2)(1,2)`.* The map `S->s_1`, `T->t_1` respects
  `t_1s_1=1` and sends `Q` to `1-s_1t_1=s_2t_2`. This is nonzero, since
  `t_2(s_2t_2)s_2=1`. The kernel is an ideal not containing `Q`, so it is `0`.
- *Units of `J` are locally finite.* Let `d in U(J)`.
  - Its image in `F_2[z^(+-1)]` is a unit, so it equals `z^k` for some `k`.
  - As an operator on `V`, `d` equals `S^k` (or `T^(-k)` if `k<0`) plus a
    finite-rank operator. Algebraic Fredholm index is invariant under
    finite-rank perturbation, and `S^k` has index `-k`.
  - `d` is invertible on `V`, so it has index `0`, hence `k=0` and `d in 1+I`.
  - Choose `m` so that `d-1` and `d^(-1)-1` lie in `span{e_ij : i,j<m}`. Then `d`
    fixes `e_k` for `k>=m` and is invertible on `span{e_0,...,e_(m-1)}`.
  - Hence `U(J) = union_m GL_m(F_2)`, a directed union of finite groups. It is
    locally finite, so amenable.

## Step 6: the root column satisfies (K1)-(K3)

Let `G=St_n(J)` with `n>=5`. For `Delta=St_20(L)`, apply the homomorphism
`phi:St_5(J)->St_20(L)` induced by `J subset L` and the corner inclusion, and
read every statement below for the images. Write `pi:G->E_n` for the map to
matrices. By `steinberg-group-homology-gives-k2-and-k3` (ii), `ker pi` is
central, since `G` is the universal central extension of `E_n`.

Recall the Steinberg relation `[x_ij(a),x_kl(b)]=1` for `j!=k` and `i!=l`, and
`[x_ij(a),x_jl(b)]=x_il(ab)` for `i!=l`.

- *(K1).* `x_13` and `x_23` commute, so `a,b -> x_13(a)x_23(b)` maps `J^2` onto
  `N`. Composing with `pi` gives the injective map
  `(a,b) -> [[1,0,a],[0,1,b],[0,0,1]]`, which stays injective over `L`
  because `J subset L`. So `N` is isomorphic to `J^2` and is infinite.
  `N` is normal in `K`:
  - `x_12(a)` commutes with `x_13`, and `x_12(a)x_23(b)x_12(-a)=x_13(ab)x_23(b)`;
  - `x_21(a)` commutes with `x_23`, and `x_21(a)x_13(b)x_21(-a)=x_23(ab)x_13(b)`.
- *(K2), first half.* `y=x_14(1)` commutes with `x_13(a)` and with `x_23(b)`, by
  the first relation.
- *(K3).* In a `delta_e`-profile model, `tr V_n(g)->0` for every `g!=e` in `G`.

**Lemma C (the y-centralizer is amenable).** `C_K(y)` is amenable.

*Proof.*
- *Matrix shape of `K`.* `pi(K)` is generated by `e_12(a)`, `e_21(a)`,
  `e_13(a)` and `e_23(b)`, all with entries in `J`. So every `g in pi(K)` is
  `diag([[A,v],[0,1]],1_(n-3))` with `A in EL_2(J)` and `v in J^2`.
- *Centralizing `e_14(1)`.* For such `g`,
  `g e_14(1) g^(-1) = 1 + (g e_1)(e_4^T g^(-1)) = 1 + (g e_1) e_4^T`, because
  row `4` of `g^(-1)` is `e_4^T`. So `g` commutes with `e_14(1)` iff `g e_1 = e_1`,
  that is, iff `A e_1 = e_1`.
- *The stabilizer.* Let `H={A in GL_2(J) : A e_1=e_1}`. Each `A in H` is
  `[[1,b],[0,d]]`, and so is `A^(-1) = [[1,b'],[0,d']]`.
  - Multiplying out, `dd' = d'd = 1`, so `d in U(J)`.
  - `A -> d` is a homomorphism, since
    `[[1,b],[0,d]][[1,b'],[0,d']] = [[1,b'+bd'],[0,dd']]`.
  - Its kernel `{[[1,b],[0,1]]}` is abelian.
  - So `H` is abelian-by-(subgroup of `U(J)`), and it is amenable by Step 5.
- *Assembling.* `pi(C_K(y))` lies in `H x| J^2`, which is amenable, being an
  extension of `H` by the abelian `J^2`. Also `C_K(y) cap ker pi` is central.
  So `C_K(y)` is abelian-by-amenable, hence amenable.
  - The same computation holds in `E_20(L)`, because the entries stay in
    `J`.
  - `A^(-1)` has entries in `J`, because it is a product of elementary
    matrices over `J`. `QED`

## Step 7: the column carries the certificate (item 2)

Take `u`, `c` from `lem:ring-compression-cell` with `R=J`, `s=S`, `t=T`, `e=Q`.
Read them as the same words in the `x_ij`, inside `St_4(J) subset G`.

**Central-error principle.** Suppose `g in G` and `pi(g)e_ij(a)pi(g)^(-1)=e_ij(f(a))`.
Then `g x_ij(a) g^(-1) = x_ij(f(a)) z` for some central `z`, and central factors
drop out of commutators.

- *`uNu^(-1)<=N`.*
  - `x_13(a)=[x_12(a),x_23(1)]`, and `(eq:intertwine)` gives
    `u x_13(a) u^(-1) = [x_12(SaT),x_23(ST)] = x_13(SaTST) = x_13(SaT)`.
  - Likewise `x_23(b)=[x_21(b),x_13(1)]` gives `u x_23(b) u^(-1) = x_23(SbT)`.
- *`c in C_G(N)`.* `pi(c)=diag(1,1,1,1+QT)` commutes with `e_12`, `e_21`,
  `e_13` and `e_23`. The same two commutator identities then give
  `c x_13(a) c^(-1) = x_13(a)` and `c x_23(b) c^(-1) = x_23(b)` exactly.
- *The head.* `ucu^(-1) = x_12(Q) z` with `z` central. So
  `[ucu^(-1), x_23(1)] = [x_12(Q), x_23(1)] = x_13(Q) = w`, and `x_23(1) in N`.

So `w in D_G(N)`, the compression defect of the amenable group
`N = J^2`. Applying `phi` transports all three facts to `Delta`.

## Step 8: transport from P_N in B alone (item 3)

Assume `P_N in B` and lift it to projections `P_n` on `(M_(d_n),||.||_2)`.

- *Characterization of `C_2(V,N)`.* Let `(x_n)` be HS-bounded. Then
  `||Ad V_n(l)x_n-x_n||_2 -> 0` iff it tends to `0` along every free
  ultrafilter `omega`.
  - Along `omega`, this says `[x_n]_omega in Fix pi_omega sigma~(l)`.
  - `pi_omega(P_N)` is the projection onto `Fix(N) cap H_omega`.
  - Hence `(x_n) in C_2(V,N)` iff `lim_omega ||P_n x_n - x_n||_2 = 0` for every
    `omega`, iff `||P_n x_n - x_n||_2 -> 0`.
  - This replaces the first half of the proof of `thm:transport`.
- *Order.* Put `U=sigma~(u)`. Since `unu^(-1) in N` for `n in N`, the argument of
  `lem:kazhdan-projection-order` gives `U^*Fix(N) subset Fix(N)`, so
  `U^*P_NU <= P_N`.
- *Equality.* `B` is a norm matrix corona, so `lem:stable-finite` gives
  `U^*P_NU = P_N`.
- *Conclusion.* From here the rest of the proof of `thm:transport`, and the
  proof of `cor:defect-hs`, apply verbatim with `L:=N`. Step 7 gives
  `||V_n(w)-1||_2 -> 0` for every operator-norm model.

Property `(T)` enters only through `P_N in B`. The passage from HS to operator
norm is not given here. The manuscript obtains it from `thm:normal-kazhdan`.

## Step 9: relative (T) and averages cannot supply P_N (item 4)

- *They land in `A_K`.* Take any element built from `sigma~|K`:
  - an image of `C*_max(K)`;
  - a continuous function of `sigma~(h)` for `h in C[K]`;
  - a norm limit of averages over finite subsets of `N`.

  Each of these lies in `A_K`. Relative `(T)` of `(K,N)`
  (`elementary-linear-semidir-pair-relative-t`) is a statement about
  representations of `K`, so whatever it yields in `B` is of this form. By
  Steps 1-6, no such element is `P_N`.
- *No relative Kazhdan projection exists at all.* No projection
  `p in C*_max(K)` maps to the `Fix(N)` projection in every representation.
  - By Lemma Q with `C=N` (amenable), `lambda_(K/N) << lambda_K`.
  - But such a `p` would satisfy `lambda_(K/N)(p)=1` and `lambda_K(p)=0`, since
    `N` is infinite.

  So relative `(T)` gives only the quantitative almost-invariance inequality.
  Transport needs a projection, and in `delta_e`-profile models that
  projection cannot come from `A_K`.
