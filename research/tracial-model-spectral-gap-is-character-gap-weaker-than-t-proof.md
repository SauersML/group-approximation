---
rg: 2
id: tracial-model-spectral-gap-is-character-gap-weaker-than-t-proof
kind: route
title: Push every finite representation into the GNS space of its trace, read V's spectrum from its two characters, and play ping-pong on the Cantor set
target: tracial-model-spectral-gap-is-character-gap-weaker-than-t
requires:
  - thompson-v-character-simplex
  - thompson-v-has-haagerup-property
  - thompson-v-finitely-presented-infinite-simple
  - kesten-spectral-gap-replaces-kazhdan-projection-per-model
---

Notation is that of the target.  Throughout, `y=rho(h_S)` is a
self-adjoint contraction.  Two standard facts are used:
- spectra of self-adjoint elements shrink under unital `*`-homomorphisms
  and are unchanged under faithful ones;
- an isolated point of the spectrum of a self-adjoint operator is an
  eigenvalue.

The inputs from the required claims are:
- `thompson-v-character-simplex`: every character of `V` is
  `t tau_reg+(1-t)tau_triv`;
- `thompson-v-has-haagerup-property`: every Kazhdan subgroup of `V` is
  finite;
- `kesten-spectral-gap-replaces-kazhdan-projection-per-model`, item 5: the
  GNS representation of `tau` on the adjoint algebra of a `delta_e`-profile
  model is the regular one.

## Step 1: finite representations are controlled by characters

**Lemma A.**  Let `rho:G->U(M)` with `M` a finite von Neumann algebra,
and let `N=rho(G)''`.  Then `sp(rho(h_S))` lies in the closure of the
union of `sp(pi_phi(h_S))` over the characters `phi=tau o rho`, where
`tau` runs over the normal tracial states of `N`.  If `N` has a faithful
normal tracial state `tau`, then `sp(rho(h_S))=sp(pi_(tau o rho)(h_S))`.

*Proof.*
- *Spectral permanence.*  `sp_M(y)=sp_N(y)`, because `N` is a unital
  C-star subalgebra of `M`.
- *A separating family of traces.*  `N` is finite.  By the center-valued
  trace, the normal tracial states of `N` separate points.  Let
  `{tau_i}` be such a family.  The direct sum of the GNS representations
  `pi_(tau_i)` is faithful on `N`, so
  `sp_N(y)=closure union_i sp(pi_(tau_i)(y))`.
- *Each GNS space is a character representation.*  Fix `tau=tau_i` and
  put `phi=tau o rho`.  It is positive definite, normalized and constant
  on conjugacy classes, so it is a character of `G`.  In `L^2(N,tau)`
  the vector `xi=1^` is cyclic for `pi_tau(N)`.  Since `N` is the
  strong-operator closure of `span rho(G)`, the set `N xi` lies in the
  closure of `span pi_tau(rho(G)) xi`.  So `xi` is cyclic for
  `pi_tau o rho`, whose coefficient at `xi` is `phi`.  By uniqueness of GNS,
  `pi_tau o rho = pi_phi` as representations of `G`.  Extending linearly,
  `pi_tau(y)=pi_phi(h_S)`.
- The spectra of the `pi_(tau_i)(y)` are therefore spectra of character
  representations.  If one `tau` is faithful, the family `{tau}` already
  separates points, which gives the equality.  `QED`

**Lemma B.**  For every character `phi`, the operator `pi_phi(h_S)` lies
in a finite von Neumann algebra image of `G`.

*Proof.*  Put `N=pi_phi(G)''` on the GNS space with cyclic vector `xi`.
- *The vector state is a trace on `N`.*  It is tracial on `span pi_phi(G)`
  because `phi` is conjugation invariant, and it extends to `N` by
  strong continuity.
- *The vector state is faithful on `N`.*  If `tau(x^*x)=0` then
  `x xi=0`.  For every `w in N`,

  ```text
  ||x w xi||^2 = tau(w^* x^* x w) = tau(x w w^* x^*) <= ||w||^2 tau(x x^*) = ||w||^2 tau(x^* x) = 0.
  ```

  Since `xi` is cyclic, `x=0`.
- So `N` carries a faithful normal tracial state and is finite.  `QED`

## Step 2: proof of item 1 (character form)

*`(CG)` implies `(TMSG)`.*  Let `rho:G->U(M)` be a finite representation.
By Lemma A, every point of `sp(rho(h_S))` is a limit of points of the
sets `sp(pi_phi(h_S))`.  By `(CG)` those sets miss `(1-c,1)`, so their
closed union misses `(1-c,1)`.  Hence `1` is not an accumulation point.

*`(TMSG)` implies `(CG)`.*  Suppose `(CG)` fails for every `c>0`.
- *Choice.*  For each `n` choose a character `phi_n` and a point
  `lambda_n in sp(pi_(phi_n)(h_S)) cap (1-1/n,1)`.
- *The product representation.*  By Lemma B, `N_n=pi_(phi_n)(G)''` is
  finite.  The `l^infty` product `M=prod_n N_n` is a finite von Neumann
  algebra: the product of the faithful normal traces of the factors,
  weighted by `2^-n`, is faithful and normal.  Let `rho=(pi_(phi_n))_n`.
- *Spectrum.*  `sp_M(rho(h_S))` contains every `lambda_n`.  These are
  distinct from `1` and converge to `1`.
- So `1` is an accumulation point, and `(TMSG)` fails.  `QED`

## Step 3: a free subgroup of V by ping-pong

`V` acts on the Cantor set `C={0,1}^N` by prefix replacement.  Take two
complete prefix codes `(w_1,...,w_k)` and `(w'_1,...,w'_k)` with the same
number of words.  The map `w_i u -> w'_i u` is an element of `V`.  Write
`[w]` for the cylinder of `w`.

**Lemma C.**  If `E,F subset C` are clopen, nonempty and proper, some
`g in V` has `g(E)=F` and `g(C\E)=C\F`.

*Proof.*
- Each of the four sets `E`, `C\E`, `F`, `C\F` is a finite disjoint union
  of cylinders, and none is empty.
- Splitting `[w]=[w0] union [w1]` raises a count by one.  So we may
  assume `E` and `F` use the same number `k` of cylinders, and `C\E` and
  `C\F` the same number `m`.
- Matching cylinders of `E` with those of `F`, and those of `C\E` with
  those of `C\F`, gives an element of `V`.  `QED`

**Ping-pong.**
- *The two generators.*  Put `A+=[00]`, `A-=[01]`, `B+=[10]`, `B-=[11]`.
  By Lemma C choose `a in V` with `a(C\A-)=A+`, so that
  `a^-1(C\A+)=A-`.  Choose `b in V` with `b(C\B-)=B+`, so that
  `b^-1(C\B+)=B-`.
- *Powers of `a`.*  Since `A+ subset C\A-`, induction gives
  `a^n(C\A-) subset A+` and `a^-n(C\A+) subset A-` for `n>=1`.
- *The ping-pong inclusions.*  Put `X_a=[0]` and `X_b=[1]`.  Every
  nonzero power of `a` maps `X_b` into `A+ union A- = X_a`.  Likewise every
  nonzero power of `b` maps `X_a` into `X_b`.
- *No relation.*  Let `w` be a nontrivial reduced word in `a,b`.  If `w`
  is a nonzero power of `b`, it maps `X_a` into `X_b` and is not the
  identity.  Otherwise, conjugating by a suitable power of `a` gives a reduced word that starts
  and ends with nonzero powers of `a`.  Such a word maps `X_b` into
  `X_a`, which is disjoint from `X_b`, so it is not the identity.
- Hence `F=<a,b>` is free of rank two.  In particular `V` is nonamenable
  and finitely generated subgroups of `V` containing `F` are nonamenable.

## Step 4: proof of item 2

- *Characters of `V`.*  By `thompson-v-character-simplex`, every character
  of `V` is `phi=t tau_reg+(1-t) tau_triv`.  Its GNS representation is
  the cyclic subrepresentation of `lambda_V (+) 1_V` generated by
  `(sqrt(t) delta_e, sqrt(1-t) 1)`.  So `pi_phi <= lambda_V (+) 1_V`.
- *Restriction to `L`.*  For `L<=V`, `l^2(V)` is the direct sum over the
  cosets `Lg` of `l^2(Lg)`.  Each summand is `lambda_L`.  Hence

  ```text
  sp(pi_phi(h_S)) subset sp(lambda_L(h_S)) union {1}
                  subset [-1, rho_S] union {1},   rho_S=||lambda_L(h_S)||.
  ```

- *Kesten's theorem.*  For a symmetric probability measure whose support
  generates `L`, `||lambda_L(mu)||=1` if and only if `L` is amenable
  (H. Kesten, *Full Banach mean values on countable groups*, Math. Scand. 7
  (1959), 146--156).  For `L=F`, and for `L=V` with any finite generating
  set (`V` is finitely generated by `thompson-v-finitely-presented-infinite-simple`),
  `L` is nonamenable by Step 3, so `rho_S<1`.
- *Conclusion.*  `(CG)` holds with `c=1-rho_S`, so Step 2 gives `(TMSG)`
  for `(V,V)` and `(V,F)`.
- *No property `(T)`.*  By `thompson-v-has-haagerup-property`, every
  Kazhdan subgroup of `V` is finite.  `V` and `F` are infinite.  `QED`

## Step 5: proof of item 3

- *Setup.*  Let `F_2=<a,b>` with `S={e,a^(+-1),b^(+-1)}`.  For `n>=2` let
  `q_n:F_2->Z/n` send `a->1` and `b->0`, and compose with the regular
  representation of `Z/n` on `C^n`.
- *Eigenvalues.*  The characters `chi_k` of `Z/n` are eigenvectors of
  `h_S` with eigenvalue `(3+2cos(2 pi k/n))/5`.  For `k=1` this lies in
  `(1-c_n,1)` with `c_n->0`.
- *Product representation.*  The direct product representation into
  `prod_n M_n`, a finite von Neumann algebra, therefore has spectrum
  accumulating at `1`.
- *Comparison.*  Step 3 embeds the same `F_2` in `V`, and Step 4 gives
  `(TMSG)` for `(V,F_2)`.  `QED`

## Step 6: proof of item 4

- *Setup.*  Let `V_n in U(d_n)^G` be `delta_e`-profile,
  `tr V_n(g)->delta_e(g)`.  The adjoint unitaries are
  `Ad V_n(g)=V_n(g) (x) conj(V_n(g))`, with normalized traces
  `|tr V_n(g)|^2`.  Let `tau=lim_omega tr` on the corona `B`.  It vanishes
  on the null ideal, so it is a trace on `B`, and
  `tau(sigma~(g))=delta_e(g)`.
- *The completion is finite.*  In `L^2(B,tau)` the vector `xi=1^` is
  cyclic for `pi_tau(B)`, and its vector state is tracial.  The argument of
  Lemma B shows that this state is faithful on `pi_tau(B)''`.  So
  `N=pi_tau(sigma~(G))''` carries the faithful normal trace `xi`, whose
  composite with `pi_tau o sigma~` is `delta_e`.
- *Spectrum.*  By Lemma A with that faithful trace,

  ```text
  sp(pi_tau(y)) = sp(pi_(delta_e)(h_S)) = sp(lambda_G(h_S)) = sp(lambda_L(h_S))
                subset [-1, ||lambda_L(h_S)||],
  ```

  where `y=sigma~(h_S)`.  The middle equality uses the coset decomposition
  of Step 4.  Spectral permanence in `B(L^2(B,tau))` shows this is the
  spectrum of `pi_tau(y)` as an operator.
- *The projection is null.*  If `(MSG)` holds for `sigma~` on `L`, then
  `P=chi_{1}(y)` is a continuous function of `y`, and
  `pi_tau(P)=chi_{1}(pi_tau(y))=0` because `1` is not in
  `sp(pi_tau(y))`.  Hence `tau(P)=<pi_tau(P)xi,xi>=0`.  `QED`

This is item 5 of `kesten-spectral-gap-replaces-kazhdan-projection-per-model`
seen from the whole corona instead of from `A_L`.  No part of Steps 1--6
uses property `(T)` or a Kazhdan projection.
