---
rg: 2
id: leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity
kind: claim
title: Trace certificates against the Toeplitz corner survivors are exactly hyperlinearity of EL_20(J)
distinct_from:
  leavitt-corner-bcs-support-coefficient-gate: that proves every hyperlinear quotient of the support group kills z; this upgrades it to every Connes-embeddable character (including sign characters), and then proves that on the Toeplitz survivor class any such trace certificate is equivalent to faithful hyperlinearity of EL_20(J), so no non-regular trace is a weaker target.
  character-diracization-limit: that computes the pointwise limit of |tau|^(2k) for an arbitrary character; this applies that limit to Jacobson elementary groups, where C_E(L)=1 and perfectness of L force the scalar kernel to be trivial.
  diracization-gap-equals-nonhyperlinear-group: that grades a power-uniform gap for non-embeddable traces; this is about embeddable traces as certificates of impossibility, and has no gap hypothesis.
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that uses the canonical group trace, which is faithful; this uses arbitrary embeddable characters, which need only charge the corner projection.
  binary-jacobson-head-retaining-homomorphisms-are-faithful: that is the all-or-nothing statement for homomorphisms of EL_5(J); this is the all-or-nothing statement for embeddable traces of EL_n(J), n>=2, and needs the sign case handled by perfectness of the finitary kernel.
  binary-jacobson-el3-is-sofic: that asks for sofic approximations of EL_3(J); this identifies hyperlinearity of EL_20(J) as the exact decision point for the Toeplitz class of the Leavitt corner diagram, and EL_3 soficity does not decide it.
artifacts:
  - research/leavitt-corner-trace-gate-jacobson-proof.md
---

**ESTABLISHED (obstruction to a class of approaches, and exact decomposition).**

**Setup.**
* `B_loop`, `R=L_(F_2)(1,2)`, `Delta=St_20(R)`, `pi:Delta->E_20(R)`, `q=s_1t_1`, `z=x_13(q)`, `P_z=(1-z)/2` are as in
  `agent-leavitt-not-bcs-negative-root-corner`.
* `J=F_2<S,T | TS=1>`, `Q=1-ST`, and `E_n=EL_n(J)` acting on `V_n=F_2^(N x {1..n})` (finitely supported vectors).
* `L_n=GL_fin(N x {1..n},F_2)`.
* A character `tau` of a countable group `Gamma` is *CE* if it has matricial microstates: for every finite `F` and
  `eps>0` there are `d` and `U:F->U(d)` with `||U_gU_h-U_(gh)||_2<eps` and `|tr U_g-tau(g)|<eps` for `g,h in F`.
  Genuine homomorphisms are not required.

**Theorem TG (trace gate).** Let `Phi:A(B_loop)->P_z C[Delta] P_z` be a unital star homomorphism (`LNC3`), let `X` be
its support and `Gamma_X=<X,z>`. Then every CE character `tau` of `Gamma_X` satisfies `tau(z)=1`.

This strengthens the hyperlinear shadow gate of `leavitt-corner-bcs-support-coefficient-gate`. The gate is the case
`tau=1_N` for a normal subgroup `N` with `Gamma_X/N` hyperlinear. The strengthening also forbids CE characters with
`tau(z)=-1`, i.e. projective sign models.

**Theorem JH (all-or-nothing for Jacobson elementary groups).** Let `n>=2`, `E=E_n`, `L=L_n`, and `w in L\{1}`. The
following are equivalent:

1. `E` is hyperlinear;
2. `E` has a hyperlinear quotient in which `w` survives;
3. `E` has a CE character `tau` with `tau(w)!=1`.

More precisely, for any CE character `tau` of `E` exactly one of the following holds:

```text
(a)  tau|_L == 1   and tau factors through the symbol quotient E/L;
(b)  the scalar kernel K_tau={g : |tau(g)|=1} is trivial, and E is hyperlinear.     (JH1)
```

In particular, if `E` is not hyperlinear, then every CE character of `E` factors through `E/L`, which is the Laurent
elementary group `EL_n(F_2[x,x^(-1)])`.

**The Haar fixed-point characters (the natural candidates, recorded as members of the class).**
* `E` acts on the compact group `Y=F_2^(N x {1..n})` by Haar-preserving automorphisms.
* For `k>=1` put `phi_k(g)=mu^k(Fix_(Y^k)(g))`. This is a character of `E` with

```text
phi_k(g) = 2^(-k rank(g-1))   (g in L),        phi_k(g) = 0   (g notin L).             (JH2)
```

So `phi_k(x_13(Q))=2^(-k)`, `K_(phi_k)=1`, and `phi_k` is Skudlarek's character of `L` extended by zero.
Consequently

```text
phi_k is CE for some k   ==>   EL_n(J) is hyperlinear.                               (JH3)
```

The converse is not asserted.

**Corollary (the Toeplitz survivor class of LNC3).**
* Let `T_2=F_2<s_2,t_2> <= R`. By `prime-characteristic-defect-embeds-the-jacobson-algebra`, `T_2 ≅ J` via
  `S->s_2, T->t_2`, and `q=1-s_2t_2` corresponds to `Q`.
* Call a support `X` *elementary Toeplitz* if `pi(Gamma_X) <= E_20(T_2) ≅ EL_20(J)`.

For elementary Toeplitz supports:

1. **(kill direction)** If `EL_20(J)` is hyperlinear, no `LNC3` has elementary Toeplitz support. One CE character of
   `EL_20(J)` with `tau(x_13(Q))!=1`, for instance `phi_k`, kills all such supports at once, by pulling back along `pi`.
2. **(construct direction)** An `LNC3` with elementary Toeplitz support makes `EL_20(J)` nonhyperlinear.
3. **(no weaker certificate)** Any trace certificate for the kill direction that is defined on `EL_20(J)` already
   implies that `EL_20(J)` is hyperlinear. This covers Haar fixed-point characters, invariant-random-subgroup
   characters, Skudlarek-type rank characters extended by zero, sign characters, and any CE character with `tau(z)!=1`.

So the "next falsifiable step" recorded on the target, whether `E_20(T_2)` has a hyperlinear quotient *or model* in
which `x_13(1-s_2t_2)` survives, is exactly the question whether `EL_20(J)` is hyperlinear. Nothing in between exists.

**Where the class dies.** Every non-regular trace approach is pushed through Diracization,
`|tau|^(2k) -> 1_(K_tau)` (`character-diracization-limit`). The invariant is the scalar kernel `K_tau`.
* **Non-sign case.** If `K_tau` meets the simple group `L` trivially, then `C_E(L)=1` forces `K_tau=1`, and the limit
  is the regular character `delta_e`.
* **Sign case.** If `K_tau` meets `L` nontrivially, it contains `L`. Perfectness of `L` makes the scalar homomorphism
  trivial on `L`, so `tau|_L == 1`. A sign or phase certificate with `tau(w) in T\{1}` therefore cannot exist.

So a trace certificate carries exactly the information "E is hyperlinear" and nothing weaker.

**Context.** `EL_20(J)` contains `EL_5(J)`.
* It is Kazhdan (the Ershov--Jaikin-Zapirain theorem imported in `steinberg-finite-presentation-and-kazhdan-theorem`)
  and not LEF (`cohn-elementary-group-is-not-lef`).
* It is not MF, because MF passes to subgroups and `binary-jacobson-steinberg-head-root-is-mf-invisible` kills the head
  in every norm-corona model of `EL_5(J)`.
* Its hyperlinearity is open. It is an amenable-by-linear group, the extension direction for which no permanence
  theorem is available.

Proof: [[leavitt-corner-trace-gate-jacobson-proof]].
