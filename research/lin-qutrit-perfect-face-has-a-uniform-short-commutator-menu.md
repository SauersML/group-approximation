---
rg: 2
id: lin-qutrit-perfect-face-has-a-uniform-short-commutator-menu
kind: claim
title: The Lin qutrit perfect face has a fixed uniformly nontrivial menu of length-four commutator words
artifacts:
  - research/lin-qutrit-short-commutator-menu-proof.md
distinct_from:
  lin-perfect-face-forces-qutrit-offdiagonal-three-corner-row: that obtains a positive off-diagonal qutrit coefficient as a linear combination of 27 clock words; this turns the same commutator floor into a fixed menu of individual length-four words by adjoining the literal Boolean reflections.
  lin-loss-is-a-three-corner-full-c-fourier-coefficient: those losing coefficients vanish on the perfect face and become positive in sound models; the words here are uniformly nontrivial inside every perfect trace.
  common-naimark-context-transport-is-an-inner-full-c-gauge: that proves the canonical amplified transport is Morita-neutral; this is a source-algebra certificate before any transport or raw return is chosen.
  positive-one3-global-clock-is-z3-lcs-plus-unary-sector: that audits the clause clock and the unary Boolean sector; this quantifies their unavoidable cross-context noncommutativity and isolates the still-additive cross-typing gate.
---

**ESTABLISHED SOURCE WORD CERTIFICATE; THE CROSS-TYPING IDENTITY IS
STILL ADDITIVE, SO THIS IS NOT A GROUPIFICATION THEOREM.**

Use the audited positive-ONE3 output `B_13` of the Lin perfect-face route.
For every clause `c`, its three allowed assignments give a PVM

```text
p_(c,0)+p_(c,1)+p_(c,2)=1.
```

Put

```text
C=|Clauses(B_13)|,                    N=3C,
K_13(tau)=N^(-2) sum_(i,j) ||[p_i,p_j]||_(2,tau)^2.    (SC1)
```

The sum is over all ordered clause atoms. The perfect trace space is
nonempty and compact, has no character, and therefore has the uniform
floor

```text
kappa_13=min_(perfect tau) K_13(tau)>0.                 (SC2)
```

Let `omega=exp(2 pi i/3)`. For a clause `c` and an arbitrary clause atom
`j=(d,b)`, define two actual unitaries in the perfect algebra:

```text
u_c=sum_(a=0)^2 omega^a p_(c,a),
v_j=1-2p_j.                                             (SC3)
```

Thus `u_c^3=v_j^2=1`. Form the ordinary length-four group word

```text
w_(c,j)=u_c v_j u_c^(-1) v_j.                           (SC4)
```

The fixed menu has `CN=N^2/3` entries. In every perfect trace it obeys
the exact identity

```text
(1/(CN)) sum_(c,j) ||w_(c,j)-1||_2^2
       =18 K_13(tau)
       >=18 kappa_13.                                   (SC5)
```

In particular at least one menu word has

```text
tau((w-1)^*(w-1))>=delta_w,          delta_w=18kappa_13. (SC6)
```

The selected word can depend on the trace. Since every unitary defect is
at most four, `(SC5)` also gives the consistency bound
`0<delta_w<=4`. For the selected word, the spectral projection

```text
R=1_[delta_w/2,4]((w-1)^*(w-1))
```

satisfies

```text
tau(R)>=delta_w/(8-delta_w),
(w-1)^*(w-1)R>=(delta_w/2)R.                            (SC7)
```

The same Boolean-reflection alphabet shortens the earlier off-diagonal
three-corner coefficient. If `a'!=a`, then

```text
D_(c,a;j;a')=p_(c,a)p_jp_(c,a')
 =-(1/18) sum_(r,t=0)^2
     omega^(-ar-a't) u_c^r v_j u_c^t.                  (SC8)
```

So `D` is an at-most-nine-word full-complex coefficient, rather than the
27-clock-word expansion obtained by also Fourier-expanding `p_j`. Its
exact off-diagonal type remains

```text
u_cD=omega^aD,                    Du_c=omega^(a')D.      (SC9)
```

The normalized three-corner row still has energy `K_13/4`. Consequently
`(SC5)` and `(SC8)` expose, in the same fixed finite alphabet, both an
individual ordinary word defect and a positive off-diagonal full-complex
coefficient.

The result is robust after the relation weights are normalized. For a
fixed positive relation-defect menu, set

```text
W=sum_l alpha_l,                 d=Def/W.
```

There is `epsilon_13>0` such that

```text
d<=epsilon_13  =>  K_13>=kappa_13/2,
                    average_(c,j)||w_(c,j)-1||_2^2>=9kappa_13,
                    average_three_corner||D||_2^2>=kappa_13/8. (SC10)
```

Hence no exact, or asymptotically exact, decoder of this face can make
every qutrit clause clock commute with every literal Boolean reflection.
This is stronger than merely saying that some projection pair fails to
commute: a fixed finite menu of individual words carries a
dimension-independent average defect.

The remaining gate is precise. The reflection is tied to the qutrit clock
by the additive Fourier identity

```text
v_(d,b)=1-2p_(d,b)
         =1-(2/3)sum_(s=0)^2 omega^(-bs)u_d^s.          (SC11)
```

Naming `u_d` and `v_(d,b)` as abstract group generators does not make
`(SC11)` an ordinary group relation. Indeed, the three desired scalar
joint types

```text
(omega^s; v_0,v_1,v_2),
v_s=-1 and v_a=+1 for a!=s,                             (SC12)
```

are not a coset of a character group: the ratio of the `s=1` and `s=0`
types has order six, whereas a three-point coset has difference group of
order three. Thus the naive commuting local group presentation cannot
enforce the cross-typing. This does not rule out a noncommuting ancillary
gadget.

No single word is proved uniformly nontrivial across all traces, no
effective value of `kappa_13` is claimed, and no ordinary presentation is
proved to authenticate `(SC11)` in finite approximations. No
nonhyperlinear group is claimed.

Primary-source interfaces inherited from the audited Lin route:

- Junqiao Lin, *MIPco=coRE*, Definition 6.14 and Theorem 6.15:
  https://arxiv.org/abs/2510.07162
- Laura Mancinska, Pieter Spaas, Taro Spirig, and Matthijs Vernooij,
  *Gap-preserving reductions and RE-completeness of independent set games*,
  Theorem 3.1 and Remark 3.2: https://arxiv.org/abs/2505.05253
- Eric Culf and Kieran Mastel, *RE-completeness of entangled constraint
  satisfaction problems*, Lemma 3.10, Example 4.13, and Theorem 4.14:
  https://arxiv.org/abs/2410.21223

DERIVATION
lin-qutrit-short-commutator-menu-proof
