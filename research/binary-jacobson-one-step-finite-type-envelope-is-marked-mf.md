---
rg: 2
id: binary-jacobson-one-step-finite-type-envelope-is-marked-mf
kind: claim
title: The Jacobson full-cycle packet and every one-step balanced overlap have a marked virtually free envelope
artifacts:
  - research/binary-jacobson-one-step-finite-type-envelope-proof.md
distinct_from:
  binary-jacobson-constant-q-root-envelope-is-finite: that retains every constant and head-labelled root but omits the balanced S/T-bearing occurrence; this adds the actual balanced involution and every conjugation incidence which starts and ends in the finite packet.
  binary-jacobson-active-cycle-generates-rank-three: that proves the corresponding words generate the full Jacobson elementary group after all mixed coefficient relations are imposed; this proves that their one-step finite-type shadow is virtually free and marked MF, so a load-bearing relation must lie in the kernel of that shadow map.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that gives the regular stationary vector for an arbitrary graph of finite groups; this identifies the literal Jacobson vertex and overlap groups, retains the actual head mark, and also proves the direct unitary Hall inequality on every coordinate-selected block support.
---

**ESTABLISHED.**  Put

```text
J=F_2<S,T | TS=1>,          Q=1-ST,
E=EL_3(J),                  F=EL_3(F_2[Q]).              (JFT1)
```

Then `F_2[Q] ~= F_2 x F_2` and therefore

```text
F ~= GL_3(F_2) x GL_3(F_2).                              (JFT2)
```

Let `u=w_12 in F` be the constant Weyl word and let

```text
a=a_12=[[S,Q,0],[0,T,0],[0,0,1]],
h=a u=[[Q,S,0],[T,0,0],[0,0,1]],
w=x_13(Q).                                                (JFT3)
```

Thus `h^2=1` and `[h,w]=1`.  Define the complete one-step finite overlap

```text
K=F cap h F h <= E,       theta=Ad(h)|_K,                (JFT4)
```

This overlap is explicit.  If `G_Q x G_P` denotes the head/tail
decomposition in `(JFT2)`, then

```text
K={(g,1):g in GL(<e_1,e_3>), g(e_2)=e_2}
  ~= GL_2(F_2) ~= S_3,       theta=id.                    (JFT4a)
```

and let `B=K semidirect_theta C_2`, with its involution denoted again by
`h`.  The finite graph-of-groups envelope

```text
Gamma_F=F *_K B                                             (JFT5)
```

has the following properties.

1. `Gamma_F` is virtually free and residually finite.  It is therefore
   operator MF.  The vertex copy of `F` embeds, so the mark `w` survives;
   indeed a finite quotient can be chosen injective on all of `F`.
2. There is a canonical surjection

   ```text
   Gamma_F -> E,        F |-> F,       h |-> h,           (JFT6)
   ```

   and `a=h u` in both groups.  It records every conjugation relation
   `h k h=theta(k)` whose two endpoints lie in the finite packet.  Since
   `F` contains the complete directed constant three-cycle,
   `binary-jacobson-active-cycle-generates-rank-three` makes `(JFT6)`
   surjective.
3. In every finite-dimensional unitary representation, no Hall deficit can
   be obtained merely by decomposing the surviving `w=-1` cut into finite
   `F`-isotypic or finer orthogonal matrix-coordinate blocks and retaining
   the actual nonzero blocks of `h`.  If `P_i` are the selected source and
   target blocks and

   ```text
   i -> j  iff  P_j rho(h) P_i != 0,
   ```

   then for every set `S` of source blocks

   ```text
   rank(P_S) <= rank(P_(N(S))).                           (JFT7)
   ```

   The same statement holds for the central `F`-type support of `a`, since
   `a=h u` and `u in F` preserves every central isotypic carrier.
4. The regular finite-packet profile is strictly positive on every marked
   type.  Writing `G=GL_3(F_2)` and
   `Irr(F)={alpha box beta}`, let `d_alpha,d_beta` be the degrees and let
   `r_alpha` be the dimension of the negative eigenspace of the transvection
   `w` in `alpha`.  On the `alpha box beta` isotypic part of `lambda_F`, the
   marked dimension is

   ```text
   d_alpha r_alpha d_beta^2.                              (JFT8)
   ```

   It is positive exactly when `alpha` is nontrivial, and the sum of `(JFT8)`
   is `|F|/2`.  The regular restrictions across `F <- K -> B` agree after a
   common amplification.  Finite quotients of `Gamma_F` injective on `F`
   realize integral multiples of this same marked profile.

Consequently the finite packet at the full-cycle threshold does not contain
a hidden isotypic or block-support Hall selector.  Any successful Jacobson
collapse must use a relation in the kernel of `(JFT6)`: equivalently, an
alternating mixed-coefficient occurrence/holonomy not encoded by the entire
one-step finite overlap.  Omitting blocks from `(JFT7)` can help only after a
separate group relation proves operator-norm leakage into every omitted block
is small; finite type support itself supplies no such estimate.

One relation escaping this envelope is identified, with optimal
balanced-syllable length, by
`binary-jacobson-first-mixed-kernel-is-three-syllable`.

DERIVATION
binary-jacobson-one-step-finite-type-envelope-proof
