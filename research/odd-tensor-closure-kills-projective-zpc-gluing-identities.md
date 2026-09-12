---
rg: 2
id: odd-tensor-closure-kills-projective-zpc-gluing-identities
kind: claim
title: Odd tensor closure reduces every exact ZPC gluing identity to a trilinear condition on the source support
distinct_from:
  selector-gated-equality-is-not-affine-pp-definable: that rules out exact gluing gadgets built from commuting parity auxiliaries on scalar configurations; this allows arbitrary noncommuting auxiliaries and projective central-sign packets, and derives the scalar sector from the source ZPC commutations instead of assuming it.
  zpc-transducer-is-exact-gluing-identity-or-nonhyperlinear: that proves a non-circular transducer needs an exact gluing identity; this proves that such an identity forces a trilinear rigidity of the source strategy's joint readable-payload support.
  odd-tensor-closure-forces-a-threehot-hidden-sector: that applies ternary tensor closure to literal one-hot selector spectra of a BCS source; this applies it to priority-decoded payload copies of two incident controlled-linear contexts.
  central-character-profiles-affine-under-odd-tensor-products: that treats port words that are scalar on a whole representation; this needs only joint eigenvectors of the commuting source observables inside tensor products of complete models.
  priority-decoded-contexts-are-not-glued-by-raw-gate-equality: that gives countermodels to two specific gluing relations; this constrains every exact gluing identity whatsoever in the marked group algebra.
---

**ESTABLISHED.** Let `L` be any finite binary LCS with solution group
`Gamma_L` and marked central involution `J`. It may have arbitrary auxiliary
variables and rows, including projective central-sign packets. Let it carry
two predication contexts `c,d` that share an unreadable variable `q`:
- selector variables `Z_(c,1..m)` and `Z_(d,1..n)`;
- predicated gate variables `G_(c,a)` and `H_(d,b)` for `q`;
- priority projections `Q_(c,a)` and `R_(d,b)` from
  `odd-selector-priority-decoding`;
- decoded copies, completed by the identity on even corners,

```text
U_c=(1-E_c)+sum_a Q_(c,a) G_(c,a),     U_d=(1-F_d)+sum_b R_(d,b) H_(d,b).  (OTZ1)
```

No transport or corner-identification words are used.

**Completeness hypothesis.** Let `M` be a family of perfect ZPC models. Every
`rho` in `M` must extend to a representation of `Gamma_L` with `J=-I` and with
canonical predication:

```text
Z_(c,a)=1-2P_(c,a),     G_(c,a)=P_(c,a) U_q+(1-P_(c,a)),                 (OTZ2)
```

and likewise for `d`. Here `P_(c,a)` are the readable branch projections and
`U_q` is the payload involution. These operators pairwise commute in a ZPC
model:
- readable observables are Z-aligned, so they commute with each other;
- `U_q` commutes with the readable observables of every context containing
  `q`, by edge commutation.

So the negative central sector has a joint spectral decomposition, whose
support is

```text
S(rho) subseteq F_2^m x F_2^n x F_2,     points (s,t,u).                 (OTZ3)
```

The selector parity rows give `s` and `t` odd parity. Write `p(x)` for the
first active index of an odd vector `x`.

**Theorem.** Assume the exact gluing identity

```text
(U_c-U_d)(1-J)=0     in C[Gamma_L].                                     (OTZ4)
```

Then for all `rho_1,rho_2,rho_3` in `M` and all `(s_i,t_i,u_i)` in `S(rho_i)`,
with `s=s_1+s_2+s_3` and `t=t_1+t_2+t_3`,

```text
sum_(i=1)^3 u_i ( (s_i)_(p(s)) + (t_i)_(p(t)) ) = 0     in F_2.         (OTZ5)
```

**Two-atom form.** Take `rho_1=rho_2=rho_3=rho` and the points `(s,t,0)`,
`(s,t,1)`, `(s',t',u')`. Then `(OTZ4)` forces

```text
s_(p(s'))=t_(p(t'))                                                     (OTZ6)
```

for every selector atom `(s,t)` on which `U_q` takes both signs, and every
atom `(s',t')` of the support.

**Singleton encodings.** With `s=e_a` and `t=e_b`, `(OTZ6)` says: if the atom
`(a,b)` carries both payload signs, then every support atom `(a',b')`
satisfies `a'=a` iff `b'=b`. So on the support, the branch labels of the two
incident contexts must determine each other.

## Consequences

- **The projective escape is closed.**
  `zpc-transducer-is-exact-gluing-identity-or-nonhyperlinear` left open an
  exact gluing identity with "no relevant scalar sector". But the relevant
  scalar sector is not supplied by the gadget: it is the joint spectrum of
  the commuting source observables `(Z_c, Z_d, U_q)`, and the tensor cube of
  complete models realizes its ternary sums. No auxiliary generators or
  relators can change `(OTZ5)`.
- **The only surviving non-circular transducers are source-specific.** An
  exact ZPC context transducer needs a source strategy whose joint support
  satisfies `(OTZ5)` on every incident pair, together with an encoding of the
  selectors that makes it hold. If a complete transducer also satisfies
  `(CTX')` while some triple violates `(OTZ5)`, then its solution group is
  already nonhyperlinear. That is circular as a reduction.
- **Scope.**
  - Corner identifications by fixed transport words are not covered. For pure
    cycle gadgets see `zpc-projective-cycle-gauge-cannot-glue-priority-decoders`.
  - Model-dependent rounding is not covered.
  - The theorem does not decide whether the explicit gap witness of
    `explicit-zpc-irs-gap-game-witness` satisfies `(OTZ5)` under some encoding.
