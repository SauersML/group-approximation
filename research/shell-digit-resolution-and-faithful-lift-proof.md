---
rg: 2
id: shell-digit-resolution-and-faithful-lift-proof
kind: route
title: Encode gaps by terminated digit words and extend the action from an invariant dense set
target: fixed-base-shells-embed-in-contracting-rsg
requires:
  - terminated-digit-carries-form-finite-injection-nucleus
  - shell-cantor-embeddings-are-finite-germ-extensions
  - odometer-prefix-groups-have-fg-index-kernels
artifacts:
  - research/artifacts/boone-higman-terminated-digit-resolution-2026-09-08.md
---

Use the graph and path cones C_X,C_Y from the nucleus claim.
For n=r*q+i, 0<=i<r, let w(q) be the finite bijective-base-h
word for q. Call i*w(q)*# the gap token for n. Every path in
C_X with infinitely many # edges is uniquely a sequence of gap
tokens. This set Z is dense in C_X. Identify it with the dense
set of binary sequences with infinitely many 1s by

    token(n_0)*token(n_1)*... <-> 0^n_0*1*0^n_1*1*... .

The binary set is invariant under V and under all shell maps.
This correspondence is a homeomorphism of the two dense subspaces.

## Lift the binary prefix maps

Let A:C_X->C_X increment the first gap index by one. On the
root edges it has the formulas

    A(i*z)=(i+1)*z for i<r-1,
    A((r-1)*z)=0*I(z).

Let B:C_X->C_X prepend the token 0*# for the zero gap. These
are rational homeomorphisms onto disjoint clopen images whose
union is C_X:

    A(C_X)=C_X minus 0*#*C_X,       B(C_X)=0*#*C_X.

They agree on Z with binary prefixing by 0 and 1. Hence a binary
prefix u defines an injection U_u by composing A and B. Explicitly,
U_u prepends one fixed gap token for every 1 in u and then increases
the next gap by the number of trailing zeros in u. Its inverse is
defined on its clopen image.

For a binary V table with pairs u_j->v_j, define the lifted map
on U_(u_j)(C_X) by U_(v_j)*U_(u_j)^-1. These pieces have disjoint
clopen domains and ranges and form a homeomorphism of C_X. The
prefix partition identities follow from the displayed partition
by A and B, so table expansions give the same map.

All recurrent local actions in these finite constructions lie in
N. More explicitly, a fixed integer increment on the first gap
reduces after the root edge to a fixed nonnegative power of I;
its inverse uses powers of I^-1 on their clopen domains. For
c>=0, processing a digit d in I^c leaves carry
floor((d+c-1)/h), which strictly reduces c when c>1. Thus the
eventual states of such increments are I and the typed identities.
Refining the inverse charts uses I^-1(1z)=D(z) and the identity
branches of I^-1, so inverse increments have only D and identity
recurrent states. Fixed token insertions and removals are canonical
prefix maps. A finite V table consequently has nucleus contained
in N and is an element of H_(h,r).

## Lift an actual shell permutation

Let rho be one of the specified generator permutations. On a
terminated first gap token, send token(n)*z to token(rho(n))*z.
We must extend this to the paths whose first digit block never
terminates, and verify finite-state behavior there.

A source odometer chart fixes a root and finitely many ordinary
base-h digits. Bijective-base words of a fixed length k also give
every residue modulo h^k exactly once. Replace the ordinary source
and target prefixes by the corresponding bijective prefixes. Their
integer values differ from the ordinary representatives by integer
multiples of the relevant h-power. Absorb those differences into
the integer carry label. The chart now has the form

    i*U*(tail) -> j*V*(tail+c),

where tail+c is the fixed translation on its bijective-base value,
implemented by a power of I or its partial inverse. A negative carry
requires excluding only finitely many terminated tails. Words too
short to have the specified prefix, and the original finite
exceptions of rho, likewise give only finitely many gap tokens.
Refine the chart partitions and handle these finitely many tokens
individually by their exact token replacements.

Concretely, write the old ordinary prefix values as u,v and the
new bijective prefix values as U_0,V_0. Set

    a=(U_0-u)/h^k,       b=(V_0-v)/h^l.

An input U_0+h^k*q has old tail q+a, so its output has new
tail q+(a+c-b). This is an integer translation, with no change
of scale on the remaining tail. Choose a finite cutoff large
enough that both tails are nonnegative and the original near
chart agrees with rho. Removing the finitely many excluded
token cones leaves a clopen domain. The finitely many boundary
prefix cones, together with the finitely many short token cones,
cover C_X; hence this removal and the exact exceptional token
replacements really produce a finite clopen partition.

This gives finitely many rational partial maps on clopen sets.
On the nonterminating digit paths they agree with the corresponding
odometer forest charts (under the bijective-digit coordinate).
Those charts form a homeomorphism of the r-root h-adic boundary.
Together with the actual bijection of finite gap indices, they give
a homeomorphism of C_X. Alternatively construct the same extension
for rho^-1; the two composites fix the dense terminated-gap set
and are therefore identity. The fixed translations have recurrent
states in N, as above; finite token exceptions have only identity
states. The lifted shell generator therefore belongs to H_(h,r).

## Relations, faithfulness, and scope

All the lifted generators preserve Z and realize the original
E_nu action there. Every true relation of E_nu is identity on
Z, hence on C_X by continuity. Thus the lifts define a homomorphism
E_nu->H_(h,r). If its image is identity, the original element fixes
the dense binary set with infinitely many 1s, hence is identity
on the original Cantor set. The homomorphism is injective.

The required nucleus claim supplies a finitely presented simple
overgroup of H_(h,r), so composition gives the asserted embedding
of E_nu. It does not give E_nu a finite presentation.

Paths with a final # followed by infinitely many digits form the
new Cantor fibers over the old eventually-zero points. They have
not been identified with individual points. In particular this
construction changes the compactification of the dense gap-token
space; it is not a conjugacy of the original Cantor action.
