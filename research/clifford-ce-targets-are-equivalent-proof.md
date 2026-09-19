---
rg: 2
id: clifford-ce-targets-are-equivalent-proof
kind: route
title: Crossed product by the parity flip, then compress to the negative central corner
target: clifford-ce-targets-are-equivalent
requires: []
artifacts:
  - notes/PERFECT_CORE_KUN_THOM_WREATH.md
---

# Crossed product by the parity flip, then compress to the negative central corner

Internal proofs, transcribed from `notes/PERFECT_CORE_KUN_THOM_WREATH.md`,
Proposition 4 and Theorem 6. `requires: []` is a proof commitment; both
arguments are elementary given the Clifford relations, and neither uses any
open input.

## Proposition 4 — full versus even core

> **Proposition 4.**  One has
> \[ M_{\mathrm{full}}\cong (A_{\mathrm{CAR}}\rtimes G)\rtimes_{\operatorname{Ad}(C_o)}\mathbb Z/2 \]
> for any fixed Majorana generator \(C_o\).  Consequently
> \[ M_{\mathrm{full}}\text{ is Connes-embeddable} \iff A_{\mathrm{CAR}}\rtimes G\text{ is Connes-embeddable.} \]
>
> **Proof.**  The odd Majorana \(C_o\) normalizes the even Clifford algebra.
> It also normalizes the crossed-product unitaries modulo the even algebra,
> because
> \[ C_o u_g C_o=(C_oC_{go})u_g \]
> and \(C_oC_{go}\) is even.  Moreover \(C_o^2=1\), and the even crossed
> product together with \(C_o\) generates \(M_{\mathrm{full}}\).  The parity
> automorphism fixes the even crossed product and sends \(C_o\) to \(-C_o\),
> so its conditional expectation proves that the two homogeneous summands
> are linearly independent.  This proves `(19a)`.
>
> Connes embeddability passes to von Neumann subalgebras, giving the forward
> implication in `(19b)`.  Conversely, the regular covariant representation
> embeds a crossed product by the finite group \(\mathbb Z/2\) into
> \(M_2(A_{\mathrm{CAR}}\rtimes G)\).  Matrix amplification preserves Connes
> embeddability, giving the reverse implication.

Both directions of the equivalence are cheap for the same reason: the extension
is by the *finite* group `Z/2`, so one direction is subalgebra heredity and the
other is a two-by-two amplification. No permanence theorem for infinite groups
is involved, which is why this equivalence is safe while general
crossed-product CE permanence is not.

## Theorem 6 — no character shortcut

> **Theorem 6 (no character shortcut).**  The following are equivalent:
> 1. \(E_{\mathrm{Cl},0}\) has a Connes-embeddable character \(\chi\) with \(\chi(z)\ne1\);
> 2. it has a Connes-embeddable character \(\chi_-\) with \(\chi_-(z)=-1\);
> 3. the canonical trace \(\tau_{\mathrm{can}}\) in (24) is Connes-embeddable.
>
> **Proof.**  The implication \(3\Rightarrow2\Rightarrow1\) is immediate.
> For \(1\Rightarrow2\), realize \(\chi\) in a tracial matrix ultraproduct.
> The central involution \(z\) has spectral projections
> \[ e_+=(1+z)/2,\qquad e_-=(1-z)/2. \]
> The inequality \(\chi(z)\ne1\) says that \(e_-\) has positive trace.
> Compressing to this central corner and normalizing the trace gives a
> Connes-embeddable character \(\chi_-\) with \(\chi_-(z)=-1\).

The step `2 => 3` is Lemma 5 of the same document, which computes that in the
`z = -1` sector the Pauli monomials other than the identity have trace zero,
forcing the character to be `tau_can`.

The load-bearing move is the compression in `1 => 2`. It works because `z` is
**central**, so its spectral projections are central and the corner is again a
tracial von Neumann algebra with a Connes-embeddable trace after
renormalization. Note the contrast with the operator-norm setting of
`kun-thom-clifford-extension-not-weak-mf`, where exactly the same corner cut is
performed and there it *leads to a contradiction* — the difference being that
the operator-norm corona is stably finite and supports the Kazhdan projection
argument, while a tracial ultraproduct does not obstruct the corner.

## Scope

This is a statement about the relationships between targets, not about whether
any of them holds. It closes no open question and should not be read as
evidence in either direction on `kun-thom-clifford-crossed-product-ce`.
