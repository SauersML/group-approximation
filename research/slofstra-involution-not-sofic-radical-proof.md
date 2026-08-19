---
rg: 2
id: slofstra-involution-not-sofic-radical-proof
kind: route
title: Make Slofstra's finite-coordinate constructions permutation-valued throughout
target: slofstra-involution-not-sofic-radical
requires: []
artifacts:
  - notes/NOTEPAD.md
---

# Make Slofstra's finite-coordinate constructions permutation-valued throughout

Internal proof from `notes/NOTEPAD.md`, section "The Slofstra involution
survives a sofic image". `requires: []` is a proof commitment. The primary
source is pinned in the corpus at statement level: *"Primary pins checked line
by line: Slofstra, arXiv:1703.08618v2, Definition 2.5 and Proposition 5.1
(only elementwise approximate visibility), and arXiv:1606.03140, Theorem 3.1
(universal group embedding, without hyperlinearity of the target)."*

## Step 1 — an exact involution by `o(|X_n|)` surgery

Start from Slofstra's sofic seed

```text
K_0 = <x,y,a,b | a^2=b^2=1, [a,b]=1,
                 yay^(-1)=a, yby^(-1)=ab, xyx^(-1)=y^2>
```

and an asymptotically free permutation approximation. If `A_n` is assigned to
`a` then `d_H(A_n^2,1) -> 0` and `d_H(A_n,1) -> 1`.

> Changing `A_n` on `o(|X_n|)` points makes it an exact involution: retain its
> one- and two-cycles and replace all cycles of length at least three.  The
> mass of the latter cycles is exactly the mass moved by `A_n^2`, hence is
> `o(|X_n|)`.  This edit preserves all relators asymptotically.

The counting is the crux and it is exact: cycles of length `>= 3` are
precisely the support of `A_n^2`, so making the involution exact costs only
the already-vanishing defect. The second limit then gives
`|F_n| = o(|X_n|)` for the fixed-point set of `A_n`.

## Step 2 — permutation-preservation through Proposition 4.8

> Inspecting its proof shows more than the stated unitary claim: every block
> matrix introduced there is a permutation matrix whenever the input matrices
> are permutation matrices.  Diagonal sums, block swaps, and products preserve
> this property.

Faithfulness is deliberately not claimed: *"We do not assert that these
approximations are faithful on all of `G`; only visibility of `xi` is needed."*

## Step 3 — the intermediate group, where `J` is made maximally visible

For `Ghat = <G,J,t | J^2=t^2=1, [J,G]=[J,t]=1, t xi t = J xi>` put
`Omega_n = X_n x {0,1}`, let `J_n(z,e) = (z, e+1 mod 2)`, and build `T_n`
orbit by orbit: on each two-cycle `{u,v}` of `A_n` flip the second coordinate
over one chosen endpoint; over a fixed point of `A_n` let `T_n` be the
identity. Then `T_n^2 = 1`, `[T_n,J_n] = 1`, and on the four points above each
two-cycle

```text
T_n (A_n x 1) T_n = J_n (A_n x 1).
```

> The only failures of `(HSC11)` lie above `F_n`.  Thus its normalized Hamming
> defect is `|F_n|/|X_n| = o(1)`.

and `d_H(J_n,1) = 1`, so `J` is maximally visible.

## Step 4 — transport into `S`, and the metric bookkeeping

Proposition 4.2 embeds `Ghat` over `Z_2` into `S`, and its proof is again
permutation-preserving (block diagonal permutations and block swaps whose
nonzero blocks are products of input permutations), with the lift fixing `J`
up to repeated diagonal copies. Applying it coordinatewise sends every
defining relator of `S` to the identity in Hamming distance while `J` stays at
Hamming distance one; the metric ultraproduct gives `Theta`.

The conversion between the two metrics is exact, which is what makes the
imported Hilbert--Schmidt estimates usable:

```text
||P-Q||_2^2 = 2 d_H(P,Q)      for permutation matrices P,Q.
```

So vanishing input Hamming defects give vanishing input Frobenius defects, the
cited block estimates give vanishing output Frobenius defects, and because the
outputs are permutations the identity returns vanishing output Hamming defects.

## Conclusion

`Theta(J) != 1` and the image lies in a metric ultraproduct of finite
symmetric groups, hence is sofic. So `J` is not killed by every homomorphism
to a sofic group, i.e. `J notin Rad_sof(S)`.
