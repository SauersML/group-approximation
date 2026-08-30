---
rg: 2
id: finitely-generated-centralizer-switches-sigma1-proof
kind: route
title: Enumerate finite derivation certificates and apply Britton normal form
target: finitely-generated-centralizer-switches-are-sigma1
requires: []
---

For a finite list of words in a finite presentation, enumerate van Kampen
derivations in parallel.  All listed words are trivial exactly when a
finite derivation for each has appeared, proving the finite-equation event
is `Sigma^0_1`.

Let `A_e=<x_(e,1),...,x_(e,m_e)|R_e>` and
`K_e=<h_(e,1),...,h_(e,r_e)>`.  Since `K_e<=A_e`, equality holds
exactly when every `x_(e,i)` equals some word in the `h_(e,j)`.  The
finite collection of those words and equality derivations is an enumerable
certificate, so `{e:K_e=A_e}` is also `Sigma^0_1`.

In the centralizing HNN extension, `K_e=A_e` makes the stable letter
centralize the whole base, giving `A_e x Z`, which is amenable when
`A_e` is.  If `K_e<A_e`, choose `a notin K_e`.  Expanding a
nonempty reduced word in `t` and `a t a^-1` gives an HNN word whose
only possible pinches have intervening base coefficient `a` or
`a^-1`.  Neither lies in `K_e`, so Britton's lemma says the word is
nontrivial.  Thus `t` and `a t a^-1` freely generate `F_2), making
the extension nonamenable.

Hence amenability in this family is exactly the c.e. event `K_e=A_e`.
It cannot equal a `Pi^0_2`-complete non-c.e. totality event.
