---
rg: 2
id: binary-jacobson-steinberg-cover-k2-citation
kind: route
title: Identify the Toeplitz graph algebra, compute its stable rank and K-two, and apply unstable K-two stability
target: binary-jacobson-steinberg-cover-is-elementary
requires: []
---

This route records four primary-source inputs and checks their hypotheses.

1.  The graph with a loop at `v`, one edge from `v` to a sink `w`, and no
    other edges is the algebraic Toeplitz graph.  Abrams, *Leavitt path
    algebras: the first decade*, Example 2.14, identifies its Leavitt path
    algebra with `K<x,y | xy=1>`.  Taking `x=T,y=S` identifies it with `J`.
    Source: <https://link.springer.com/article/10.1007/s13373-014-0061-7#Sec15>.

2.  Ara--Pardo, Theorem 2.8, classifies the Bass stable rank of a row-finite
    Leavitt path algebra.  The Toeplitz graph is not acyclic.  Its only proper
    nonempty hereditary saturated quotient is the one-loop graph, whose
    cycle has no exit; the original graph has a sink.  Therefore neither the
    rank-one nor infinite-rank cases of that theorem applies, and
    `bsr(J)=2`.  Source: <https://arxiv.org/abs/math/0609354>.

3.  Gabe--Ruiz--Tomforde--Whalen, Theorem 4.3, computes even algebraic
    K-groups of a Leavitt path algebra over a finite field as the kernel of a
    graph matrix over `Z/(q^j-1)`.  Here `q=2` and degree `2` has `j=1`, so
    the coefficient group is `Z/(2^1-1)=0`; hence `K_2(J)=0`.
    Source: <https://arxiv.org/pdf/1407.5094>.

4.  Suslin--Tulenbaev stabilization, in the Steinberg notation recorded by
    Weibel, *The K-book*, Chapter III, Remark 5.5.2, says that if
    `sr(R)=d+1`, then

    ```text
    K_2(n,R)=ker(St_n(R)->E_n(R)) -> K_2(R)
    ```

    is an isomorphism for `n>=d+3`.  With `sr(J)=2`, take `d=1`; rank five
    is in the stable range.  Sources:
    <https://www.mathnet.ru/eng/znsl1879> and
    <https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.III.pdf#page=39>.

Combining the last two steps gives `K_2(5,J)=0`.  The canonical map is
surjective by the definition of `E_5(J)`, so it is the isomorphism `(JSI3)`.
