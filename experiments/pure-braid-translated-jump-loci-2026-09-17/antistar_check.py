"""Ascending links at barycentres of positive-dimensional cells.

In the Morse argument, the ascending link of the barycentre of a cell tau with lowest
vertex v is the join of two order complexes:
  - A = the proper faces of tau not containing v (the antistar of v in the boundary of tau);
  - the cofaces of tau with the same lowest vertex.
If A is simply connected, then so is the join.  This script checks, for n given on the
command line, that A is nonempty, connected and simply connected (and has reduced
H_0 = H_1 = 0 over F_1000003) for EVERY cell <C0,F> with base chamber C0 = identity and
EVERY vertex v of that cell.  The free S_n-action  w.<C,F> = <wC, wF>  preserves the
Salvetti face order, so the cells with base C0 represent every cell.  Uses the exact face
rule of salvetti_morse.py and the pi_1 test of verify_cert.py.

With the optional argument "one", only the first vertex of each cell is checked.  This
suffices: the face poset of <C0,F> is {G : G refines F} ordered by refinement (the
chamber of the face G is G o C0), and the Young subgroup prod_B S_B of the blocks of F
fixes F, preserves refinement, and acts transitively on star(F) with
v in star(G) <=> wv in star(wG).  So A_{wv} = w.A_v, an isomorphic poset.
Usage: python3 antistar_check.py n [one]"""
import sys, time
from salvetti_morse import faces_below, star, compose, refines, order_complex_homology
from verify_cert import pi1_trivial

def main():
    n = int(sys.argv[1])
    one = len(sys.argv) > 2 and sys.argv[2] == "one"
    C0 = tuple(range(n))
    ok = True
    for F in faces_below(C0):
        d = n - len(F)
        if d < 1:
            continue
        # proper faces of <C0,F>: <G o C0, G> with G a strict refinement of F
        # (every such G is a face of the chamber C0 o ... ; G ranges over faces >= F)
        faces = []
        for Cp in star(F):
            for G in faces_below(Cp):
                if G != F and refines(G, F) and compose(G, C0) == Cp:
                    faces.append((Cp, G))
        faces = sorted(set(faces))
        worst = None
        t0 = time.time()
        verts = star(F)[:1] if one else star(F)
        for v in verts:
            A =[(Cp, G) for (Cp, G) in faces if v not in star(G)]
            b = order_complex_homology(A, p=1000003, maxdim=1)
            pt = pi1_trivial(A) if d >= 2 else True
            good = len(A) > 0 and b != [-1] and all(x == 0 for x in b[:2]) and pt
            if not good:
                ok = False
                worst = (v, b, pt)
        print("cell type", [sorted(B) for B in F], "dim", d, "proper faces", len(faces),
              "vertices checked", len(verts), "antistar size", len(A),
              "all antistars 1-connected" if worst is None else f"FAIL {worst}",
              round(time.time() - t0, 1), "s", flush=True)
    print("ANTISTARS OK" if ok else "ANTISTARS FAILED")

if __name__ == "__main__":
    main()
