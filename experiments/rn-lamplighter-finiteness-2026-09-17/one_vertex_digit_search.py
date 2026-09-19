"""Consistency check for rational-affine-rn-groups-are-not-k-graph-full-groups (w14-101).
A one-vertex 2-graph whose path monoid sits inside Aff(Z[1/6],<2,3>) acting on Z_3, with colour-1 edges
e_c(x) = 3x + c (c in E) and colour-2 edges f_c(x) = (3^d x + c)/2 (c in F), needs the commutation
3F + 2E = 3^d E + F (as multisets, all sums distinct); E, F complete residue systems mod 3, mod 3^d.
Scaling by a power of 2 (a unit of Z_3) makes the digits integers; min(E)=0 forces min(F)=0 and
2 wF = (3^d - 2) wE for the widths. The theorem says no Kakutani-equivalent k-graph exists at all,
so this search must find nothing.  Usage: python3 one_vertex_digit_search.py"""
import itertools
def search(d, WE):
    n = 3**d; hits = 0; tested = 0
    for wE in range(2, WE+1):
        if ((n-2)*wE) % 2: continue
        wF = (n-2)*wE//2
        if wF + 1 < n: continue
        for a in range(1, wE):
            E = (0, a, wE)
            if len({c % 3 for c in E}) < 3: continue
            R0 = sorted(n*b for b in E)
            for mid in itertools.combinations(range(1, wF), n-2):
                F = (0,) + mid + (wF,)
                if len({c % n for c in F}) < n: continue
                tested += 1
                L = sorted(3*x + 2*b for x in F for b in E)
                if len(set(L)) == len(L) and L == sorted(n*b + x for x in F for b in E):
                    print("HIT", d, E, F); hits += 1
    return hits, tested
for d, WE in [(1, 60), (2, 6)]:
    h, t = search(d, WE)
    print(f"d={d} widths(E)<= {WE}: {t} admissible (E,F) tested, {h} commuting pairs")
