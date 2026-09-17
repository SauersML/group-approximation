"""SAT certificates on the type-preserving subgroup Gamma_0 = ker(Gamma_T -> Z/3, a_x -> 1).
Gamma_0 has index 3, is torsion-free (a finite subgroup fixes a point of the Ã2 building; being
type-preserving it fixes a vertex; the vertex action is free), and has property (T).
The type of a normal form w is (#positive letters - #negative letters) mod 3.

mode 'lo'  : positive-cone clauses on type-0 elements of B(R)       UNSAT => Gamma_0 not left-orderable
mode 'pre' : left-preorder clauses (P,H,P^-1) on type-0 elements, with 'some type-0 element of B(3)
             outside H' (these contain the Schreier generators a_x a_0^-1, a_0 a_x a_0, a_0^-1 a_x of
             Gamma_0 for the transversal {1, a_0, a_0^-1})    UNSAT => every Gamma_0 -> Homeo_+(R) trivial
Only products g*h with |h| <= hmax are imposed (a subset of the true constraints, so UNSAT is sound).
Usage: [SOLVER=glucose4] gamma0_sat.py mode R hmax file [i j ...]   (default solver CaDiCaL 1.5.3)"""
import json, sys, time
import os
from pysat.solvers import Solver
from a2group import A2Group

def typ(w):
    return sum(e for (_, e) in w) % 3

def run(G, mode, R, hmax):
    layers = G.ball(R)
    elems = [w for l in layers[1:] for w in l if typ(w) == 0]
    hs = [w for l in layers[1:hmax + 1] for w in l if typ(w) == 0]
    S = Solver(name=os.environ.get('SOLVER', 'cadical153')); P = {}; H = {}; nv = 0
    for w in elems:
        if w in P: continue
        wi = G.inv(w)
        if mode == 'lo':
            nv += 1; P[w] = nv; P[wi] = -nv
        else:
            nv += 1; P[w] = nv; nv += 1; P[wi] = nv; nv += 1; H[w] = H[wi] = nv
            S.add_clause([P[w], P[wi], H[w]]); S.add_clause([-P[w], -P[wi]])
            S.add_clause([-P[w], -H[w]]); S.add_clause([-P[wi], -H[w]])
    ncl = 0
    for g in elems:
        for h in hs:
            gh = G.mul(g, h)
            if not gh:
                if mode == 'lo':
                    S.add_clause([-P[g], -P[h]])
                else:
                    S.add_clause([-P[g], -P[h]]); S.add_clause([-H[g], -P[h]]); S.add_clause([-P[g], -H[h]])
                continue
            if gh not in P: continue
            ncl += 1
            S.add_clause([-P[g], -P[h], P[gh]])
            if mode != 'lo':
                S.add_clause([-H[g], -P[h], P[gh]]); S.add_clause([-P[g], -H[h], P[gh]])
                S.add_clause([-H[g], -H[h], H[gh]])
    if mode != 'lo':
        S.add_clause([-H[w] for w in elems if len(w) <= 3])
    return S.solve(), len(elems), ncl

if __name__ == "__main__":
    mode, R, hmax, f = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    Ts = json.load(open(f))
    idx = [int(a) for a in sys.argv[5:]] or range(len(Ts))
    for i in idx:
        t0 = time.time()
        G = A2Group([tuple(t) for t in Ts[i]])
        assert G.check_confluence()[0]
        res, ne, ncl = run(G, mode, R, hmax)
        tors = sum(1 for t in Ts[i] if len(set(t)) == 1)
        print(f"T{i} mode={mode} R={R} hmax={hmax} type0-elems={ne} products={ncl} torsion-triples={tors} SAT={res} ({time.time()-t0:.0f}s)", flush=True)
