"""Seed types of the depth-j problem, lifted to a finite Q.

Every same-fibre pair of Gamma_{j+1}(Q) is D-equivalent (same fold closure)
to the lift at some point y of a representative pair of one D-component of
the pair graph of core_{j+1}.  Type 0 is the unique lawful component; types
1.. are the overfold components.  seed(tau, y) returns the pair of vertices
of Gamma_{j+1}(Q) over y.
"""
from foldlib import depth_graphs, inverse_perm, act, inv
from pair_automaton import core, pair_graph, components


class Seeds:
    def __init__(self, PA, PB, j):
        self.PA, self.PB = PA, PB
        self.IA, self.IB = inverse_perm(PA), inverse_perm(PB)
        self.Gj, self.G, self.m = depth_graphs(PA, PB, j)
        C = core(j + 1)
        _, _, psi = depth_graphs([0], [0], j)
        states, idx, edges = pair_graph(C)
        comp, _ = components(len(states), edges)
        law = [r for r, vs in comp.items()
               if psi[states[vs[0]][0]] == psi[states[vs[0]][1]]]
        assert len(law) == 1
        over = sorted(r for r in comp if r not in law)
        self.reps = [states[comp[law[0]][0]]] + [states[comp[r][0]] for r in over]
        self.sizes = [len(comp[law[0]])] + [len(comp[r]) for r in over]
        self.C = C

    def vertex(self, x, y):
        w = self.C.word[x][1]
        p = act(y, inv(w), self.PA, self.PB, self.IA, self.IB)
        v = self.G.read(p, w)
        assert v is not None and self.G.over[v] == y
        return v

    def seed(self, tau, y):
        x, x2 = self.reps[tau]
        return (self.vertex(x, y), self.vertex(x2, y))

    def ntypes(self):
        return len(self.reps)
