"""Sub-claims (A), (B) of analyze.py on the three non-malnormal hosts that
produced the k = 1 violations of k1_nonmal_s12.txt (Gamma_X cap lifted)."""
import analyze
from census import compact, graph_of, regular_action, fi_subgroup

CASES = [
    (['baB', 'BAb'], [[2, 0, 1], [0, 2, 1]]),
    (['BAbb', 'BAba'], [[0, 4, 2, 3, 1], [1, 4, 0, 3, 2]]),
    (['aba', 'AAB'], [[4, 0, 2, 3, 1], [0, 1, 2, 4, 3]]),
]

for ws, perms in CASES:

    def host_v(kind, rng, ws=ws):
        return ws, compact(*graph_of(ws)), ws

    def rand_X_v(Cws, rng, perms=perms):
        reg = regular_action(perms)
        return fi_subgroup(Cws, reg), ('reg', len(reg[0]))

    analyze.host = host_v
    analyze.rand_X = rand_X_v
    analyze.main(0, 1, 'viol:' + '/'.join(ws), cap=10 ** 6)
