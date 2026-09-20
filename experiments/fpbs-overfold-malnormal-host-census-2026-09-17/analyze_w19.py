"""Sub-claims (A), (B) of analyze.py on the w19-fp-last1 non-malnormal
counterexample B = <b, a b^2 a^-1>, X = ker(B -> S3)."""
import analyze
from census import compact, graph_of, regular_action, fi_subgroup


def host_w19(kind, rng):
    ws = ['b', 'abbA']
    return ws, compact(*graph_of(ws)), ws


def rand_X_w19(Cws, rng):
    return fi_subgroup(Cws, regular_action([[1, 2, 0], [1, 0, 2]])), ('reg', 6)


analyze.host = host_w19
analyze.rand_X = rand_X_w19
analyze.main(0, 1, 'w19')
