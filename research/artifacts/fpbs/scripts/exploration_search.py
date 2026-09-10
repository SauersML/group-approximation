"""Balanced exhaustive search shared by the exact replay and implicit-graph pilot."""

import heapq
import itertools


def edge_key(u, v):
    return (u, v) if u < v else (v, u)


def balanced_search(source, target, neighbors, distance, read_edge,
                    *, direction, query_limit, reverse=False):
    """Return a path, an exhausted finite component, or explicit censoring.

    Only read_edge obtains percolation information. Geometry is deterministic.
    query_limit bounds fresh queries; cached answers may still certify a result.
    """
    assert direction >= 0 and query_limit >= 0
    if source == target:
        return {"status": "connected", "trace": (), "path": (source,),
                "finite_component": frozenset()}
    depths, parents = [{source: 0}, {target: 0}], [{source: None}, {target: None}]
    queues, cache, trace = [[], []], {}, []
    order = itertools.count()
    goals = [target, source]

    def enqueue(side, u):
        adjacent = list(neighbors(u))
        if reverse:
            adjacent.reverse()
        for v in adjacent:
            priority = depths[side][u]+1+direction*distance(v, goals[side])
            heapq.heappush(queues[side], (priority, next(order), u, v))

    def path_to_root(side, vertex):
        path = [vertex]
        while parents[side][vertex] is not None:
            vertex = parents[side][vertex]
            path.append(vertex)
        return path

    enqueue(0, source)
    enqueue(1, target)
    side = 0
    while True:
        exhausted = 0 if not queues[0] else (1 if not queues[1] else None)
        if exhausted is not None:
            return {"status": "disconnected", "trace": tuple(trace), "path": (),
                    "finite_component": frozenset(depths[exhausted])}
        _, _, u, v = heapq.heappop(queues[side])
        edge = edge_key(u, v)
        fresh = edge not in cache
        if fresh:
            if len(trace) == query_limit:
                return {"status": "censored", "trace": tuple(trace), "path": (),
                        "finite_component": frozenset()}
            cache[edge] = read_edge(edge)
            trace.append((edge, cache[edge]))
        if cache[edge] and v not in depths[side]:
            depths[side][v] = depths[side][u]+1
            parents[side][v] = u
            enqueue(side, v)
            if v in depths[1-side]:
                left, right = path_to_root(0, v), path_to_root(1, v)
                return {"status": "connected", "trace": tuple(trace),
                        "path": tuple(list(reversed(left))+right[1:]),
                        "finite_component": frozenset()}
        if fresh:
            side = 1-side


def verify_certificate(result, source, target, neighbors):
    """Verify returned finite certificates using only the recorded answers."""
    trace = result["trace"]
    answers = dict(trace)
    assert len(answers) == len(trace)
    if result["status"] == "connected":
        path = result["path"]
        assert path[0] == source and path[-1] == target
        for u, v in zip(path, path[1:]):
            assert v in neighbors(u)
            assert answers[edge_key(u, v)]
    elif result["status"] == "disconnected":
        cell = result["finite_component"]
        assert (source in cell) != (target in cell)
        for u in cell:
            for v in neighbors(u):
                if v not in cell:
                    assert edge_key(u, v) in answers and not answers[edge_key(u, v)]
    else:
        assert result["status"] == "censored"
        assert not result["path"] and not result["finite_component"]
