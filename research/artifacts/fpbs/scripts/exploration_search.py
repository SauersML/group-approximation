"""Balanced exhaustive search shared by the exact replay and implicit-graph pilot."""

import heapq
import itertools


def edge_key(u, v):
    return (u, v) if u < v else (v, u)


def optimistic_search(source, target, neighbors, distance, read_edge,
                      *, query_limit, planning_limit):
    """Test optimistic shortest paths, preferring fewer unqueried edges.

    Planning sees only graph geometry and cached answers. Its expansion cap
    is separate from the fresh percolation-query cap. Either can censor.
    """
    assert query_limit >= 0 and planning_limit >= 0
    cache, trace = {}, []
    expansions = replans = 0

    def result(status, path=(), cell=frozenset(), reason=None):
        return {"status": status, "trace": tuple(trace), "path": tuple(path),
                "finite_component": frozenset(cell), "censor_reason": reason,
                "planning_expansions": expansions, "replans": replans}

    if source == target:
        return result("connected", (source,))
    while True:
        replans += 1
        order = itertools.count()
        heuristic = distance(source, target)
        queue = [(heuristic, 0, heuristic, next(order), 0, source)]
        best, parent = {source: (0, 0)}, {source: None}
        path = None
        while queue:
            _, unknown, _, _, depth, u = heapq.heappop(queue)
            if (depth, unknown) != best[u]:
                continue
            if expansions == planning_limit:
                return result("censored", reason="planning")
            expansions += 1
            if u == target:
                path = [u]
                while parent[u] is not None:
                    u = parent[u]
                    path.append(u)
                path.reverse()
                break
            for v in neighbors(u):
                edge = edge_key(u, v)
                if not cache.get(edge, True):
                    continue
                candidate = (depth+1, unknown+(edge not in cache))
                if v in best and best[v] <= candidate:
                    continue
                best[v], parent[v] = candidate, u
                heuristic = distance(v, target)
                heapq.heappush(queue, (candidate[0]+heuristic, candidate[1],
                                      heuristic, next(order), candidate[0], v))
        if path is None:
            return result("disconnected", cell=best)
        for u, v in zip(path, path[1:]):
            edge = edge_key(u, v)
            if edge not in cache:
                if len(trace) == query_limit:
                    return result("censored", reason="queries")
                cache[edge] = bool(read_edge(edge))
                trace.append((edge, cache[edge]))
            if not cache[edge]:
                break
        else:
            return result("connected", path)


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
