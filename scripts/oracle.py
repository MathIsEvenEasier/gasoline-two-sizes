"""Exact interval-supply LP oracle; standard library only.

This evaluates the mathematical relaxation, not floating-point solver output.
Vertex j is the inventory after consumption j (vertex 0 is also vertex n).
For delivery i, edges (i-1)->i and i->(i-1) have weights lo[i]-y[i]
and y[i]-hi[i]. They encode lower bounds on differences of inventories.
Every directed cycle has nonpositive weight when sum(lo)<=sum(y)<=sum(hi).
The largest path weight from any vertex gives a feasible inventory potential.
"""
from fractions import Fraction


def capacity(x, y):
    assert len(x) == len(y) and sum(x) == sum(y)
    s = 0
    levels = [0]
    for a, b in zip(x, y):
        s += a
        levels.append(s)
        s -= b
        levels.append(s)
    return max(levels) - min(levels)


def interval_lp(lo, hi, y, certificate=False):
    n = len(y)
    assert n and len(lo) == len(hi) == n
    assert all(0 <= a <= b for a, b in zip(lo, hi))
    assert all(v >= 0 for v in y)
    assert sum(lo) <= sum(y) <= sum(hi)
    potential = [0] * n
    witness = [(j, j, 0, 'empty') for j in range(n)]
    for start in range(n):
        v, total = start, 0
        for length in range(1, n):
            total += lo[v] - y[v]
            v = (v + 1) % n
            if total > potential[v]:
                potential[v] = total
                witness[v] = (start, v, length, 'forward')
        v, total = start, 0
        for length in range(1, n):
            v = (v - 1) % n
            total += y[v] - hi[v]
            if total > potential[v]:
                potential[v] = total
                witness[v] = (start, v, length, 'backward')
    peaks = [potential[(i + 1) % n] + y[i] for i in range(n)]
    value = max(peaks)
    if not certificate:
        return value
    supplies = [potential[(i + 1) % n] - potential[i] + y[i]
                for i in range(n)]
    assert all(a <= q <= b for a, q, b in zip(lo, supplies, hi))
    assert sum(supplies) == sum(y)
    assert capacity(supplies, y) == value
    end = (peaks.index(value) + 1) % n
    return {'value': value, 'supplies': supplies, 'potential': potential,
            'lower_bound_path': witness[end], 'peak_day': (end - 1) % n}


def prefix_lp(prefix, K, y, certificate=False):
    n = len(y)
    return interval_lp(list(prefix) + [1] * (n-len(prefix)),
                       list(prefix) + [K] * (n-len(prefix)), y, certificate)


def iterative_rounding(x, y, record=False):
    assert set(x) <= {1, max(x)} and min(x) >= 1
    assert len(x) == len(y) and sum(x) == sum(y)
    K = max(x)
    available = list(enumerate(x))
    prefix, trace = [], []
    for j in range(len(y)):
        values = {v: prefix_lp(prefix + [v], K, y)
                  for v in set(v for _, v in available)}
        index, v = min(available, key=lambda iv: (values[iv[1]], iv[0]))
        trace.append({'position': j, 'candidate_values': values,
                      'chosen_index': index, 'chosen': v})
        prefix.append(v)
        available.remove((index, v))
    result = {'order': prefix, 'capacity': capacity(prefix, y)}
    if record:
        result['steps'] = trace
    return result


def assignment_from_supplies(prefix, K, y, supplies):
    """Construct remaining doubly-stochastic block as rational entries."""
    h = K - 1
    r = len(y) - len(prefix)
    m = (sum(y) - sum(prefix) - r) // h
    p = [Fraction(v-1, h) for v in supplies[len(prefix):]]
    assert sum(p) == m and all(0 <= v <= 1 for v in p)
    rows = ([[v/m for v in p] for _ in range(m)] if m else [])
    rows += ([[ (1-v)/(r-m) for v in p] for _ in range(r-m)] if r > m else [])
    assert all(sum(row) == 1 for row in rows)
    assert all(sum(row[j] for row in rows) == 1 for j in range(r))
    return rows
