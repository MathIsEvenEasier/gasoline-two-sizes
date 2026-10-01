"""Exact O(n)-arithmetic implementation for positive integer {1,K} inputs.

Implements the same position-first iterative rounding decisions, including
original-index tie breaking, via the score formula in research-notes.tex.
This module does not invoke an LP solver or use floating point.
"""
from collections import deque


def solve(x, y, record=False):
    if not x or len(x) != len(y):
        raise ValueError('Equal nonempty input lengths required')
    if any(type(v) is not int or v < 1 for v in list(x) + list(y)):
        raise ValueError('All input values must be positive integers')
    K = max(x)
    if set(x) - {1, K} or sum(x) != sum(y):
        raise ValueError('Supply sizes must be {1,K} and totals must agree')
    n, h = len(x), K-1
    d = [v-1 for v in y]
    D, T, V = ([0]*(n+1) for _ in range(3))
    total = 0
    for t in range(n-1, -1, -1):
        total += d[t]
        D[t] = max(0, d[t]-h+D[t+1])
        T[t] = max(T[t+1], total-h*(n-t-1))
        V[t] = max(V[t+1], d[t]+D[t+1])
    initial_lp = max(V[0], T[0]+D[0])+1
    queues = {value: deque(i for i,v in enumerate(x) if v == value)
              for value in set(x)}
    s = A = B = 0
    order, steps = [], []
    for t in range(n):
        R = d[t]+D[t+1]
        Bstar = max(B,T[t+1])
        F = max(V[t+1],Bstar-A,R)
        u, v = Bstar+R-s, s-A
        scores = {value: max(F,u-(value-1),v+(value-1))+1
                  for value,queue in queues.items() if queue}
        chosen = min(scores,key=lambda value:(scores[value],queues[value][0]))
        index = queues[chosen].popleft()
        if record:
            steps.append({'position':t,'candidate_values':scores,
                          'chosen_index':index,'chosen':chosen})
        order.append(chosen)
        B = max(B,s+chosen-1)
        s += chosen-1-d[t]
        A = min(A,s)
    assert s == 0
    result = {'order':order,'capacity':B-A+1,'initial_lp':initial_lp}
    if record:
        result['steps'] = steps
    return result
