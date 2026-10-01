"""Explicit family attaining IR / OPT = 2 - 2/K for every integer K >= 3.

The input order realizes the specified original-index tie rule. See the
sharpness theorem in research-notes.tex for the proof for arbitrary K.
"""


def instance(K):
    if type(K) is not int or K < 3:
        raise ValueError('The construction requires an integer K >= 3')
    h = K - 1
    x = [K, 1] * (h - 1) + [K]
    y = [2] + [v for j in range(1, h - 1) for v in (h - j, j + 2)] + [K, h]
    optimal_order = [1, K] * (h - 1) + [K]
    return x, y, optimal_order
