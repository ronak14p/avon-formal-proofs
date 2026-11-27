#!/usr/bin/env python3
# Non-Lean sanity check (NOT part of the proof): for n<=4 enumerate all subsets A of {0,1}^n, compute
# E = #edgeBoundary (ordered pairs x in A, y not in A, adjacent), V = #innerVertexBoundary, a = |A|, N = 2^n,
# and test (i) the invariant Q >= 0 and Q*V >= 12 a^2 (N-a)^2 with Q = 3N^2 E - 4(2a-N)a(N-a), and
# (ii) E*V >= 4^(n-1) for |A| = 2^(n-1) (n>=1).  Exact integer arithmetic.
import itertools
for n in range(1, 5):
    N = 1 << n
    nb = [[x ^ (1 << i) for i in range(n)] for x in range(N)]
    bad_inv = bad_half = 0; half_sets = 0; eq_half = 0
    for mask in range(1 << N):
        a = bin(mask).count("1")
        E = V = 0
        for x in range(N):
            if mask >> x & 1:
                h = sum(1 for y in nb[x] if not (mask >> y & 1))
                E += h; V += 1 if h else 0
        Q = 3 * N * N * E - 4 * (2 * a - N) * a * (N - a)
        if Q < 0 or Q * V < 12 * a * a * (N - a) ** 2: bad_inv += 1
        if a == N // 2:
            half_sets += 1
            if E * V < 4 ** (n - 1): bad_half += 1
            if E * V == 4 ** (n - 1): eq_half += 1
    print(f"n={n}: subsets={1<<N}, invariant violations={bad_inv}, half-size sets={half_sets}, EV<4^(n-1) violations={bad_half}, equality cases={eq_half}")
