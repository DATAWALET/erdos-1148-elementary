"""Verification of Theorem 4.2: exceptions below N = 250000 for Erdős #1148.

Two independent methods are run over all n <= N and must agree:
  (i)  exhaustive triple enumeration;
  (ii) Algorithm 1 (reduction theorem 3.1 + exact criterion lemma 4.1).

WLOG justification for (i): if n = a^2 + b^2 - c^2 with a^2, b^2, c^2 <= n, then
n >= a^2  => b >= c, and n >= b^2 => a >= c. Hence every valid representation has
c <= min(a, b), so enumerating 0 <= c <= min(a, b) is exhaustive.

License: MIT.
"""

import math

N = 250000


def is_prime(x):
    if x < 2:
        return False
    if x % 2 == 0:
        return x == 2
    f = 3
    while f * f <= x:
        if x % f == 0:
            return False
        f += 2
    return True


# ---------- method (i): exhaustive enumeration ----------
def brute_exceptions(N):
    M = math.isqrt(N)
    solvable = bytearray(N + 1)
    for a in range(M + 1):
        a2 = a * a
        for b in range(a, M + 1):          # b >= a WLOG (symmetric in a, b)
            base = a2 + b * b
            for c in range(a + 1):         # c <= min(a, b) = a
                n = base - c * c
                if 1 <= n <= N:
                    solvable[n] = 1
    return [n for n in range(1, N + 1) if not solvable[n]]


# ---------- Lemma 4.1: exact criterion ----------
def representable_by_criterion(n, m):
    """True iff exists a <= m with D = n - a^2 >= 0, D != 2 (mod 4), and D = u*v,
    u == v (mod 2), u + v <= 2m.  Searches a = m - t, t odd (t = 1, 3, 5, ...)."""
    r = n - m * m
    t = 1
    while m - t >= 0:
        D = r + 2 * m * t - t * t
        if D < 1:
            break
        if D <= m * m and D % 4 != 2:
            # look for same-parity factor pair u*v = D with u + v <= 2m
            u = 1
            while u * u <= D:
                if D % u == 0:
                    v = D // u
                    if (u + v) % 2 == 0 and u + v <= 2 * m:
                        return True
                u += 1
        t += 2
    return False


# ---------- method (ii): Algorithm 1 ----------
def fast_exceptions(N):
    out = []
    for n in range(1, N + 1):
        m = math.isqrt(n)
        r = n - m * m
        if r % 4 != 2:
            continue                      # Theorem 2.1, cases 1 and 2
        if m >= 5 and not is_prime(2 * m + r - 1):
            continue                      # Theorem 3.1 (reduction)
        if n > 25 and not representable_by_criterion(n, m):
            out.append(n)
        elif n <= 25 and not representable_by_criterion(n, m):
            out.append(n)
    return out


if __name__ == "__main__":
    ex_fast = fast_exceptions(N)
    print("Algorithm 1 exceptions:", len(ex_fast), "| max:", max(ex_fast))
    ex_brute = brute_exceptions(N)
    print("brute force exceptions:", len(ex_brute), "| max:", max(ex_brute))
    assert ex_fast == ex_brute, "methods disagree!"
    assert max(ex_brute) == 6563
    assert all(s not in ex_brute for s in range(6564, N + 1))
    print("AGREEMENT on all n <=", N)
    print(ex_brute)
