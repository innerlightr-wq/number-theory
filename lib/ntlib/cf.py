"""Continued fractions of a pinned slope interval, and convergents."""
__all__ = ["cf_pinned", "convergents"]


def cf_pinned(N, D, maxt=3000):
    """Partial quotients of a slope pinned to [N/D, (N+1)/D].

    Emits only the quotients that are certified by both endpoints, and stops as soon as
    the two disagree.  Never guesses.
    """
    out = []
    alo, ahi = N, N + 1
    dlo, dhi = D, D
    for _ in range(maxt):
        q1, q2 = alo // dlo, ahi // dhi
        if q1 != q2:
            return out
        out.append(q1)
        alo -= q1 * dlo
        ahi -= q2 * dhi
        if alo <= 0 or ahi <= 0:
            return out
        alo, dlo, ahi, dhi = dhi, ahi, dlo, alo
    return out


def convergents(a):
    """a = [a_1, a_2, ...] -> [(p_1,q_1), (p_2,q_2), ...] for [0; a_1, a_2, ...]."""
    pm, qm = 1, 0
    p0, q0 = 0, 1
    out = []
    for ai in a:
        p1, q1 = ai * p0 + pm, ai * q0 + qm
        out.append((p1, q1))
        pm, qm, p0, q0 = p0, q0, p1, q1
    return out
