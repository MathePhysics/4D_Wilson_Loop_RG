"""Fluctuation energy E_f = J^T Gamma J of an arbitrary closed lattice loop, in the abelian Gaussian analogue of `../abelian_first_step`.

The sibling module computes E_f for squares, folding momenta by symmetry.  Here the same operators (`Lat`, `curl_operator`, `div_operator`,
`averaging_operator`, `extract_blocks`, `bloch`, `null_space`, `bloch_transform`) are imported and applied to any closed link current,
with no momentum folding, so that rectangles, L-shapes and loops spanning three directions can be treated.  The per-momentum operators are
built once and applied to a whole list of loops.

A loop is a list of unit steps (axis, +1 or -1).  A start point other than the origin is given as (steps, start).

This is a sanity check of structure in the U(1) Gaussian analogue.  It does not test any bound or proof of the programme.
"""
import itertools
import os
import sys

import numpy as np

_HERE = os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(_HERE, "..", "abelian_first_step"))
import abelian_first_step as af  # noqa: E402

D, LB = 4, 3        # dimension and block side used throughout


# ---------------------------------------------------------------------------------------------- loops
def rect(a, b, plane=(0, 1)):
    mu, nu = plane
    return [(mu, 1)] * a + [(nu, 1)] * b + [(mu, -1)] * a + [(nu, -1)] * b


def skew(a, b, c):
    """Go a along axis 0, b along 1, c along 2, and back: a loop spanning three directions (six corners)."""
    return [(0, 1)] * a + [(1, 1)] * b + [(2, 1)] * c + [(0, -1)] * a + [(1, -1)] * b + [(2, -1)] * c


def lshape(a, b, c, d):
    """The a x b rectangle with a c x d corner removed (c < a, d < b), in the plane of axes 0, 1 (six corners)."""
    return [(0, 1)] * a + [(1, 1)] * d + [(0, -1)] * (a - c) + [(1, 1)] * (b - d) + [(0, -1)] * c + [(1, -1)] * b


def reverse(steps):
    return [(a, -s) for a, s in reversed(steps)]


def permute(steps, perm):
    return [(perm[a], s) for a, s in steps]


def counts(steps):
    """(number of links P, number of corners c); a corner is a place where consecutive steps differ."""
    P = len(steps)
    return P, sum(1 for i in range(P) if steps[i] != steps[(i + 1) % P])


def current(lat, steps, start=(0, 0, 0, 0)):
    J = np.zeros(lat.nl)
    p = np.array(start)
    for ax, sg in steps:
        if sg == 1:
            J[lat.link(p, ax)] += 1
            p[ax] += 1
        else:
            p[ax] -= 1
            J[lat.link(p, ax)] -= 1
    assert (p == np.array(start)).all(), "loop is not closed"
    return J


# ---------------------------------------------------------------------------------------------- energy
def _split(item):
    return (item, (0, 0, 0, 0)) if isinstance(item[0], tuple) else item


def energies(loops, K=6, gauge="landau"):
    """E_f for each loop on the 4-torus with K coarse sites per side (side 3K), blocks of side 3.

    gauge: 'landau' or 'xi1' (see ../abelian_first_step/README.md).  The result depends on the gauge condition, as the programme's own
    coefficients depend on its cutoff prescription.
    """
    lat3 = af.Lat(D, LB, 3)
    Cm = af.curl_operator(lat3)
    bA = af.extract_blocks(Cm.T @ Cm, lat3, "link")
    bD = af.extract_blocks(af.div_operator(lat3), lat3, "site")
    bQ = af.extract_blocks(af.averaging_operator(lat3), lat3, "coarse")
    lat = af.Lat(D, LB, K)
    items = [_split(x) for x in loops]
    Jh = [af.bloch_transform(lat, current(lat, s, st)) for s, st in items]
    res = np.zeros(len(items))
    for k in itertools.product(range(K), repeat=D):
        th = 2 * np.pi * np.array(k) / K
        A, Q, Dm = af.bloch(bA, th), af.bloch(bQ, th), af.bloch(bD, th)
        if gauge == "landau":
            N = af.null_space(np.vstack([Q, Dm]))
            Ar = N.conj().T @ A @ N
        elif gauge == "xi1":
            N = af.null_space(Q)
            Ar = N.conj().T @ (A + Dm.conj().T @ Dm) @ N
        else:
            raise ValueError(gauge)
        C = np.array([N.conj().T @ J[k] for J in Jh]).T
        X = np.linalg.solve(Ar, C)
        res += np.real(np.sum(C.conj() * X, axis=0))
    return res / K ** D


def fit(P, c, E):
    """Least squares E = alpha P + b c.  Returns (alpha, b)."""
    A = np.array([[p, k] for p, k in zip(P, c)], dtype=float)
    return tuple(np.linalg.lstsq(A, np.asarray(E, dtype=float), rcond=None)[0])


def loo_errors(P, c, E):
    """Leave-one-out prediction errors of the fit E = alpha P + b c."""
    P, c, E = (np.asarray(x, dtype=float) for x in (P, c, E))
    out = []
    for i in range(len(E)):
        m = np.arange(len(E)) != i
        a, b = fit(P[m], c[m], E[m])
        out.append(E[i] - (a * P[i] + b * c[i]))
    return np.array(out)


def link_contributions(loop, K=6, gauge="landau"):
    """E_f split over the links of one loop.

    Returns (E, c) with c[i] = J_l (Gamma J)_l for the i-th step of the loop (in the order of the steps), so that c.sum() = E (checked by the
    tests).  Gamma J is rebuilt in position space from the per-momentum solution, with the inverse of the convention of
    `abelian_first_step.bloch_transform`.  A link visited twice with opposite signs is counted at each visit.
    """
    steps, start = _split(loop)
    lat3 = af.Lat(D, LB, 3)
    Cm = af.curl_operator(lat3)
    bA = af.extract_blocks(Cm.T @ Cm, lat3, "link")
    bD = af.extract_blocks(af.div_operator(lat3), lat3, "site")
    bQ = af.extract_blocks(af.averaging_operator(lat3), lat3, "coarse")
    lat = af.Lat(D, LB, K)
    J = current(lat, steps, start)
    Jh = af.bloch_transform(lat, J)
    field = np.zeros(Jh.shape, dtype=complex)
    for k in itertools.product(range(K), repeat=D):
        th = 2 * np.pi * np.array(k) / K
        A, Q, Dm = af.bloch(bA, th), af.bloch(bQ, th), af.bloch(bD, th)
        if gauge == "landau":
            N = af.null_space(np.vstack([Q, Dm]))
            Ar = N.conj().T @ A @ N
        elif gauge == "xi1":
            N = af.null_space(Q)
            Ar = N.conj().T @ (A + Dm.conj().T @ Dm) @ N
        else:
            raise ValueError(gauge)
        field[k] = N @ np.linalg.solve(Ar, N.conj().T @ Jh[k])
    f = np.fft.ifftn(field, axes=tuple(range(D))).reshape(K ** D, -1)
    cell, loc = af.link_cell_index(lat)
    GJ = np.real(f[cell, loc])
    E = float(J @ GJ)
    c = []
    p = np.array(start)
    for ax, sg in steps:
        if sg == 1:
            l = lat.link(p, ax)
            p[ax] += 1
        else:
            p[ax] -= 1
            l = lat.link(p, ax)
        c.append(sg * GJ[l])      # J_l = sg on this visit
    return E, np.array(c)
