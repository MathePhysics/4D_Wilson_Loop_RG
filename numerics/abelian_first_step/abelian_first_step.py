"""Abelian (U(1)) Gaussian analogue of the first RG step for a square Wilson loop.

What is computed
----------------
Weak-coupling U(1) lattice gauge theory on a periodic d-torus, action (1/2g^2)|da|^2,
fine links a.  The coarse link is Balaban's averaged link, in its abelian (linear) form
(V5 eq. (nonlinear-average), RG1 (0.4)):

    b_c = L^-d sum_{x in B_y} avg_{gamma, gamma'} [ a(gamma) + a([x,x']) - a(gamma') ],

centred blocks B_y of odd side L, x' = x + L e_mu, gamma / gamma' ranging over the
path families G(y,x), G(y+L e_mu, x') (each nonzero coordinate displacement traversed in
one run, every ordering).  This is the linear map Q.

The fluctuation field is the Gaussian field with Q a = 0 (and a gauge condition).  For a
closed contour with link current J the fluctuation factor in the first-step expansion
W_fine(C) ~ kappa_C W_coarse(C) is, in this Gaussian analogue,

    kappa_C = exp(-(g^2/2) E_f),    E_f = J^T Gamma J,

with Gamma the covariance (at g = 1) of the constrained field.  Two gauge conditions:
  'landau' : fluctuation in S = {Q a = 0, div a = 0}, covariance Pi (Pi A Pi)^+ Pi
  'xi1'    : Q a = 0 with Feynman weight  A + div^T div  (conditional covariance)
The loop is gauge invariant, but conditioning on Q a (which is only gauge covariant)
makes E_f depend on the gauge condition, so the constants alpha, beta are
prescription dependent -- as the programme's delta m^sigma is.

Everything is done by Bloch decomposition over the coarse lattice (period L fine sites).
"""
import itertools
import numpy as np
import scipy.sparse as sp


# ---------------------------------------------------------------- lattice bookkeeping
class Lat:
    def __init__(self, d, L, K):
        assert L % 2 == 1
        self.d, self.L, self.K = d, L, K
        self.h = (L - 1) // 2
        self.N = L * K
        self.ns = self.N ** d
        self.shape = (self.N,) * d

    def site(self, X):
        """linear index of fine site with integer coordinates X (any ints, wrapped)."""
        idx = 0
        for c in X:
            idx = idx * self.N + (int(c) % self.N)
        return idx

    def link(self, X, mu):
        return mu * self.ns + self.site(X)

    @property
    def nl(self):
        return self.d * self.ns

    def coords(self):
        return np.array(np.unravel_index(np.arange(self.ns), self.shape)).T  # (ns, d)

    def cell_offset(self, X):
        """coarse cell Y and centred offset n of fine coordinate X (per direction)."""
        X = np.asarray(X)
        Y = np.floor_divide(X + self.h, self.L)
        return Y, X - self.L * Y


def curl_operator(lat):
    """d: link space -> plaquette space, (da)_{mu nu}(x) = a_nu(x+mu)-a_nu(x)-a_mu(x+nu)+a_mu(x)."""
    d, ns = lat.d, lat.ns
    C = lat.coords()
    rows, cols, vals = [], [], []
    pl = 0
    for mu in range(d):
        for nu in range(mu + 1, d):
            xm = C.copy(); xm[:, mu] += 1
            xn = C.copy(); xn[:, nu] += 1
            r = pl * ns + np.arange(ns)
            def lid(X, m):
                idx = np.zeros(len(X), dtype=np.int64)
                for k in range(d):
                    idx = idx * lat.N + (X[:, k] % lat.N)
                return m * ns + idx
            for X, m, s in ((xm, nu, 1.0), (C, nu, -1.0), (xn, mu, -1.0), (C, mu, 1.0)):
                rows.append(r); cols.append(lid(X, m)); vals.append(np.full(ns, s))
            pl += 1
    return sp.csr_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))),
                         shape=(pl * ns, lat.nl))


def div_operator(lat):
    """(div a)(x) = sum_mu [a_mu(x) - a_mu(x-mu)]."""
    d, ns = lat.d, lat.ns
    C = lat.coords()
    rows, cols, vals = [], [], []
    r = np.arange(ns)
    for mu in range(d):
        xb = C.copy(); xb[:, mu] -= 1
        def lid(X, m):
            idx = np.zeros(len(X), dtype=np.int64)
            for k in range(d):
                idx = idx * lat.N + (X[:, k] % lat.N)
            return m * ns + idx
        rows += [r, r]; cols += [lid(C, mu), lid(xb, mu)]; vals += [np.ones(ns), -np.ones(ns)]
    return sp.csr_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))),
                         shape=(ns, lat.nl))


def _run_links(lat, start, nu, m):
    """links (as dict link->coef) of the straight run from `start` by displacement m along nu."""
    out = {}
    p = np.array(start)
    step = 1 if m > 0 else -1
    for _ in range(abs(m)):
        if step == 1:
            out[lat.link(p, nu)] = out.get(lat.link(p, nu), 0.0) + 1.0
            p[nu] += 1
        else:
            p[nu] -= 1
            out[lat.link(p, nu)] = out.get(lat.link(p, nu), 0.0) - 1.0
    return out


def _path_avg(lat, centre, n):
    """average over orderings of the link-coefficient vector of a path centre -> centre+n."""
    nz = [k for k in range(lat.d) if n[k] != 0]
    if not nz:
        return {}
    acc = {}
    perms = list(itertools.permutations(nz))
    for perm in perms:
        p = np.array(centre)
        for nu in perm:
            for l, c in _run_links(lat, p, nu, int(n[nu])).items():
                acc[l] = acc.get(l, 0.0) + c / len(perms)
            p[nu] += n[nu]
    return acc


def averaging_operator(lat):
    """Q: link space -> coarse link space; rows indexed (mu, coarse site Y linear)."""
    d, L, K, h = lat.d, lat.L, lat.K, lat.h
    nY = K ** d
    offs = list(itertools.product(range(-h, h + 1), repeat=d))
    rows, cols, vals = [], [], []
    for Yc in itertools.product(range(K), repeat=d):
        Yl = 0
        for c in Yc:
            Yl = Yl * K + c
        y = np.array(Yc) * L
        for mu in range(d):
            row = mu * nY + Yl
            acc = {}
            yp = y.copy(); yp[mu] += L
            for n in offs:
                n = np.array(n)
                x = y + n
                for l, c in _path_avg(lat, y, n).items():
                    acc[l] = acc.get(l, 0.0) + c
                for l, c in _run_links(lat, x, mu, L).items():
                    acc[l] = acc.get(l, 0.0) + c
                for l, c in _path_avg(lat, yp, n).items():
                    acc[l] = acc.get(l, 0.0) - c
            for l, c in acc.items():
                rows.append(row); cols.append(l); vals.append(c / L ** d)
    return sp.csr_matrix((vals, (rows, cols)), shape=(d * nY, lat.nl))


# ---------------------------------------------------------------- Bloch blocks
def link_cell_index(lat):
    """for every fine link: (cell Y linear in K^d, local index (n,mu) in 0..d*L^d)."""
    d, L, K, h = lat.d, lat.L, lat.K, lat.h
    C = lat.coords()
    Y, n = lat.cell_offset(C)
    Y = Y % K
    Yl = np.zeros(lat.ns, dtype=np.int64)
    nl_ = np.zeros(lat.ns, dtype=np.int64)
    for k in range(d):
        Yl = Yl * K + Y[:, k]
        nl_ = nl_ * L + (n[:, k] + h)
    loc = np.concatenate([mu * L ** d + nl_ for mu in range(d)])
    cell = np.concatenate([Yl] * d)
    return cell, loc


def extract_blocks(O, lat, row_kind):
    """Blocks o_R (rows in cell R, columns in cell 0), R in {-1,0,1}^d, for a translation-
    covariant operator on a torus with K>=3.  row_kind: 'link' (rows are links),
    'coarse' (rows are (mu,Y)), 'site' (rows are sites)."""
    d, L, K = lat.d, lat.L, lat.K
    assert K >= 3
    cell_l, loc_l = link_cell_index(lat)
    cols0 = np.where(cell_l == 0)[0]
    cols0 = cols0[np.argsort(loc_l[cols0])]            # local order
    sub = sp.csc_matrix(O)[:, cols0].tocoo()
    if row_kind == 'link':
        rc, rl, nloc = cell_l[sub.row], loc_l[sub.row], d * L ** d
    elif row_kind == 'coarse':
        nY = K ** d
        rc, rl, nloc = sub.row % nY, sub.row // nY, d
    elif row_kind == 'site':
        C = lat.coords()
        Y, n = lat.cell_offset(C)
        Y = Y % K
        cs = np.zeros(lat.ns, dtype=np.int64); ls = np.zeros(lat.ns, dtype=np.int64)
        for k in range(d):
            cs = cs * K + Y[:, k]; ls = ls * L + (n[:, k] + lat.h)
        rc, rl, nloc = cs[sub.row], ls[sub.row], L ** d
    blocks = {}
    for R in itertools.product((-1, 0, 1), repeat=d):
        Rl = 0
        for r in R:
            Rl = Rl * K + (r % K)
        m = rc == Rl
        if not m.any():
            continue
        B = np.zeros((nloc, d * L ** d))
        np.add.at(B, (rl[m], sub.col[m]), sub.data[m])
        # sub.col indexes cols0 (already in local order)
        blocks[R] = B
    return blocks


def bloch(blocks, theta):
    out = None
    for R, B in blocks.items():
        ph = np.exp(-1j * float(np.dot(theta, R)))
        out = B * ph if out is None else out + B * ph
    return out


def null_space(M, tol=1e-9):
    u, s, vh = np.linalg.svd(M, full_matrices=True)
    r = int((s > tol * max(1.0, s.max())).sum())
    return vh[r:].conj().T


def gamma_apply(A, Q, D, Jhat, gauge):
    """return J^dagger Gamma J for one Bloch momentum."""
    if gauge == 'landau':
        N = null_space(np.vstack([Q, D]))
        Ar = N.conj().T @ A @ N
    elif gauge == 'xi1':
        N = null_space(Q)
        Ar = N.conj().T @ (A + D.conj().T @ D) @ N
    elif gauge == 'total':           # unconstrained, Feynman weight, zero modes dropped
        w, v = np.linalg.eigh(A + D.conj().T @ D)
        keep = w > 1e-10
        v = v[:, keep]; w = w[keep]
        c = v.conj().T @ Jhat
        return float(np.real(np.sum(np.abs(c) ** 2 / w)))
    else:
        raise ValueError(gauge)
    c = N.conj().T @ Jhat
    x = np.linalg.solve(Ar, c)
    return float(np.real(np.vdot(c, x)))


# ---------------------------------------------------------------- loops
def square_current(lat, n, plane=(0, 1), corner=None):
    """link current of a counter-clockwise square of side n*L fine units in `plane`."""
    d, L = lat.d, lat.L
    s = n * L
    mu, nu = plane
    J = np.zeros(lat.nl)
    p = np.zeros(d, dtype=int) if corner is None else np.array(corner)
    for direction, sign in ((mu, 1), (nu, 1), (mu, -1), (nu, -1)):
        for _ in range(s):
            if sign == 1:
                J[lat.link(p, direction)] += 1.0
                p[direction] += 1
            else:
                p[direction] -= 1
                J[lat.link(p, direction)] -= 1.0
    return J


def bloch_transform(lat, J):
    """J (links) -> array (K,)*d + (d*L^d,) of Bloch components, convention sum_Y f(Y) e^{-i theta Y}."""
    d, L, K = lat.d, lat.L, lat.K
    cell, loc = link_cell_index(lat)
    f = np.zeros((K ** d, d * L ** d))
    f[cell, loc] = J
    f = f.reshape((K,) * d + (d * L ** d,))
    return np.fft.fftn(f, axes=tuple(range(d)))


def momentum_list(d, K, plane, sym):
    """momenta (as integer tuples) with multiplicities.  For a loop in `plane` of a d>=3
    torus the energy is invariant under reflection of each transverse direction and under
    permutation of the transverse directions (the blocks and path families are symmetric),
    so transverse momenta are folded (exact, checked against sym=False in the tests)."""
    if not sym or d < 3:
        return [(k, 1.0) for k in itertools.product(range(K), repeat=d)]
    tr = [i for i in range(d) if i not in plane]
    fold = [(k, (1.0 if (k == 0 or 2 * k == K) else 2.0)) for k in range(K // 2 + 1)]
    out = []
    for kp in itertools.product(range(K), repeat=len(plane)):
        for combo in itertools.product(fold, repeat=len(tr)):
            ks = [c[0] for c in combo]
            if ks != sorted(ks):
                continue
            # multiplicity of the sorted tuple under permutations
            from collections import Counter
            from math import factorial
            cnt = Counter(ks)
            perm = factorial(len(ks))
            for v in cnt.values():
                perm //= factorial(v)
            w = float(perm)
            for c in combo:
                w *= c[1]
            k = [0] * d
            for i, p in enumerate(plane):
                k[p] = kp[i]
            for i, t in enumerate(tr):
                k[t] = ks[i]
            out.append((tuple(k), w))
    return out


def loop_energies(d, L, K, ns, gauges=('landau', 'xi1', 'total'), plane=(0, 1), sym=True, verbose=False):
    """E_f = J^T Gamma J for squares of side n*L (n in ns) on a torus of K coarse sites per direction."""
    lat3 = Lat(d, L, 3)
    A3 = (lambda c: (c.T @ c))(curl_operator(lat3))
    D3 = div_operator(lat3)
    Q3 = averaging_operator(lat3)
    bA = extract_blocks(A3, lat3, 'link')
    bD = extract_blocks(D3, lat3, 'site')
    bQ = extract_blocks(Q3, lat3, 'coarse')
    lat = Lat(d, L, K)
    Jh = {n: bloch_transform(lat, square_current(lat, n, plane)) for n in ns}
    res = {(g, n): 0.0 for g in gauges for n in ns}
    ks = momentum_list(d, K, plane, sym)
    for i, (k, w) in enumerate(ks):
        th = 2 * np.pi * np.array(k) / K
        A, Q, D = bloch(bA, th), bloch(bQ, th), bloch(bD, th)
        for n in ns:
            J = Jh[n][k]
            for g in gauges:
                res[(g, n)] += w * gamma_apply(A, Q, D, J, g)
        if verbose and i % 100 == 0:
            print(f"  momentum {i}/{len(ks)}", flush=True)
    return {key: v / K ** d for key, v in res.items()}
