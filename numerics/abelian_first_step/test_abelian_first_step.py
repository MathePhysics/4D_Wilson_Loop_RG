"""Checks for abelian_first_step.py.  Run:  python3 test_abelian_first_step.py"""
import itertools
import numpy as np
import abelian_first_step as af


def dense_E(lat, J, gauge):
    d = af.curl_operator(lat)
    D = af.div_operator(lat).toarray()
    Q = af.averaging_operator(lat).toarray()
    A = (d.T @ d).toarray()
    if gauge == 'landau':
        N = af.null_space(np.vstack([Q, D]))
        Ar = N.T @ A @ N
    elif gauge == 'xi1':
        N = af.null_space(Q)
        Ar = N.T @ (A + D.T @ D) @ N
    else:
        w, v = np.linalg.eigh(A + D.T @ D)
        k = w > 1e-10
        c = v[:, k].T @ J
        return float(np.sum(c ** 2 / w[k]))
    c = N.T @ J
    return float(c @ np.linalg.solve(Ar, c))


def test_gauge_covariance():
    """Q(d phi) = phi(c+) - phi(c-) at block centres (abelian version of V5 Lemma, (ii))."""
    for d, L in ((2, 3), (3, 3), (2, 5)):
        lat = af.Lat(d, L, 3)
        Q = af.averaging_operator(lat)
        rng = np.random.default_rng(1)
        phi = rng.normal(size=lat.ns)
        C = lat.coords()
        a = np.zeros(lat.nl)
        for mu in range(d):
            X = C.copy()
            X[:, mu] += 1
            idx = np.zeros(lat.ns, dtype=np.int64)
            for k in range(d):
                idx = idx * lat.N + (X[:, k] % lat.N)
            a[mu * lat.ns:(mu + 1) * lat.ns] = phi[idx] - phi
        b = Q @ a
        err = 0.0
        K = lat.K
        for Yc in itertools.product(range(K), repeat=d):
            Yl = 0
            for c in Yc:
                Yl = Yl * K + c
            y = np.array(Yc) * L
            for mu in range(d):
                yp = y.copy()
                yp[mu] += L
                err = max(err, abs(b[mu * K ** d + Yl] - (phi[lat.site(yp)] - phi[lat.site(y)])))
        print(f"gauge covariance d={d} L={L}: max err {err:.2e}")
        assert err < 1e-12


def test_loop_is_closed():
    lat = af.Lat(2, 3, 4)
    J = af.square_current(lat, 1)
    assert np.abs(af.div_operator(lat) @ J).max() < 1e-12


def test_bloch_matches_dense():
    for d, L, K, gs in ((2, 3, 4, ('landau', 'xi1', 'total')), (2, 5, 3, ('landau', 'xi1')),
                        (3, 3, 3, ('landau', 'xi1'))):
        lat = af.Lat(d, L, K)
        n = 1
        J = af.square_current(lat, n)
        bl = af.loop_energies(d, L, K, (n,), gauges=gs)
        for g in gs:
            de = dense_E(lat, J, g)
            print(f"d={d} L={L} K={K} n={n} {g}: bloch {bl[(g, n)]:.10f} dense {de:.10f}")
            assert abs(bl[(g, n)] - de) < 1e-8 * max(1, abs(de))


def test_constrained_below_total():
    """The constrained covariance is a conditional covariance: E_f <= E_total (xi=1)."""
    r = af.loop_energies(2, 3, 5, (1, 2), gauges=('xi1', 'total'))
    for n in (1, 2):
        assert r[('xi1', n)] <= r[('total', n)] + 1e-12


if __name__ == "__main__":
    test_gauge_covariance()
    test_loop_is_closed()
    test_bloch_matches_dense()
    test_constrained_below_total()
    print("all tests passed")
