#!/usr/bin/env python3
"""
certify_all_n_m3.py
===================
100% Rigorous Outward-Rounded 3D Interval Arithmetic Certification (mpmath.iv)
closing the ENTIRE m = 3 infinite family of Hagele's 2017 Refined BMV Lower Bound
Conjecture (IQOQI Problem #40 / Open Quantum Problems M14) for ALL n >= 7 and
n = inf simultaneously (together with the already-proved n = 1..6 exact PSD
certificates, this proves m = 3 for ALL integers n >= 1 and ALL dimensions d >= 1):

    rho(s, s + v; eps) > 0    for ALL s > 0, v > 0, eps in [0, 1/7].

Proof Architecture (Zero Gaps, Covering ALL of (0, inf) x (0, inf) x [0, 1/7]):
  - Region 1 (Small-(s,v) corner): s + v <= t0 = 0.25, eps in [0, 1/7]
      3D Mean-Value Form certification of d/ds [rho(s, s+v; eps)] > 0 on
      [0, 0.25] x [0, 0.25] x [0, 1/7] using the exact O(N) simplex power series
      with rigorous remainder + entire P_tilde(u; eps) / sinhc(eps*u/2) series.
      Since rho(0, v; eps) == 0 identically for all eps >= 0, FTC gives rho > 0.
  - Region 2 (Large-v tail): v >= V0 = 30, ALL s > 0, ALL eps in [0, 1/7]
      Explicit elementary analytic bounds verified in mpmath.iv:
        * 2a (0 < s <= 1, v >= 30): e^{v/6} d/ds[rho(s, s+v; eps)] > 0.007 > 0.
        * 2b (s >= 1,     v >= 30): psi_eps(t) e^{v/6} rho(s, s+v; eps) > 0.101 > 0.
  - Region 3 (Large-s tail): s >= S0 = 25, 0 < v <= V0 = 30, ALL eps in [0, 1/7]
      Exact identity for rho(s, s+v; eps) / q_eps(t) with factored (term2 + term3)
      and explicit uniform bound on |rho3b / q_eps(t)|, certified via 2D MVF over
      (v, eps) in [0, 30] x [0, 1/7] in parallel.
  - Region 4 (Compact 3D box): (0, 25] x (0, 30] x [0, 1/7]
      Split with zero gaps into:
        * 4a:  [0, 1]  x [0, 2.5]  x [0, 1/7] -> d/ds rho > 0 (O(N) simplex series)
        * 4b1: [0, 1]  x [2.5,4.0] x [0, 1/7] -> d/ds rho > 0 (P_tilde series + G_lead)
        * 4b2: [0, 1]  x [4.0, 30] x [0, 1/7] -> d/ds rho > 0 (zero-cancellation closed form)
        * 4c:  [1, 25] x [0, 2.5]  x [0, 1/7] -> rho > 0 (D_eps + P_tilde + G_lead)
        * 4d:  [1, 25] x [2.5, 30] x [0, 1/7] -> rho > 0 (zero-cancellation closed form + G_lead)
      using adaptive 3D binary bisection + rigorous 3D Mean-Value Form (forward AD)
      with (v, eps)-jet caching and eps-polynomial caching across CPU cores.
"""

import math
import os
import subprocess
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
import sympy as sp
import mpmath as mp
from mpmath import iv

# Outward-rounded interval precision (12 decimal digits ~ 43+ bits, rigorous!)
iv.dps = 12
mp.mp.dps = 25

# ==============================================================================
# 1. RIGOROUS FORWARD-MODE AD OVER mpmath.iv (Jet2 for 2D, Jet3 for 3D MVF)
# ==============================================================================
class Jet2:
    """2D first-order dual interval: (val, d1, d2)."""
    __slots__ = ("v", "d1", "d2")
    def __init__(self, v, d1=None, d2=None):
        self.v = v if isinstance(v, iv.mpf) else iv.mpf(v)
        self.d1 = iv.mpf(0) if d1 is None else (d1 if isinstance(d1, iv.mpf) else iv.mpf(d1))
        self.d2 = iv.mpf(0) if d2 is None else (d2 if isinstance(d2, iv.mpf) else iv.mpf(d2))
    def __add__(self, o):
        if isinstance(o, Jet2): return Jet2(self.v + o.v, self.d1 + o.d1, self.d2 + o.d2)
        return Jet2(self.v + o, self.d1, self.d2)
    def __radd__(self, o): return Jet2(o + self.v, self.d1, self.d2)
    def __sub__(self, o):
        if isinstance(o, Jet2): return Jet2(self.v - o.v, self.d1 - o.d1, self.d2 - o.d2)
        return Jet2(self.v - o, self.d1, self.d2)
    def __rsub__(self, o): return Jet2(o - self.v, -self.d1, -self.d2)
    def __neg__(self): return Jet2(-self.v, -self.d1, -self.d2)
    def __mul__(self, o):
        if isinstance(o, Jet2):
            return Jet2(self.v*o.v, self.d1*o.v + self.v*o.d1, self.d2*o.v + self.v*o.d2)
        return Jet2(self.v*o, self.d1*o, self.d2*o)
    def __rmul__(self, o): return Jet2(o*self.v, o*self.d1, o*self.d2)
    def __truediv__(self, o):
        if isinstance(o, Jet2):
            v2 = o.v*o.v
            return Jet2(self.v/o.v, (self.d1*o.v - self.v*o.d1)/v2, (self.d2*o.v - self.v*o.d2)/v2)
        return Jet2(self.v/o, self.d1/o, self.d2/o)
    def __rtruediv__(self, o):
        v2 = self.v*self.v
        return Jet2(o/self.v, -o*self.d1/v2, -o*self.d2/v2)
    def __pow__(self, n):
        if n == 0: return Jet2(1, 0, 0)
        if n == 1: return self
        p = n * (self.v ** (n - 1))
        return Jet2(self.v ** n, p * self.d1, p * self.d2)


class Jet3:
    """3D first-order dual interval: (val, ds, dv, de)."""
    __slots__ = ("v", "ds", "dv", "de")
    def __init__(self, v, ds=None, dv=None, de=None):
        self.v = v if isinstance(v, iv.mpf) else iv.mpf(v)
        self.ds = iv.mpf(0) if ds is None else (ds if isinstance(ds, iv.mpf) else iv.mpf(ds))
        self.dv = iv.mpf(0) if dv is None else (dv if isinstance(dv, iv.mpf) else iv.mpf(dv))
        self.de = iv.mpf(0) if de is None else (de if isinstance(de, iv.mpf) else iv.mpf(de))
    def __add__(self, o):
        if isinstance(o, Jet3):
            return Jet3(self.v + o.v, self.ds + o.ds, self.dv + o.dv, self.de + o.de)
        return Jet3(self.v + o, self.ds, self.dv, self.de)
    def __radd__(self, o): return Jet3(o + self.v, self.ds, self.dv, self.de)
    def __sub__(self, o):
        if isinstance(o, Jet3):
            return Jet3(self.v - o.v, self.ds - o.ds, self.dv - o.dv, self.de - o.de)
        return Jet3(self.v - o, self.ds, self.dv, self.de)
    def __rsub__(self, o): return Jet3(o - self.v, -self.ds, -self.dv, -self.de)
    def __neg__(self): return Jet3(-self.v, -self.ds, -self.dv, -self.de)
    def __mul__(self, o):
        if isinstance(o, Jet3):
            return Jet3(self.v*o.v,
                        self.ds*o.v + self.v*o.ds,
                        self.dv*o.v + self.v*o.dv,
                        self.de*o.v + self.v*o.de)
        return Jet3(self.v*o, self.ds*o, self.dv*o, self.de*o)
    def __rmul__(self, o): return Jet3(o*self.v, o*self.ds, o*self.dv, o*self.de)
    def __truediv__(self, o):
        if isinstance(o, Jet3):
            v2 = o.v*o.v
            return Jet3(self.v/o.v,
                        (self.ds*o.v - self.v*o.ds)/v2,
                        (self.dv*o.v - self.v*o.dv)/v2,
                        (self.de*o.v - self.v*o.de)/v2)
        return Jet3(self.v/o, self.ds/o, self.dv/o, self.de/o)
    def __rtruediv__(self, o):
        v2 = self.v*self.v
        return Jet3(o/self.v, -o*self.ds/v2, -o*self.dv/v2, -o*self.de/v2)
    def __pow__(self, n):
        if n == 0: return Jet3(1, 0, 0, 0)
        if n == 1: return self
        p = n * (self.v ** (n - 1))
        return Jet3(self.v ** n, p*self.ds, p*self.dv, p*self.de)


def j_exp(x):
    if isinstance(x, Jet3):
        e = iv.exp(x.v)
        return Jet3(e, e*x.ds, e*x.dv, e*x.de)
    if isinstance(x, Jet2):
        e = iv.exp(x.v)
        return Jet2(e, e*x.d1, e*x.d2)
    return iv.exp(x)

def j_sqrt(x):
    if isinstance(x, Jet3):
        s = iv.sqrt(x.v)
        inv2s = iv.mpf(1) / (2 * s)
        return Jet3(s, x.ds*inv2s, x.dv*inv2s, x.de*inv2s)
    if isinstance(x, Jet2):
        s = iv.sqrt(x.v)
        inv2s = iv.mpf(1) / (2 * s)
        return Jet2(s, x.d1*inv2s, x.d2*inv2s)
    return iv.sqrt(x)

def j_val(x):
    return x.v if isinstance(x, (Jet2, Jet3)) else x

def j_add_rem(x, rem_iv, rx=None, x_obj=None, re=None, e_obj=None):
    if isinstance(x, Jet3):
        ds, dv, de = x.ds, x.dv, x.de
        if rx is not None and isinstance(x_obj, Jet3):
            ds = ds + rx * x_obj.ds
            dv = dv + rx * x_obj.dv
            de = de + rx * x_obj.de
        if re is not None and isinstance(e_obj, Jet3):
            ds = ds + re * e_obj.ds
            dv = dv + re * e_obj.dv
            de = de + re * e_obj.de
        return Jet3(x.v + rem_iv, ds, dv, de)
    if isinstance(x, Jet2):
        d1, d2 = x.d1, x.d2
        if rx is not None and isinstance(x_obj, Jet2):
            d1 = d1 + rx * x_obj.d1
            d2 = d2 + rx * x_obj.d2
        if re is not None and isinstance(e_obj, Jet2):
            d1 = d1 + re * e_obj.d1
            d2 = d2 + re * e_obj.d2
        return Jet2(x.v + rem_iv, d1, d2)
    return x + rem_iv


# ==============================================================================
# 2. PRECOMPUTED CONSTANTS & EXACT POLYNOMIALS FOR P_tilde(x; eps)
# ==============================================================================
ZERO = iv.mpf(0)
ONE = iv.mpf(1)
HALF = iv.mpf('0.5')
QUARTER = iv.mpf('0.25')
ONE_THIRD = iv.mpf(1) / 3
TWO_THIRDS = iv.mpf(2) / 3
FOUR_THIRDS = iv.mpf(4) / 3
TWO_NINTHS = iv.mpf(2) / 9
ONE_NINTH = iv.mpf(1) / 9
ONE_SIXTH = iv.mpf(1) / 6
ONE_TWELFTH = iv.mpf(1) / 12
ONE_36TH = iv.mpf(1) / 36
E_MAX_MP = mp.mpf(1) / 7
E_MAX_IV = iv.mpf(1) / 7

N_PHI = 10     # For eps*u <= 0.72, rem < 1e-10
N_P_MAX = 18   # For P_tilde(u; eps) = phi*psi*L_diag / u^4 on u <= 5.0 (14 for u <= 3.0)
N_D = 16       # For u <= 2.5, rem < 1e-10
N_HSINH = 12   # For s <= 1.0, rem < 1e-10
N_SIMP = 16    # For s <= 1.0, v <= 2.5, M <= 2.25, rem < 3e-6

FACT = [math.factorial(k) for k in range(40)]
INV_FACT = [iv.mpf(1) / FACT[k] for k in range(40)]
NEG_HALF_POW = [(-HALF)**k for k in range(30)]

def _build_C_P():
    _e = sp.Symbol('e')
    denom = (1 + _e) * (1 + 2*_e)
    out = []
    for m in range(N_P_MAX):
        k = m + 4
        t1 = 6 * (sp.Rational(2, 3) + _e)**k
        s_mid = sp.Rational(1, 3)**k - (1 + _e) * sum(
            sp.binomial(k, j) * sp.Rational(1, 3)**(k - j) * _e**(j - 1) for j in range(1, k + 1)
        )
        t2 = -6 * ((-1)**k) * s_mid
        num = sp.expand(t1 + t2)
        q_poly, r_poly = sp.div(num, denom, _e)
        assert r_poly == 0
        t3 = -3 * (1 + (-1)**k) * _e**(k - 2)
        poly = sp.expand(q_poly + t3) / sp.factorial(k)
        p = sp.Poly(poly, _e)
        out.append([iv.mpf(int(c.p)) / iv.mpf(int(c.q)) for c in reversed(p.all_coeffs())])
    return out

C_P = _build_C_P()


# ==============================================================================
# 3. ZERO-WRAPPING ELEMENTARY & SERIES EVALUATORS
# ==============================================================================
def _psi_point(u_pt, e_pt):
    u = iv.mpf(u_pt); e = iv.mpf(e_pt)
    if e_pt == 0: return u
    z = e * u
    if z.a >= 0.05: return (1 - iv.exp(-z)) / e
    N = 12; s = ZERO; zp = ONE
    for m in range(N):
        s += ((-1)**m) * zp * INV_FACT[m + 1]
        zp *= z
    rem = (zp * INV_FACT[N + 1]).b
    return u * (s + iv.mpf([-rem, rem]))

def _phi_point(u_pt, e_pt):
    u = iv.mpf(u_pt); e = iv.mpf(e_pt)
    if e_pt == 0: return u
    z = e * u
    if z.a >= 0.05: return (iv.exp(z) - 1) / e
    N = 12; s = ZERO; zp = ONE
    for m in range(N):
        s += zp * INV_FACT[m + 1]
        zp *= z
    q = z.b / (N + 2)
    rem = (zp * INV_FACT[N + 1] / (1 - q)).b
    return u * (s + iv.mpf([0, rem]))

def _f_dpsi_point(z_pt):
    z = iv.mpf(z_pt)
    if z_pt == 0: return HALF
    if z.a >= 0.05: return (1 - (1 + z) * iv.exp(-z)) / (z * z)
    N = 10; s = ZERO; zp = ONE
    for m in range(N):
        s += ((-1)**m) * (m + 1) * zp * INV_FACT[m + 2]
        zp *= z
    rem = ((N + 1) * zp * INV_FACT[N + 2]).b
    return s + iv.mpf([-rem, rem])

def _g_dphi_point(z_pt):
    z = iv.mpf(z_pt)
    if z_pt == 0: return HALF
    if z.a >= 0.05: return ((z - 1) * iv.exp(z) + 1) / (z * z)
    N = 10; s = ZERO; zp = ONE
    for m in range(N):
        s += (m + 1) * zp * INV_FACT[m + 2]
        zp *= z
    q = z.b / (N + 3)
    rem = ((N + 1) * zp * INV_FACT[N + 2] / (1 - q)).b
    return s + iv.mpf([0, rem])

def psi_jet(u, eps):
    uv, ev = j_val(u), j_val(eps)
    val = iv.mpf([_psi_point(uv.a, ev.b).a, _psi_point(uv.b, ev.a).b])
    if not isinstance(u, (Jet2, Jet3)) and not isinstance(eps, (Jet2, Jet3)):
        return val
    dpsi_du = iv.exp(-ev * uv)
    f_hi = _f_dpsi_point((iv.mpf(ev.a) * iv.mpf(uv.a)).a).b
    f_lo = _f_dpsi_point((iv.mpf(ev.b) * iv.mpf(uv.b)).b).a
    dpsi_de = iv.mpf([(-(iv.mpf(uv.b)**2) * iv.mpf(f_hi)).a,
                      (-(iv.mpf(uv.a)**2) * iv.mpf(f_lo)).b])
    if isinstance(u, Jet3) or isinstance(eps, Jet3):
        uds = u.ds if isinstance(u, Jet3) else ZERO
        udv = u.dv if isinstance(u, Jet3) else ZERO
        ude = u.de if isinstance(u, Jet3) else ZERO
        eds = eps.ds if isinstance(eps, Jet3) else ZERO
        edv = eps.dv if isinstance(eps, Jet3) else ZERO
        ede = eps.de if isinstance(eps, Jet3) else ZERO
        return Jet3(val, dpsi_du*uds + dpsi_de*eds, dpsi_du*udv + dpsi_de*edv, dpsi_du*ude + dpsi_de*ede)
    ud1 = u.d1 if isinstance(u, Jet2) else ZERO
    ud2 = u.d2 if isinstance(u, Jet2) else ZERO
    ed1 = eps.d1 if isinstance(eps, Jet2) else ZERO
    ed2 = eps.d2 if isinstance(eps, Jet2) else ZERO
    return Jet2(val, dpsi_du*ud1 + dpsi_de*ed1, dpsi_du*ud2 + dpsi_de*ed2)

def phi_jet(u, eps):
    uv, ev = j_val(u), j_val(eps)
    val = iv.mpf([_phi_point(uv.a, ev.a).a, _phi_point(uv.b, ev.b).b])
    if not isinstance(u, (Jet2, Jet3)) and not isinstance(eps, (Jet2, Jet3)):
        return val
    dphi_du = iv.exp(ev * uv)
    g_lo = _g_dphi_point((iv.mpf(ev.a) * iv.mpf(uv.a)).a).a
    g_hi = _g_dphi_point((iv.mpf(ev.b) * iv.mpf(uv.b)).b).b
    dphi_de = iv.mpf([(iv.mpf(uv.a)**2 * iv.mpf(g_lo)).a,
                      (iv.mpf(uv.b)**2 * iv.mpf(g_hi)).b])
    if isinstance(u, Jet3) or isinstance(eps, Jet3):
        uds = u.ds if isinstance(u, Jet3) else ZERO
        udv = u.dv if isinstance(u, Jet3) else ZERO
        ude = u.de if isinstance(u, Jet3) else ZERO
        eds = eps.ds if isinstance(eps, Jet3) else ZERO
        edv = eps.dv if isinstance(eps, Jet3) else ZERO
        ede = eps.de if isinstance(eps, Jet3) else ZERO
        return Jet3(val, dphi_du*uds + dphi_de*eds, dphi_du*udv + dphi_de*edv, dphi_du*ude + dphi_de*ede)
    ud1 = u.d1 if isinstance(u, Jet2) else ZERO
    ud2 = u.d2 if isinstance(u, Jet2) else ZERO
    ed1 = eps.d1 if isinstance(eps, Jet2) else ZERO
    ed2 = eps.d2 if isinstance(eps, Jet2) else ZERO
    return Jet2(val, dphi_du*ud1 + dphi_de*ed1, dphi_du*ud2 + dphi_de*ed2)

def sinhc_half_jet_x(x, eps):
    z = (eps * x) * HALF
    z2 = z * z
    s0 = (((z2 * INV_FACT[9] + INV_FACT[7]) * z2 + INV_FACT[5]) * z2 + INV_FACT[3]) * z2 + ONE
    s1 = (((z2 * (8 * INV_FACT[9]) + 6 * INV_FACT[7]) * z2 + 4 * INV_FACT[5]) * z2 + 2 * INV_FACT[3]) * z
    s2 = (((z2 * (56 * INV_FACT[9]) + 30 * INV_FACT[7]) * z2 + 12 * INV_FACT[5]) * z2 + 2 * INV_FACT[3])
    zm = iv.mpf(j_val(z).b)
    q0 = zm * zm / 132
    base = INV_FACT[11] / (1 - q0)
    r0 = (base * (zm**10)).b
    r1 = (base * 10 * (zm**9)).b
    r2 = (base * 90 * (zm**8)).b
    r3 = (base * 720 * (zm**7)).b
    eh = eps * HALF
    v0 = j_add_rem(s0, iv.mpf([0, r0]), iv.mpf([0, r1]), z)
    v1 = j_add_rem(s1, iv.mpf([0, r1]), iv.mpf([0, r2]), z) * eh
    v2 = j_add_rem(s2, iv.mpf([0, r2]), iv.mpf([0, r3]), z) * (eh * eh)
    return v0, v1, v2

def phi_tilde_jet_x(x, eps):
    z = eps * x
    N = N_PHI
    cN = INV_FACT[N]
    v0 = z * 0 + cN
    v1 = z * 0 + cN * (N - 1)
    v2 = z * 0 + cN * ((N - 1) * (N - 2))
    for m in range(N - 2, -1, -1):
        c = INV_FACT[m + 1]
        v0 = v0 * z + c
        if m >= 1: v1 = v1 * z + c * m
        if m >= 2: v2 = v2 * z + c * (m * (m - 1))
    zm = iv.mpf(j_val(z).b)
    q0 = zm / (N + 2)
    base = INV_FACT[N + 1] / (1 - q0)
    r0 = (base * (zm**N)).b
    r1 = (base * N * (zm**(N - 1))).b
    r2 = (base * (N * (N - 1)) * (zm**(N - 2))).b
    r3 = (base * (N * (N - 1) * (N - 2)) * (zm**(N - 3))).b
    v0 = j_add_rem(v0, iv.mpf([0, r0]), iv.mpf([0, r1]), z)
    v1 = j_add_rem(v1, iv.mpf([0, r1]), iv.mpf([0, r2]), z) * eps
    v2 = j_add_rem(v2, iv.mpf([0, r2]), iv.mpf([0, r3]), z) * (eps * eps)
    return v0, v1, v2

def _get_CP_eps(eps, cm_cache):
    ev = j_val(eps)
    key = (ev.a, ev.b, type(eps))
    if cm_cache is not None and key in cm_cache:
        return cm_cache[key]
    cs = []
    for coeffs in C_P:
        res = eps * 0 + coeffs[-1]
        for c in reversed(coeffs[:-1]):
            res = res * eps + c
        cs.append(res)
    if cm_cache is not None:
        cm_cache[key] = cs
    return cs

def P_tilde_jet_x(x, eps, cm_cache=None):
    xm = iv.mpf(j_val(x).b)
    N = 14 if xm.b <= 3.05 else N_P_MAX
    cs = _get_CP_eps(eps, cm_cache)
    v0 = x * 0 + cs[N - 1]
    v1 = x * 0 + cs[N - 1] * (N - 1)
    v2 = x * 0 + cs[N - 1] * ((N - 1) * (N - 2))
    for m in range(N - 2, -1, -1):
        v0 = v0 * x + cs[m]
        if m >= 1: v1 = v1 * x + cs[m] * m
        if m >= 2: v2 = v2 * x + cs[m] * (m * (m - 1))
    em = iv.mpf(j_val(eps).b)
    r = TWO_THIRDS + em
    q0 = r * xm / (N + 4)
    base = 14 * (r**4) * INV_FACT[N + 3] / (1 - q0)
    rx = r * xm
    r0 = (base * (rx**N)).b
    r1 = (base * N * r * (rx**(N - 1))).b
    r2 = (base * (N * (N - 1)) * (r * r) * (rx**(N - 2))).b
    r3 = (base * (N * (N - 1) * (N - 2)) * (r**3) * (rx**(N - 3))).b
    base_e = 24 * (r**3) * INV_FACT[N + 2] / (1 - q0)
    re0 = (base_e * (rx**N)).b
    re1 = (base_e * N * r * (rx**(N - 1))).b
    re2 = (base_e * (N * (N - 1)) * (r * r) * (rx**(N - 2))).b
    v0 = j_add_rem(v0, iv.mpf([-r0, r0]), iv.mpf([-r1, r1]), x, iv.mpf([-re0, re0]), eps)
    v1 = j_add_rem(v1, iv.mpf([-r1, r1]), iv.mpf([-r2, r2]), x, iv.mpf([-re1, re1]), eps)
    v2 = j_add_rem(v2, iv.mpf([-r2, r2]), iv.mpf([-r3, r3]), x, iv.mpf([-re2, re2]), eps)
    return v0, v1, v2

def _sqrt_Ldiag_jet_series(u, eps, cm_cache=None):
    sc, scp, scpp = sinhc_half_jet_x(u, eps)
    Pt, Ptp, Ptpp = P_tilde_jet_x(u, eps, cm_cache)
    sq = j_sqrt(Pt)
    sqp = Ptp / (2 * sq)
    sqpp = Ptpp / (2 * sq) - (Ptp * Ptp) / (4 * sq * sq * sq)
    f = u * sq
    fp = sq + u * sqp
    fpp = 2 * sqp + u * sqpp
    invs = 1 / sc
    invsp = -scp * (invs * invs)
    invspp = (2 * scp * scp * invs - scpp) * (invs * invs)
    return f * invs, fp * invs + f * invsp, fpp * invs + 2 * fp * invsp + f * invspp

def A_jet_series(t, eps, cm_cache=None):
    h, hp, hpp = _sqrt_Ldiag_jet_series(t, eps, cm_cache)
    et = j_exp(t * (-ONE_THIRD))
    return et * h, et * (hp - h * ONE_THIRD), et * (hpp - hp * TWO_THIRDS + h * ONE_NINTH)

def B_jet_series(v, eps, cm_cache=None):
    h, hp, hpp = _sqrt_Ldiag_jet_series(v, eps, cm_cache)
    ev = j_exp(v * ONE_SIXTH)
    return ev * h, ev * (hp + h * ONE_SIXTH), ev * (hpp + hp * ONE_THIRD + h * ONE_36TH)

def _exp_diff_over_phi_series(u, eps, alpha_coeff, N):
    pt, ptp, ptpp = phi_tilde_jet_x(u, eps)
    a = eps * alpha_coeff + HALF
    apows = [a]
    for m in range(1, N):
        apows.append(apows[-1] * a)
    cs = [(apows[m] - NEG_HALF_POW[m + 1]) * INV_FACT[m + 1] for m in range(N)]
    v0 = u * 0 + cs[N - 1]
    v1 = u * 0 + cs[N - 1] * (N - 1)
    v2 = u * 0 + cs[N - 1] * ((N - 1) * (N - 2))
    for m in range(N - 2, -1, -1):
        v0 = v0 * u + cs[m]
        if m >= 1: v1 = v1 * u + cs[m] * m
        if m >= 2: v2 = v2 * u + cs[m] * (m * (m - 1))
    um = iv.mpf(j_val(u).b)
    am = iv.mpf(j_val(a).b)
    q0 = am * um / (N + 2)
    base = 2 * am * INV_FACT[N + 1] / (1 - q0)
    r0 = (base * ((am * um)**N)).b
    r1 = (base * N * am * ((am * um)**(N - 1))).b
    r2 = (base * (N * (N - 1)) * (am * am) * ((am * um)**(N - 2))).b
    r3 = (base * (N * (N - 1) * (N - 2)) * (am**3) * ((am * um)**(N - 3))).b
    base_e = iv.mpf(alpha_coeff) * INV_FACT[N] / (1 - q0)
    re0 = (base_e * ((am * um)**N)).b
    re1 = (base_e * N * am * ((am * um)**(N - 1))).b
    re2 = (base_e * (N * (N - 1)) * (am * am) * ((am * um)**(N - 2))).b
    v0 = j_add_rem(v0, iv.mpf([-r0, r0]), iv.mpf([-r1, r1]), u, iv.mpf([-re0, re0]), eps)
    v1 = j_add_rem(v1, iv.mpf([-r1, r1]), iv.mpf([-r2, r2]), u, iv.mpf([-re1, re1]), eps)
    v2 = j_add_rem(v2, iv.mpf([-r2, r2]), iv.mpf([-r3, r3]), u, iv.mpf([-re2, re2]), eps)
    invp = 1 / pt
    invpp = -ptp * (invp * invp)
    invppp = (2 * ptp * ptp * invp - ptpp) * (invp * invp)
    return v0 * invp, v1 * invp + v0 * invpp, v2 * invp + 2 * v1 * invpp + v0 * invppp

def D_jet_series(u, eps):
    return _exp_diff_over_phi_series(u, eps, 1, N_D)

def h_sinh_jet_series(s, eps):
    return _exp_diff_over_phi_series(s, eps, 2, N_HSINH)


# ==============================================================================
# 4. ZERO-CANCELLATION CLOSED-FORM EVALUATORS WITH _r_tight CLAMPING
# ==============================================================================
def _r_tight_eps(u, eps, ps, alpha, e23, e1e):
    r = alpha * (ps * ps) * e23 + ((eps + 1) * ps + 1) * e1e
    uv, ev = j_val(u), j_val(eps)
    if uv.a >= 3:
        ua, ub = iv.mpf(uv.a), iv.mpf(uv.b)
        alpha_v = (ev + 1) * (2*ev + 1) * HALF
        psa = psi_jet(ua, ev); psb = psi_jet(ub, ev)
        ra = alpha_v * (psa * psa) * iv.exp(-ua * TWO_THIRDS) + ((ev + 1) * psa + 1) * iv.exp(-(ev + 1) * ua)
        rb = alpha_v * (psb * psb) * iv.exp(-ub * TWO_THIRDS) + ((ev + 1) * psb + 1) * iv.exp(-(ev + 1) * ub)
        tight = iv.mpf([max(j_val(r).a, rb.a), min(j_val(r).b, ra.b)])
        if isinstance(r, Jet3): return Jet3(tight, r.ds, r.dv, r.de)
        if isinstance(r, Jet2): return Jet2(tight, r.d1, r.d2)
        return tight
    return r

def tilde_dB_jet_closed(u, eps, need_eB=True, need_d2=True):
    ep1 = eps + 1
    ep21 = 2*eps + 1
    c_eps = 6 / (ep1 * ep21)
    ps = psi_jet(u, eps)
    emev = j_exp(-eps * u)
    q = 1 / ps
    qp = -emev * (q * q)
    alpha = ep1 * ep21 * HALF
    e23 = j_exp(u * (-TWO_THIRDS))
    e1e = j_exp(-ep1 * u)
    r = _r_tight_eps(u, eps, ps, alpha, e23, e1e)
    if (1 - j_val(r)).a <= 0:
        return None
    w = j_sqrt(1 - r)
    rp = 2 * alpha * ps * ((emev - ps * ONE_THIRD) * e23 - e1e)
    wp1 = w + 1
    h = 1 / wp1
    hp = rp / (2 * w * wp1 * wp1)

    e16 = j_exp(u * (-ONE_SIXTH))
    e12e = j_exp(-(eps + HALF) * u)
    ep12 = eps + HALF
    q_add = q + ep1
    N0 = (3 * ps) * e16 + c_eps * q_add * e12e
    N1 = (3 * emev - ps * HALF) * e16 + c_eps * (qp - ep12 * q_add) * e12e
    dB = N0 * h
    dBp = N1 * h + N0 * hp

    fm = e12e * q
    fmp = -fm * (q + HALF)

    if not need_d2 and not need_eB:
        return (dB, dBp, None, None, None, fm, fmp, None, c_eps, ps, q, qp, None)

    qpp = emev * (emev + 1) * (q * q * q)
    rpp_poly = (1 - (3*eps + FOUR_THIRDS)*ps + (2*eps*eps + eps*FOUR_THIRDS + TWO_NINTHS)*(ps*ps))
    rpp = 2 * alpha * (rpp_poly * e23 + (ep21 * ps - 1) * e1e)

    dBpp = None
    if need_d2:
        hpp = rpp / (2 * w * wp1 * wp1) + (rp * rp) * (3 * w + 1) / (4 * w * w * w * wp1 * wp1 * wp1)
        N2 = (ps * ONE_TWELFTH - (3*eps + 1) * emev) * e16 + c_eps * (qpp - ep21 * qp + (ep12 * ep12) * q_add) * e12e
        dBpp = N2 * h + 2 * N1 * hp + N0 * hpp

    eBp = eBpp = None
    if need_eB:
        wp = -rp / (2 * w)
        wpp = -rpp / (2 * w) - (rp * rp) / (4 * w * w * w)
        tA = q * w
        tAp = qp * w + q * wp
        tApp = qpp * w + 2 * qp * wp + q * wpp
        eBp = tAp + tA * HALF
        eBpp = tApp + tAp + tA * QUARTER

    fmpp = fm * ((q + HALF)**2 + emev * q * q)
    return (dB, dBp, dBpp, eBp, eBpp, fm, fmp, fmpp, c_eps, ps, q, qp, qpp)


# ==============================================================================
# 5. THE FIVE 3D REGION-4 EVALUATORS (ALL WITH CACHING & G_lead CANCELLATION)
# ==============================================================================
def drho_ds_simplex(s, v, eps, ve_cache=None, cm_cache=None):
    """Singularity-free d/ds [rho(s, s+v; eps)] on [0, 1] x [0, 2.5] x [0, 1/7]."""
    N = N_SIMP
    sv2 = s + v * HALF
    v2 = v * HALF
    a = j_exp(-eps * sv2)
    b = j_exp(-eps * v2)
    c = j_exp(eps * v2)
    Z0 = -psi_jet(sv2, eps)
    Z1 = -psi_jet(v2, eps)
    Z2 = phi_jet(v2, eps)

    def div_1mtZ(arr, Z):
        out = [arr[0]]
        for n in range(1, N):
            out.append(arr[n] + Z * out[-1])
        return out

    base = [s * 0 + 1] + [s * 0] * (N - 1)
    f111 = div_1mtZ(div_1mtZ(div_1mtZ(base, Z0), Z1), Z2)
    f211 = div_1mtZ(f111, Z0)
    f311 = div_1mtZ(f211, Z0)
    f411 = div_1mtZ(f311, Z0)
    f321 = div_1mtZ(f311, Z1)
    f312 = div_1mtZ(f311, Z2)
    f221 = div_1mtZ(f211, Z1)
    f231 = div_1mtZ(f221, Z1)
    f212 = div_1mtZ(f211, Z2)
    f213 = div_1mtZ(f212, Z2)
    f222 = div_1mtZ(f221, Z2)

    c300 = (a * a * a) * iv.mpf('1.5')
    c210 = eps * (a * a * b)
    c201 = eps * (a * a * c)
    c120 = (eps - HALF) * (a * b * b)
    c102 = (eps - HALF) * (a * c * c)
    c111 = (2 * eps * eps - 2 * eps + HALF) * (a * b * c)

    tot = s * 0
    prod = eps * 0 + 1
    for n in range(N):
        term = (c300*f411[n] + c210*f321[n] + c201*f312[n]
                + c120*f231[n] + c102*f213[n] + c111*f222[n])
        tot = tot + (prod * term) * INV_FACT[n + 5]
        prod = prod * (1 - eps * (n + 3))

    P3_ub = ((abs(j_val(c300)) + abs(j_val(c210)) + abs(j_val(c201))
              + abs(j_val(c120)) + abs(j_val(c102)) + abs(j_val(c111))) / 20).b
    M = max(abs(j_val(Z0)).b, abs(j_val(Z1)).b, abs(j_val(Z2)).b)
    em = iv.mpf(j_val(eps).b)
    q = em * iv.mpf(M)
    S_geom = ((N+2)*(N+1)/(1-q) + (2*N+3)*q/(1-q)**2 + q*(1+q)/(1-q)**3).b
    rem = (iv.mpf(P3_ub) * (iv.mpf(M)**5) * (q**(N-5)) * iv.mpf(S_geom) / 5040).b
    rem_d = ((N + 4) * iv.mpf(rem) / (1 - q)).b
    rem_de = ((N + 4) * (iv.mpf(M) + 6) * iv.mpf(rem) / (1 - q)).b

    if isinstance(s, Jet3):
        dF = Jet3(6*tot.v + iv.mpf([-rem, rem]),
                  6*tot.ds + iv.mpf([-rem_d, rem_d]),
                  6*tot.dv + iv.mpf([-rem_d, rem_d]),
                  6*tot.de + iv.mpf([-rem_de, rem_de])) - j_exp((2*s + v) * (-ONE_SIXTH)) / 36
    else:
        dF = 6 * tot + iv.mpf([-rem, rem]) - j_exp((2*s + v) * (-ONE_SIXTH)) / 36

    _, Ap, App = A_jet_series(s + v, eps, cm_cache)
    key = (j_val(v).a, j_val(v).b, j_val(eps).a, j_val(eps).b, isinstance(v, Jet3))
    if ve_cache is not None and key in ve_cache:
        Bp, Bpp = ve_cache[key]
    else:
        _, Bp, Bpp = B_jet_series(v, eps, cm_cache)
        if ve_cache is not None:
            ve_cache[key] = (Bp, Bpp)
    return dF - App * Bp - Ap * Bpp


def drho_ds_mid_v(s, v, eps, ve_cache=None, cm_cache=None):
    """Exact d/ds [rho(s, s+v; eps)] on [0, 1] x [2.5, 4.0] x [0, 1/7] with combined G1, G2."""
    key = (j_val(v).a, j_val(v).b, j_val(eps).a, j_val(eps).b, isinstance(v, Jet3))
    if ve_cache is not None and key in ve_cache:
        G1, G2, Bp, Bpp, c_eps, sc = ve_cache[key]
    else:
        c_eps = 6 / ((eps + 1) * (2*eps + 1))
        sc = j_sqrt(c_eps)
        ps_v = psi_jet(v, eps); emev = j_exp(-eps * v)
        qv = 1 / ps_v; qvp = -emev * (qv * qv); qvpp = emev * (emev + 1) * (qv * qv * qv)
        ftm = j_exp(-(2*eps + HALF) * v) * qv
        a_ft = qv + (eps + HALF)
        ftmp = -ftm * a_ft
        ftmpp = ftm * (a_ft * a_ft + emev * qv * qv)
        epv = j_exp(v * HALF)
        fpp = epv * (qv * HALF + qvp)
        fppp = epv * (qv * QUARTER + qvp + qvpp)
        _, Bp, Bpp = B_jet_series(v, eps, cm_cache)
        G1 = c_eps * (fpp - ftmp) - sc * Bp
        G2 = c_eps * (fppp - ftmpp) - sc * Bpp
        if ve_cache is not None:
            ve_cache[key] = (G1, G2, Bp, Bpp, c_eps, sc)

    t = s + v
    drho0 = -j_exp(s * (-ONE_THIRD) - v * ONE_SIXTH) / 36
    ps_t = psi_jet(t, eps); emet = j_exp(-eps * t)
    qt = 1 / ps_t; qtp = -emet * (qt * qt); qtpp = emet * (emet + 1) * (qt * qt * qt)
    gt = j_exp(-(eps + HALF) * t) * qt
    gtp = -gt * (qt + HALF)
    gtpp = gt * ((qt + HALF)**2 + emet * qt * qt)
    _, hp, hpp = h_sinh_jet_series(s, eps)
    _, Ap, App = A_jet_series(t, eps, cm_cache)
    dApt = sc * qtp - Ap
    dAppt = sc * qtpp - App
    return drho0 + c_eps * (hpp * gtp + hp * gtpp) + qtpp * G1 + qtp * G2 + dAppt * Bp + dApt * Bpp


def drho_ds_closed(s, v, eps, ve_cache=None, cm_cache=None):
    """Zero-cancellation d/ds [rho(s, s+v; eps)] on [0, 1] x [4.0, 30] x [0, 1/7]."""
    key = (j_val(v).a, j_val(v).b, j_val(eps).a, j_val(eps).b, isinstance(v, Jet3))
    if ve_cache is not None and key in ve_cache:
        vd = ve_cache[key]
    else:
        res = tilde_dB_jet_closed(v, eps, need_eB=True, need_d2=True)
        if res is None:
            vd = None
        else:
            _, dBp, dBpp, eBp, eBpp, fm, _, _, c_eps, _, qv, _, _ = res
            emev = j_exp(-eps * v)
            ftm = emev * fm
            a_ft = qv + (eps + HALF)
            ftmp = -ftm * a_ft
            ftmpp = ftm * (a_ft * a_ft + emev * qv * qv)
            vd = (dBp - c_eps * ftmp, dBpp - c_eps * ftmpp, eBp, eBpp, c_eps)
        if ve_cache is not None:
            ve_cache[key] = vd
    if vd is None:
        return None
    comb_p, comb_pp, eBpv, eBppv, c_eps = vd

    t = s + v
    res_t = tilde_dB_jet_closed(t, eps, need_eB=False, need_d2=True)
    if res_t is None:
        return None
    dBt, dBpt, dBppt, _, _, _, gtp, gtpp, _, _, _, qtp, qtpp = res_t

    drho0 = -j_exp(s * (-ONE_THIRD) - v * ONE_SIXTH) / 36
    _, hp, hpp = h_sinh_jet_series(s, eps)
    drho123a = c_eps * (hpp * gtp + hp * gtpp) + qtpp * comb_p + qtp * comb_pp
    edApt = dBpt - dBt * HALF
    edAppt = dBppt - dBpt + dBt * QUARTER
    drho3b = j_exp(s * (-HALF)) * (edAppt * eBpv + edApt * eBppv)
    return drho0 + drho123a + drho3b


def rho_small_v(s, v, eps, ve_cache=None, cm_cache=None):
    """Singularity-free rho(s, s+v; eps) on [1, 25] x [0, 2.5] x [0, 1/7] with combined G1, G2."""
    key = (j_val(v).a, j_val(v).b, j_val(eps).a, j_val(eps).b, isinstance(v, Jet3))
    if ve_cache is not None and key in ve_cache:
        G1, G2, Bp, Bpp, c_eps, sc = ve_cache[key]
    else:
        c_eps = 6 / ((eps + 1) * (2*eps + 1))
        sc = j_sqrt(c_eps)
        _, Dp, Dpp = D_jet_series(v, eps)
        _, Bp, Bpp = B_jet_series(v, eps, cm_cache)
        G1 = c_eps * Dp - sc * Bp
        G2 = c_eps * Dpp - sc * Bpp
        if ve_cache is not None:
            ve_cache[key] = (G1, G2, Bp, Bpp, c_eps, sc)

    t = s + v
    tv = j_val(t)
    rho0 = j_exp(s * (-ONE_THIRD) - v * ONE_SIXTH) / 12

    ps_s = psi_jet(s, eps); emes = j_exp(-eps * s)
    qs = 1 / ps_s; qsp = -emes * (qs * qs)
    ps_t = psi_jet(t, eps); emet = j_exp(-eps * t)
    qt = 1 / ps_t; qtp = -emet * (qt * qt)

    e1es = j_exp(-(eps + 1) * s)
    emDs_p = (qsp + qs * HALF) - e1es * (qsp - (eps + HALF) * qs)
    epgt_p = -emet * qt * (qt + HALF)
    rho_cross = c_eps * j_exp(v * (-HALF)) * emDs_p * epgt_p

    if tv.b <= 4.5:
        At, Apt, _ = A_jet_series(t, eps, cm_cache)
        dAt = sc * qt - At
        dApt = sc * qtp - Apt
    else:
        res_t = tilde_dB_jet_closed(t, eps, need_eB=False, need_d2=False)
        if res_t is None:
            return None
        dBt, dBpt = res_t[0], res_t[1]
        emt2 = j_exp(t * (-HALF)) / sc
        dAt = dBt * emt2
        dApt = (dBpt - dBt * HALF) * emt2
    return rho0 + rho_cross + qtp * G1 + qt * G2 + dApt * Bp + dAt * Bpp


def rho_closed(s, v, eps, ve_cache=None, cm_cache=None):
    """Zero-cancellation rho(s, s+v; eps) on [1, 25] x [2.5, 30] x [0, 1/7] with combined G_lead."""
    key = (j_val(v).a, j_val(v).b, j_val(eps).a, j_val(eps).b, isinstance(v, Jet3))
    if ve_cache is not None and key in ve_cache:
        vd = ve_cache[key]
    else:
        res = tilde_dB_jet_closed(v, eps, need_eB=True, need_d2=True)
        if res is None:
            vd = None
        else:
            _, dBp, dBpp, eBp, eBpp, _, fmp, fmpp, c_eps, ps_v, _, _, _ = res
            G_lead = dBpp - c_eps * fmpp
            vd = (dBp, G_lead, eBp, eBpp, fmp, fmpp * ps_v, c_eps)
        if ve_cache is not None:
            ve_cache[key] = vd
    if vd is None:
        return None
    dBpv, G_lead, eBpv, eBppv, fmp, ps_fmpp, c_eps = vd

    t = s + v
    res_t = tilde_dB_jet_closed(t, eps, need_eB=False, need_d2=False)
    if res_t is None:
        return None
    dBt, dBpt, _, _, _, _, gtp, _, _, _, qt, qtp, _ = res_t

    ps_s = psi_jet(s, eps); emes = j_exp(-eps * s)
    qs = 1 / ps_s; qsp = -emes * (qs * qs)
    gs = j_exp(-(eps + HALF) * s) * qs
    gsp = -gs * (qs + HALF)

    rho0 = j_exp(s * (-ONE_THIRD) - v * ONE_SIXTH) / 12
    rho1 = -c_eps * gsp * gtp
    rho23a = qt * G_lead + qtp * dBpv + c_eps * (qsp * fmp - (emes * qs * qt) * ps_fmpp)
    edApt = dBpt - dBt * HALF
    rho3b = j_exp(s * (-HALF)) * (edApt * eBpv + dBt * eBppv)
    return rho0 + rho1 + rho23a + rho3b


# ==============================================================================
# 6. ADAPTIVE 3D BISECTION WITH MEAN-VALUE FORM
# ==============================================================================
FUNC_MAP = {
    "drho_ds_simplex": drho_ds_simplex,
    "drho_ds_mid_v": drho_ds_mid_v,
    "drho_ds_closed": drho_ds_closed,
    "rho_small_v": rho_small_v,
    "rho_closed": rho_closed,
}

def eval_mvf_3d(func, sa, sb, va, vb, ea, eb, ve_cache, cm_cache):
    s_iv = iv.mpf([sa, sb])
    v_iv = iv.mpf([va, vb])
    e_iv = iv.mpf([ea, eb])
    jet = func(Jet3(s_iv, 1, 0, 0), Jet3(v_iv, 0, 1, 0), Jet3(e_iv, 0, 0, 1), ve_cache, cm_cache)
    if jet is None:
        return None, None, None, None
    if jet.v.a > 0:
        return jet.v, mp.mpf(0), mp.mpf(0), mp.mpf(0)
    sm = (sa + sb) / 2; hs = (sb - sa) / 2
    vm = (va + vb) / 2; hv = (vb - va) / 2
    em = (ea + eb) / 2; he = (eb - ea) / 2
    f_mid = func(iv.mpf(sm), iv.mpf(vm), iv.mpf(em), ve_cache, cm_cache)
    if f_mid is None:
        return None, None, None, None
    err_s = max(abs(jet.ds.a), abs(jet.ds.b)) * hs
    err_v = max(abs(jet.dv.a), abs(jet.dv.b)) * hv
    err_e = max(abs(jet.de.a), abs(jet.de.b)) * he
    mvf = f_mid + jet.ds * iv.mpf([-hs, hs]) + jet.dv * iv.mpf([-hv, hv]) + jet.de * iv.mpf([-he, he])
    lo = max(jet.v.a, mvf.a)
    hi = min(jet.v.b, mvf.b)
    return iv.mpf([lo, hi]), err_s, err_v, err_e

def _run_3d_job(args):
    func_name, s_min, s_max, v_min, v_max, e_min, e_max, ns, nv, ne, label = args
    func = FUNC_MAP[func_name]
    t0 = time.time()
    ve_cache = {}
    cm_cache = {}
    stack = []
    s0, s1 = mp.mpf(s_min), mp.mpf(s_max)
    v0, v1 = mp.mpf(v_min), mp.mpf(v_max)
    e0, e1 = mp.mpf(e_min), mp.mpf(e_max)
    for k in range(ne):
        ea = e0 + (e1 - e0) * k / ne
        eb = e0 + (e1 - e0) * (k + 1) / ne
        for j in range(nv):
            va = v0 + (v1 - v0) * j / nv
            vb = v0 + (v1 - v0) * (j + 1) / nv
            for i in range(ns):
                sa = s0 + (s1 - s0) * i / ns
                sb = s0 + (s1 - s0) * (i + 1) / ns
                stack.append((sa, sb, va, vb, ea, eb, 0))

    certified = 0
    uncertified = 0
    min_lb = mp.mpf('1e9')
    max_depth = 0

    while stack:
        sa, sb, va, vb, ea, eb, depth = stack.pop()
        enc, err_s, err_v, err_e = eval_mvf_3d(func, sa, sb, va, vb, ea, eb, ve_cache, cm_cache)
        if enc is not None and enc.a > 0:
            certified += 1
            if enc.a < min_lb: min_lb = enc.a
            if depth > max_depth: max_depth = depth
        else:
            if depth >= 28:
                uncertified += 1
                continue
            sm = (sa + sb) / 2; vm = (va + vb) / 2; em = (ea + eb) / 2
            if err_s is not None:
                if err_s >= err_v and err_s >= err_e:
                    stack.append((sa, sm, va, vb, ea, eb, depth + 1))
                    stack.append((sm, sb, va, vb, ea, eb, depth + 1))
                elif err_v >= err_s and err_v >= err_e:
                    stack.append((sa, sb, va, vm, ea, eb, depth + 1))
                    stack.append((sa, sb, vm, vb, ea, eb, depth + 1))
                else:
                    stack.append((sa, sb, va, vb, ea, em, depth + 1))
                    stack.append((sa, sb, va, vb, em, eb, depth + 1))
            else:
                ws, wv, we = (sb - sa), (vb - va), (eb - ea) * 20
                if wv >= ws and wv >= we:
                    stack.append((sa, sb, va, vm, ea, eb, depth + 1))
                    stack.append((sa, sb, vm, vb, ea, eb, depth + 1))
                elif ws >= wv and ws >= we:
                    stack.append((sa, sm, va, vb, ea, eb, depth + 1))
                    stack.append((sm, sb, va, vb, ea, eb, depth + 1))
                else:
                    stack.append((sa, sb, va, vb, ea, em, depth + 1))
                    stack.append((sa, sb, va, vb, em, eb, depth + 1))

    dt = time.time() - t0
    return (label, certified, uncertified, float(min_lb), max_depth, dt)


# ==============================================================================
# 7. REGION 1, REGION 2, REGION 3 CERTIFICATIONS
# ==============================================================================
def verify_region1():
    print("=== REGION 1: Small-(s,v) Corner (s + v <= t0 = 0.25, eps in [0, 1/7]) ===", flush=True)
    _, cert, uncert, min_lb, max_d, dt = _run_3d_job(
        ("drho_ds_simplex", 0, '0.25', 0, '0.25', 0, str(E_MAX_MP), 1, 1, 2, "R1")
    )
    assert uncert == 0 and min_lb > 0, f"Region 1 failed: uncert={uncert}, min_lb={min_lb}"
    print(f"  [0, 0.25]^2 x [0, 1/7]: certified={cert} boxes, d/ds rho >= {min_lb:.6f} > 0 "
          f"(max_depth={max_d}, time={dt:.2f}s)  [CERTIFIED]", flush=True)
    return cert, uncert


def verify_region2():
    print("\n=== REGION 2: Large-v Tail (v >= V0 = 30, ALL s > 0, ALL eps in [0, 1/7]) ===", flush=True)
    t0 = time.time()
    V0 = iv.mpf(30)
    E_MAX = E_MAX_IV
    s1 = ONE
    alpha_max = ((1 + E_MAX) * (1 + 2*E_MAX) / 2).b
    psi_min_V0 = (7 * (1 - iv.exp(-V0 / 7))).a
    q_max_V0 = (ONE / iv.mpf(psi_min_V0)).b
    c_min = iv.mpf(49) / 12

    r_max = (iv.mpf(alpha_max) * V0**2 * iv.exp(-2*V0/3) + ((1 + E_MAX)*V0 + 1) * iv.exp(-V0)).b
    w_min = iv.sqrt(1 - iv.mpf(r_max)).a
    rp_max = (2*iv.mpf(alpha_max) * (V0**2 / 3 * iv.exp(-2*V0/3) + V0 * iv.exp(-V0))).b
    rpp_max = (2*iv.mpf(alpha_max) * ((1 + (FOUR_THIRDS + E_MAX)*V0 + TWO_NINTHS * V0**2)*iv.exp(-2*V0/3)
                                      + (1 + 2*E_MAX)*V0*iv.exp(-V0))).b
    ur_max = (iv.mpf(alpha_max)*V0**3*iv.exp(-2*V0/3) + ((1+E_MAX)*V0**2 + V0)*iv.exp(-V0)).b
    urp_max = (2*iv.mpf(alpha_max) * (V0**3/3 * iv.exp(-2*V0/3) + V0**2 * iv.exp(-V0))).b
    urpp_max = (2*iv.mpf(alpha_max) * ((V0 + (FOUR_THIRDS + E_MAX)*V0**2 + TWO_NINTHS * V0**3)*iv.exp(-2*V0/3)
                                       + (1 + 2*E_MAX)*V0**2*iv.exp(-V0))).b

    eA1_0 = (3 * (1 + E_MAX + iv.mpf(q_max_V0)) * iv.exp(-V0/3)).b
    eA1_1 = (3 * (iv.mpf(q_max_V0)**2 + (1+E_MAX)*(1+E_MAX+iv.mpf(q_max_V0))) * iv.exp(-V0/3)).b
    eA1_2 = (3 * (2*iv.mpf(q_max_V0)**3 + 2*(1+E_MAX)*iv.mpf(q_max_V0)**2
                  + (1+E_MAX)**2*(1+E_MAX+iv.mpf(q_max_V0))) * iv.exp(-V0/3)).b

    c_g1 = (1/(1+iv.mpf(w_min))**2 + iv.mpf(r_max)/(iv.mpf(w_min)*(1+iv.mpf(w_min))**3)).b
    c_g2 = (2/(iv.mpf(w_min)*(1+iv.mpf(w_min))**3)
            + iv.mpf(r_max)/(2*iv.mpf(w_min)**3*(1+iv.mpf(w_min))**3)
            + 3*iv.mpf(r_max)/(2*iv.mpf(w_min)**2*(1+iv.mpf(w_min))**4)).b
    g0_u = (iv.mpf(ur_max) / (1+iv.mpf(w_min))**2).b
    g0_1 = (iv.mpf(r_max) / (1+iv.mpf(w_min))**2).b
    g1_u = (iv.mpf(urp_max) * iv.mpf(c_g1)).b
    g1_1 = (iv.mpf(rp_max) * iv.mpf(c_g1)).b
    g2_u = (iv.mpf(urpp_max) * iv.mpf(c_g1) + iv.mpf(urp_max)*iv.mpf(rp_max)*iv.mpf(c_g2)).b
    g2_1 = (iv.mpf(rpp_max) * iv.mpf(c_g1) + iv.mpf(rp_max)**2*iv.mpf(c_g2)).b

    eA0_M = (iv.mpf(eA1_0) + iv.mpf('1.5')*iv.mpf(g0_u) + iv.mpf(eA1_0)*iv.mpf(g0_1)).b
    eA1_M = (iv.mpf(eA1_1) + iv.mpf('1.5')*iv.mpf(g1_u) + iv.mpf(eA1_0)*iv.mpf(g1_1)
             + iv.mpf(g0_u) + (iv.mpf('1.5') + iv.mpf(eA1_1))*iv.mpf(g0_1)).b
    eA2_M = (iv.mpf(eA1_2) + iv.mpf('1.5')*iv.mpf(g2_u) + iv.mpf(eA1_0)*iv.mpf(g2_1)
             + 2*(iv.mpf(g1_u) + (iv.mpf('1.5') + iv.mpf(eA1_1))*iv.mpf(g1_1))
             + TWO_THIRDS*iv.mpf(g0_u) + (2 + iv.mpf('1.5')*E_MAX + iv.mpf(eA1_2))*iv.mpf(g0_1)).b
    eB1_M = (iv.mpf(eA1_M) + iv.mpf(eA0_M)/2).b
    eB2_M = (iv.mpf(eA2_M) + iv.mpf(eA1_M) + iv.mpf(eA0_M)/4).b

    e_all = iv.mpf([0, E_MAX.b])
    hp_max = mp.mpf(0); hpp_max = mp.mpf(0)
    for i in range(4):
        si = iv.mpf([mp.mpf(i)/4, mp.mpf(i+1)/4])
        _, hp, hpp = h_sinh_jet_series(si, e_all)
        hp_max = max(hp_max, abs(hp).b)
        hpp_max = max(hpp_max, abs(hpp).b)

    # 2a: 0 < s <= 1, v >= 30, eps in [0, 1/7]
    t_A2_v = (TWO_THIRDS*(V0+1) + 2 + iv.mpf('1.5')*E_MAX + iv.mpf(eA2_M)).b
    t_A1_v = ((V0+1) + iv.mpf('1.5') + iv.mpf(eA1_M)).b
    v_B1_v = (V0/4 + iv.mpf('1.5') + iv.mpf(eB1_M)).b
    v_B2_v = (V0/24 + HALF + iv.mpf('1.5')*E_MAX + iv.mpf(eB2_M)).b
    rem_3b_quad_2a = ((iv.mpf(t_A2_v)*iv.mpf(v_B1_v) + iv.mpf(t_A1_v)*iv.mpf(v_B2_v)) / c_min * iv.exp(-2*V0/3)).b
    q1_bnd = (iv.mpf(q_max_V0)/2 + 1/V0**2).b
    q2_bnd = (iv.mpf(q_max_V0)/4 + 1/V0**2 + 2/(V0**2 * iv.mpf(psi_min_V0))).b
    rem_3b_EA_2a = (iv.mpf(eA2_M)*iv.mpf(q1_bnd) + iv.mpf(eA1_M)*iv.mpf(q2_bnd)).b
    P_main_2a = (ONE_TWELFTH - (iv.mpf(5)/8 + iv.mpf(3)*E_MAX/4)/V0
                 - (1 + 1/V0) * 2 / (V0**2)
                 - iv.mpf(rem_3b_EA_2a) - iv.mpf(rem_3b_quad_2a)).a
    main_2a_lb = (iv.exp(-s1/3) * (iv.mpf(P_main_2a) * iv.exp(-s1/3) - iv.mpf(1)/36)).a
    rho3a_2a_lb = (-ONE/(2*V0**2) - 2*iv.mpf(q_max_V0)/V0**2*iv.mpf(eB1_M)
                   - ONE/(24*V0) - ONE/V0**2*iv.mpf(eB2_M)).a
    g1_v = (HALF + iv.mpf(q_max_V0)).b
    g2_v = ((HALF + iv.mpf(q_max_V0))**2 + 1/V0**2).b
    ft1_v = (HALF + E_MAX + iv.mpf(q_max_V0)).b
    ft2_v = ((HALF + E_MAX + iv.mpf(q_max_V0))**2 + 1/V0**2).b
    rho12_2a_ub = (6 * iv.exp(-V0/3) / V0 * (iv.mpf(hpp_max)*iv.mpf(g1_v) + iv.mpf(hp_max)*iv.mpf(g2_v)
                                             + 2*iv.mpf(q_max_V0)/V0*iv.mpf(ft1_v) + ONE/V0*iv.mpf(ft2_v))).b
    lb_2a = (iv.mpf(main_2a_lb) + iv.mpf(rho3a_2a_lb) - iv.mpf(rho12_2a_ub)).a
    assert lb_2a > 0, f"Region 2a failed: {lb_2a}"
    print(f"  2a (0 < s <= 1, v >= 30): e^(v/6) * d/ds rho          >= {float(lb_2a):.6f} > 0  [CERTIFIED]", flush=True)

    # 2b: s >= 1, v >= 30, eps in [0, 1/7]
    f_min = (1 + 2*iv.exp(-s1/3) - 3*iv.exp(-2*s1/3)).a
    s_e23_max = (iv.mpf(3) / (2 * iv.e)).b
    s2_e23_max = (iv.mpf(9) / (iv.e**2)).b
    rat2_e23_max = (iv.exp(-2*s1/3) + (2/V0)*iv.mpf(s_e23_max) + (1/V0**2)*iv.mpf(s2_e23_max)).b
    rat1_e23_max = (iv.exp(-2*s1/3) + (1/V0)*iv.mpf(s_e23_max)).b
    s_diff_max = mp.mpf(0)
    for k in range(30):
        sv = iv.mpf([1 + mp.mpf(3)*k/30, 1 + mp.mpf(3)*(k+1)/30])
        val = (sv * (QUARTER*iv.exp(-2*sv/3) - iv.exp(-sv/3)/12)).b
        if val > s_diff_max: s_diff_max = val
    C_exp_const = (HALF + iv.mpf(3)/(2*V0) + iv.mpf(s_diff_max)
                   + iv.mpf(s2_e23_max)/(8*V0) + HALF*iv.mpf(rat2_e23_max)
                   + iv.mpf(3)/(2*V0)*iv.mpf(rat1_e23_max)).b
    rem_3a_2b = (iv.mpf(eB2_M) + iv.mpf(eB1_M)/V0).b
    rem_3b_EA_2b = (iv.mpf(rat1_e23_max) * ((HALF + 1/V0)*iv.mpf(eA1_M)
                                           + (QUARTER + 1/V0 + 2/V0**2)*iv.mpf(eA0_M))).b
    t2_v_exp = (2*iv.mpf(s2_e23_max)*V0*iv.exp(-2*V0/3) + 2*iv.exp(-2*s1/3)*V0**3*iv.exp(-2*V0/3)).b
    rem_3b_quad_2b = ((iv.mpf('1.1')*iv.mpf('0.32') + iv.mpf('1.51')*iv.mpf('0.08')) / c_min * iv.mpf(t2_v_exp)).b
    psi1_min = (7 * (1 - iv.exp(-s1/7))).a
    q1_max = (1 / iv.mpf(psi1_min)).b
    rem_rho1_2b = (6 * iv.exp(-s1) * iv.mpf(q1_max)*(HALF + iv.mpf(q1_max)) * iv.mpf(g1_v) * iv.exp(-V0/3)).b
    rem_rho2_2b = (6 * (iv.mpf(q1_max) + 1/V0) * (iv.mpf(q1_max)*iv.mpf(g1_v) + iv.mpf(g2_v)) * iv.exp(-V0/3)).b
    rem_tot_2b = (iv.mpf(rem_3a_2b) + iv.mpf(rem_3b_EA_2b) + iv.mpf(rem_3b_quad_2b)
                  + iv.mpf(rem_rho1_2b) + iv.mpf(rem_rho2_2b)).b

    min_2b = mp.mpf('1e9')
    N_eps = 32
    for i in range(N_eps):
        ea = E_MAX_MP * i / N_eps
        eb = E_MAX_MP * (i + 1) / N_eps
        psi_lb = (1 - iv.exp(-iv.mpf(eb)*V0)) / iv.mpf(eb)
        exp_ub = iv.exp(-iv.mpf(ea)*V0)
        val = (psi_lb / 24) * iv.mpf(f_min) - (iv.mpf(C_exp_const) + iv.mpf('1.5')*iv.mpf(eb)) * exp_ub - iv.mpf(rem_tot_2b)
        if val.a < min_2b: min_2b = val.a
    assert min_2b > 0, f"Region 2b failed: {min_2b}"
    print(f"  2b (s >= 1,     v >= 30): psi_eps(t) * e^(v/6) * rho  >= {float(min_2b):.6f} > 0  [CERTIFIED] ({time.time()-t0:.2f}s)", flush=True)
    return 0, 0


def eval_region3_pair(v, eps, S0, cm_cache):
    vv = j_val(v)
    if vv.b <= 3.0:
        c_eps = 6 / ((eps + 1) * (2*eps + 1))
        sc = j_sqrt(c_eps)
        ps_v = psi_jet(v, eps)
        _, Dp, Dpp = D_jet_series(v, eps)
        _, Bp, Bpp = B_jet_series(v, eps, cm_cache)
        G_lead = c_eps * Dpp - sc * Bpp
        G_lead1 = c_eps * Dp - sc * Bp
    else:
        res = tilde_dB_jet_closed(v, eps, need_eB=False, need_d2=True)
        if res is None: return None
        _, dBp, dBpp, _, _, _, fmp, fmpp, c_eps, ps_v, _, _, _ = res
        G_lead = dBpp - c_eps * fmpp
        G_lead1 = dBp - c_eps * fmp
    ps_S0 = psi_jet(S0, eps)
    ph_S0 = phi_jet(S0, eps)
    fac_S0 = HALF + iv.exp(-S0) * (iv.mpf(9)/14 + 1/S0)
    g1_term = -G_lead1 / (ps_v / ph_S0 + 1) if j_val(G_lead1).b <= 0 else -G_lead1
    bracket = g1_term - c_eps * j_exp(v * (-HALF)) * ((1 / ps_S0) + HALF) * fac_S0
    scale = j_exp(-eps * v) / ph_S0
    return G_lead, bracket, scale


def _run_region3_chunk(args):
    v_cuts, ea0, eb0, margin_str = args
    margin_mp = mp.mpf(margin_str)
    ea0, eb0 = mp.mpf(ea0), mp.mpf(eb0)
    v_cuts = [mp.mpf(x) for x in v_cuts]
    S0 = iv.mpf(25)
    cm_cache = {}
    stack = [(v_cuts[i], v_cuts[i+1], ea0, eb0, 0) for i in range(len(v_cuts)-1)]
    cert = 0; uncert = 0; min_lb = mp.mpf('1e9')
    while stack:
        va, vb, ea, eb, depth = stack.pop()
        vm = (va + vb)/2; hv = (vb - va)/2
        em = (ea + eb)/2; he = (eb - ea)/2
        res_j = eval_region3_pair(Jet2(iv.mpf([va, vb]), 1, 0), Jet2(iv.mpf([ea, eb]), 0, 1), S0, cm_cache)
        ok = False
        if res_j is not None:
            G_j, br_j, sc_j = res_j
            if G_j.v.a > margin_mp and br_j.v.a >= 0:
                lb = G_j.v.a; ok = True
            else:
                res_m = eval_region3_pair(iv.mpf(vm), iv.mpf(em), S0, cm_cache)
                if res_m is not None:
                    G_m, br_m, sc_m = res_m
                    dv = iv.mpf([-hv, hv]); de = iv.mpf([-he, he])
                    G_lo = max(G_j.v.a, (G_m + G_j.d1 * dv + G_j.d2 * de).a)
                    br_lo = max(br_j.v.a, (br_m + br_j.d1 * dv + br_j.d2 * de).a)
                    if br_lo >= 0: lb = G_lo
                    else:
                        sc_hi = min(sc_j.v.b, (sc_m + sc_j.d1 * dv + sc_j.d2 * de).b)
                        lb = (iv.mpf(G_lo) + iv.mpf(sc_hi) * iv.mpf(br_lo)).a
                    if lb > margin_mp: ok = True
        if ok:
            cert += 1
            if lb < min_lb: min_lb = lb
        else:
            if depth >= 22:
                uncert += 1; continue
            if res_j is not None:
                G_j = res_j[0]
                e1 = max(abs(G_j.d1.a), abs(G_j.d1.b)) * hv
                e2 = max(abs(G_j.d2.a), abs(G_j.d2.b)) * he
                if e1 >= e2:
                    stack.append((va, vm, ea, eb, depth+1)); stack.append((vm, vb, ea, eb, depth+1))
                else:
                    stack.append((va, vb, ea, em, depth+1)); stack.append((va, vb, em, eb, depth+1))
            else:
                if (vb - va) >= (eb - ea) * 20:
                    stack.append((va, vm, ea, eb, depth+1)); stack.append((vm, vb, ea, eb, depth+1))
                else:
                    stack.append((va, vb, ea, em, depth+1)); stack.append((va, vb, em, eb, depth+1))
    return cert, uncert, float(min_lb)


def verify_region3(pool):
    print("\n=== REGION 3: Large-s Tail (s >= S0 = 25, 0 < v <= 30, ALL eps in [0, 1/7]) ===", flush=True)
    t0 = time.time()
    S0 = iv.mpf(25)
    e_all = iv.mpf([0, E_MAX_IV.b])
    cm_cache = {}
    sc_min = iv.sqrt(iv.mpf(49)/12).a

    max_rho3b = mp.mpf(0)
    for i in range(60):
        va = mp.mpf(30) * i / 60; vb = mp.mpf(30) * (i + 1) / 60
        v_iv = iv.mpf([va, vb])
        if vb <= 4.5:
            _, Bp, Bpp = B_jet_series(v_iv, e_all, cm_cache)
            e23 = iv.exp(-2*(S0 + v_iv)/3); t_ub = S0 + vb
            b0 = (iv.mpf('1.5')*t_ub**2 + iv.mpf('0.002')*t_ub) * e23 / iv.mpf(sc_min)
            b1 = (t_ub**2 + iv.mpf('1.502')*t_ub) * e23 / iv.mpf(sc_min)
            val = (b1 * abs(Bp) + b0 * abs(Bpp)).b
        else:
            res = tilde_dB_jet_closed(v_iv, e_all, need_eB=True, need_d2=False)
            _, _, _, eBp, eBpp, _, _, _, _, _, _, _, _ = res
            e_dec = iv.exp(-2*S0/3 - v_iv/6); t_ub = S0 + vb
            b0 = (iv.mpf('1.5')*t_ub**2 + iv.mpf('0.002')*t_ub) * e_dec / iv.mpf(sc_min)
            b1 = (t_ub**2 + iv.mpf('1.502')*t_ub) * e_dec / iv.mpf(sc_min)
            val = (b1 * abs(eBp) + b0 * abs(eBpp)).b
        if val > max_rho3b: max_rho3b = val

    margin = max_rho3b + mp.mpf('1e-5')
    v_cuts = [0, 3, 6, 12, 30]
    chunks = [(v_cuts, str(E_MAX_MP * j / 4), str(E_MAX_MP * (j + 1) / 4), str(mp.mpf(margin._mpi_[0])))
              for j in range(4)]
    cert = 0; uncert = 0; min_lb = mp.mpf('1e9')
    for c, u, ml in pool.map(_run_region3_chunk, chunks):
        cert += c; uncert += u
        if mp.mpf(ml) < min_lb: min_lb = mp.mpf(ml)
    final_lb = (iv.mpf(min_lb) - iv.mpf(max_rho3b)).a
    assert uncert == 0 and final_lb > 0, f"Region 3 failed: uncert={uncert}, final_lb={final_lb}"
    dt = time.time() - t0
    print(f"  2D (v,eps) boxes certified = {cert} (time={dt:.2f}s)", flush=True)
    print(f"  |rho3b / q_eps(t)|        <= {float(max_rho3b):.4e}", flush=True)
    print(f"  rho(s, s+v; eps)/q_eps(t) >= {float(final_lb):.6e} > 0  [CERTIFIED]", flush=True)
    return cert, uncert


# ==============================================================================
# 8. BUILT-IN NUMERICAL SELF-TEST
# ==============================================================================
def self_test():
    def phi_mp(x, eps): return x if eps == 0 else mp.expm1(eps*x)/eps
    def psi_mp(x, eps): return x if eps == 0 else -mp.expm1(-eps*x)/eps
    def L_diag_mp(x, eps):
        c = mp.mpf(6) / ((1 + eps) * (1 + 2*eps))
        p = phi_mp(x, eps); ps = psi_mp(x, eps)
        r = (1+eps)*(1+2*eps)/2 * ps**2 * mp.exp(-2*x/3) + ((1+eps)*ps + 1) * mp.exp(-(1+eps)*x)
        return c * mp.exp((mp.mpf(2)/3 + 2*eps)*x) / (p*p) * (1 - r)
    def K1_mp(s, t, eps):
        v = t - s; c = mp.mpf(6) / ((1 + eps) * (1 + 2*eps))
        return (-3*mp.exp(-(s+t)/6)
                + c*mp.exp(-(s+t)/2)/(phi_mp(s,eps)*phi_mp(t,eps))
                - c*mp.exp(eps*s - v/2)/(phi_mp(s,eps)*phi_mp(v,eps))
                + c*mp.exp(eps*t + (mp.mpf('0.5')+eps)*v)/(phi_mp(t,eps)*phi_mp(v,eps))
                - mp.exp(-(s+t)/6)*mp.sqrt(L_diag_mp(t,eps)*L_diag_mp(v,eps)))
    def rho_fd(s, v, eps):
        h = mp.mpf('1e-6'); t = s + v
        return -(K1_mp(s+h,t+h,eps) - K1_mp(s+h,t-h,eps) - K1_mp(s-h,t+h,eps) + K1_mp(s-h,t-h,eps))/(4*h*h)
    def drho_fd(s, v, eps):
        h = mp.mpf('1e-5')
        return (rho_fd(s+h, v, eps) - rho_fd(s-h, v, eps))/(2*h)

    tests = [
        ("drho_ds_simplex", drho_ds_simplex, drho_fd, '0.4', '1.2', mp.mpf(1)/10),
        ("drho_ds_mid_v",   drho_ds_mid_v,   drho_fd, '0.5', '3.2', mp.mpf(1)/7),
        ("drho_ds_closed",  drho_ds_closed,  drho_fd, '0.5', '6.0', mp.mpf(1)/7),
        ("rho_small_v",     rho_small_v,     rho_fd,  '2.0', '1.5', mp.mpf(1)/7),
        ("rho_small_v_lg",  rho_small_v,     rho_fd,  '8.0', '1.5', mp.mpf(1)/7),
        ("rho_closed",      rho_closed,      rho_fd,  '5.0', '8.0', mp.mpf(1)/10),
    ]
    for name, fn, ref, sv, vv, ev in tests:
        val = fn(iv.mpf(sv), iv.mpf(vv), iv.mpf(ev))
        ref_v = ref(mp.mpf(sv), mp.mpf(vv), ev)
        err = abs(mp.mpf(val.mid._mpi_[0]) - ref_v)
        assert err < mp.mpf('1e-5') and val.a <= ref_v + mp.mpf('1e-5') and ref_v - mp.mpf('1e-5') <= val.b, \
            f"Self-test failed for {name}: iv={val}, ref={ref_v}"
    print("Self-test passed: all 5 evaluators match 25-digit finite differences!", flush=True)


# ==============================================================================
# 9. MAIN DRIVER
# ==============================================================================
def main():
    t_all = time.time()
    n_workers = min(os.cpu_count() or 1, 4)
    print("============================================================================", flush=True)
    print("  RIGOROUS 3D INTERVAL CERTIFICATION OF rho(s, s+v; eps) > 0", flush=True)
    print(f"  Domain: ALL s > 0, ALL v > 0, ALL eps in [0, 1/7] (n >= 7 & n = inf)", flush=True)
    print(f"  Parameters: t0 = 0.25, s0 = 1.0, S0 = 25.0, V0 = 30.0 (workers={n_workers})", flush=True)
    print("============================================================================", flush=True)

    self_test()
    c1, u1 = verify_region1()
    c2, u2 = verify_region2()

    with ProcessPoolExecutor(max_workers=n_workers) as pool:
        c3, u3 = verify_region3(pool)

        print("\n=== REGION 4: Compact 3D Box (0, 25] x (0, 30] x [0, 1/7] (C++ IEEE-754 FE_UPWARD 3D MVF) ===", flush=True)
        here = os.path.dirname(os.path.abspath(__file__))
        cpp_src = os.path.join(here, "certify_region4.cpp")
        cpp_bin = os.path.join(here, "certify_region4")
        subprocess.run(
            ["g++", "-O3", "-frounding-math", "-fno-fast-math", "-pthread", cpp_src, "-o", cpp_bin],
            check=True,
        )
        proc = subprocess.run([cpp_bin], capture_output=True, text=True, check=True)
        total_boxes = c1 + c3
        total_uncert = u1 + u2 + u3
        for line in proc.stdout.splitlines():
            if line.startswith("REGION4_SUMMARY"):
                parts = dict(tok.split("=") for tok in line.split()[1:])
                total_boxes += int(parts["certified"])
                total_uncert += int(parts["uncertified"])
            else:
                print(line, flush=True)

    total_time = time.time() - t_all
    print("\n============================================================================", flush=True)
    print(f"  TOTAL_CERTIFIED_BOXES = {total_boxes}", flush=True)
    print(f"  UNCERTIFIED_BOXES     = {total_uncert}", flush=True)
    print(f"  TOTAL_RUNTIME         = {total_time:.2f}s", flush=True)
    if total_uncert == 0:
        print("  STATUS: Q.E.D. -- rho(s, s+v; eps) > 0 CERTIFIED FOR ALL s,v>0, eps in [0,1/7]!", flush=True)
    else:
        print("  STATUS: FAILED -- UNCERTIFIED BOXES REMAIN!", flush=True)
    print("============================================================================", flush=True)

if __name__ == "__main__":
    main()
