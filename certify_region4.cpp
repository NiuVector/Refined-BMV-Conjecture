// certify_region4.cpp
// 100% Rigorous IEEE-754 Outward-Rounded 3D Interval Arithmetic Certifier
// Compiled with: g++ -O3 -frounding-math -fno-fast-math -pthread certify_region4.cpp -o certify_region4
//
// Certifies Region 4: ALL (s, v, eps) in (0, 25] x (0, 30] x [0, 1/7]
// using FE_UPWARD directed rounding + 1e-14 relative outward padding on exp/sqrt
// and 3D Mean-Value Form (forward-mode AD Jet3).

#include <algorithm>
#include <cfenv>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <thread>
#include <vector>
#include "cp_table.h"

#pragma STDC FENV_ACCESS ON

static const double E_MAX_HI = 0.14285714285714288; // > 1/7 (nextafter(1.0/7.0, +inf))

// ============================================================================
// 1. RIGOROUS IEEE-754 OUTWARD-ROUNDED INTERVAL (FE_UPWARD ACTIVE)
// ============================================================================
struct Iv {
    double lo, hi;
    Iv() : lo(0.0), hi(0.0) {}
    Iv(double x) : lo(x), hi(x) {}
    Iv(double a, double b) : lo(a), hi(b) {}
};

static inline Iv iv_from_rat(double num, double den) {
    // Assumes den > 0, exact double num, den
    return Iv(-((-num) / den), num / den);
}

static inline Iv operator+(const Iv& a, const Iv& b) {
    return Iv(-((-a.lo) + (-b.lo)), a.hi + b.hi);
}
static inline Iv operator-(const Iv& a, const Iv& b) {
    return Iv(-((-a.lo) + b.hi), a.hi + (-b.lo));
}
static inline Iv operator-(const Iv& a) {
    return Iv(-a.hi, -a.lo);
}
static inline Iv operator*(const Iv& a, const Iv& b) {
    double p1 = a.lo * b.lo, p2 = a.lo * b.hi, p3 = a.hi * b.lo, p4 = a.hi * b.hi;
    double hi = std::max(std::max(p1, p2), std::max(p3, p4));
    double n1 = (-a.lo) * b.lo, n2 = (-a.lo) * b.hi, n3 = (-a.hi) * b.lo, n4 = (-a.hi) * b.hi;
    double lo = -std::max(std::max(n1, n2), std::max(n3, n4));
    return Iv(lo, hi);
}
static inline Iv iv_inv(const Iv& b) {
    // Valid when b.lo > 0 or b.hi < 0
    return Iv(-((-1.0) / b.hi), 1.0 / b.lo);
}
static inline Iv operator/(const Iv& a, const Iv& b) {
    return a * iv_inv(b);
}
static inline Iv iv_sqr(const Iv& a) {
    if (a.lo >= 0.0) return Iv(-((-a.lo) * a.lo), a.hi * a.hi);
    if (a.hi <= 0.0) return Iv(-((-a.hi) * a.hi), a.lo * a.lo);
    double m = std::max(-a.lo, a.hi);
    return Iv(0.0, m * m);
}
static inline Iv iv_exp(const Iv& a) {
    // 1e-14 relative outward padding (~45 ULPs) covers any libm rounding error
    double elo = std::exp(a.lo);
    double ehi = std::exp(a.hi);
    double lo = std::max(0.0, -((-elo) * (1.0 - 1e-14)));
    double hi = ehi * (1.0 + 1e-14);
    return Iv(lo, hi);
}
static inline Iv iv_sqrt(const Iv& a) {
    double slo = (a.lo <= 0.0) ? 0.0 : std::max(0.0, std::nextafter(std::nextafter(std::sqrt(a.lo), -INFINITY), -INFINITY));
    double shi = std::nextafter(std::nextafter(std::sqrt(a.hi), INFINITY), INFINITY);
    return Iv(slo, shi);
}
static inline double iv_abs_max(const Iv& a) {
    return std::max(std::abs(a.lo), std::abs(a.hi));
}

// ============================================================================
// 2. 3D FORWARD-MODE AD OVER Iv (Jet3)
// ============================================================================
struct Jet3 {
    Iv v, ds, dv, de;
    Jet3() {}
    Jet3(const Iv& v_) : v(v_), ds(0.0), dv(0.0), de(0.0) {}
    Jet3(const Iv& v_, const Iv& ds_, const Iv& dv_, const Iv& de_) : v(v_), ds(ds_), dv(dv_), de(de_) {}
};

static inline Jet3 operator+(const Jet3& a, const Jet3& b) {
    return Jet3(a.v + b.v, a.ds + b.ds, a.dv + b.dv, a.de + b.de);
}
static inline Jet3 operator+(const Jet3& a, const Iv& b) {
    return Jet3(a.v + b, a.ds, a.dv, a.de);
}
static inline Jet3 operator+(const Iv& a, const Jet3& b) {
    return Jet3(a + b.v, b.ds, b.dv, b.de);
}
static inline Jet3 operator-(const Jet3& a, const Jet3& b) {
    return Jet3(a.v - b.v, a.ds - b.ds, a.dv - b.dv, a.de - b.de);
}
static inline Jet3 operator-(const Jet3& a, const Iv& b) {
    return Jet3(a.v - b, a.ds, a.dv, a.de);
}
static inline Jet3 operator-(const Iv& a, const Jet3& b) {
    return Jet3(a - b.v, -b.ds, -b.dv, -b.de);
}
static inline Jet3 operator-(const Jet3& a) {
    return Jet3(-a.v, -a.ds, -a.dv, -a.de);
}
static inline Jet3 operator*(const Jet3& a, const Jet3& b) {
    return Jet3(a.v * b.v,
                a.ds * b.v + a.v * b.ds,
                a.dv * b.v + a.v * b.dv,
                a.de * b.v + a.v * b.de);
}
static inline Jet3 operator*(const Jet3& a, const Iv& b) {
    return Jet3(a.v * b, a.ds * b, a.dv * b, a.de * b);
}
static inline Jet3 operator*(const Iv& a, const Jet3& b) {
    return Jet3(a * b.v, a * b.ds, a * b.dv, a * b.de);
}
static inline Jet3 j_inv(const Jet3& b) {
    Iv ib = iv_inv(b.v);
    Iv mib2 = -(ib * ib);
    return Jet3(ib, mib2 * b.ds, mib2 * b.dv, mib2 * b.de);
}
static inline Jet3 operator/(const Jet3& a, const Jet3& b) {
    return a * j_inv(b);
}
static inline Jet3 operator/(const Jet3& a, const Iv& b) {
    return a * iv_inv(b);
}
static inline Jet3 operator/(const Iv& a, const Jet3& b) {
    return a * j_inv(b);
}
static inline Jet3 j_sqr(const Jet3& a) {
    Iv two_v = Iv(2.0) * a.v;
    return Jet3(iv_sqr(a.v), two_v * a.ds, two_v * a.dv, two_v * a.de);
}
static inline Jet3 j_exp(const Jet3& a) {
    Iv e = iv_exp(a.v);
    return Jet3(e, e * a.ds, e * a.dv, e * a.de);
}
static inline Jet3 j_sqrt(const Jet3& a) {
    Iv s = iv_sqrt(a.v);
    Iv inv2s = iv_inv(Iv(2.0) * s);
    return Jet3(s, a.ds * inv2s, a.dv * inv2s, a.de * inv2s);
}
static inline Jet3 j_add_rem(const Jet3& x, const Iv& rem, const Iv& rx, const Jet3& x_obj, const Iv& re, const Jet3& e_obj) {
    return Jet3(x.v + rem,
                x.ds + rx * x_obj.ds + re * e_obj.ds,
                x.dv + rx * x_obj.dv + re * e_obj.dv,
                x.de + rx * x_obj.de + re * e_obj.de);
}

// ============================================================================
// 3. CONSTANTS & PRECOMPUTED FACTORIALS
// ============================================================================
static Iv INV_FACT[40];
static Iv NEG_HALF_POW[30];
static Iv ONE_THIRD, TWO_THIRDS, FOUR_THIRDS, TWO_NINTHS, ONE_NINTH, ONE_SIXTH, ONE_TWELFTH, ONE_36TH;

static void init_constants() {
    double f = 1.0;
    INV_FACT[0] = Iv(1.0);
    for (int k = 1; k < 40; ++k) {
        // Compute exact k! in Iv for k <= 20, outward-rounded for k > 20
        if (k <= 20) {
            f *= (double)k;
            INV_FACT[k] = iv_from_rat(1.0, f);
        } else {
            INV_FACT[k] = INV_FACT[k - 1] * iv_from_rat(1.0, (double)k);
        }
    }
    NEG_HALF_POW[0] = Iv(1.0);
    for (int k = 1; k < 30; ++k) NEG_HALF_POW[k] = NEG_HALF_POW[k - 1] * Iv(-0.5);
    ONE_THIRD = iv_from_rat(1.0, 3.0);
    TWO_THIRDS = iv_from_rat(2.0, 3.0);
    FOUR_THIRDS = iv_from_rat(4.0, 3.0);
    TWO_NINTHS = iv_from_rat(2.0, 9.0);
    ONE_NINTH = iv_from_rat(1.0, 9.0);
    ONE_SIXTH = iv_from_rat(1.0, 6.0);
    ONE_TWELFTH = iv_from_rat(1.0, 12.0);
    ONE_36TH = iv_from_rat(1.0, 36.0);
}

// ============================================================================
// 4. ZERO-WRAPPING psi_jet, phi_jet, sinhc, phi_tilde, P_tilde, A, B, D, h_sinh
// ============================================================================
static Iv psi_point(double u_pt, double e_pt) {
    Iv u(u_pt), e(e_pt);
    if (e_pt == 0.0) return u;
    Iv z = e * u;
    if (z.lo >= 0.05) return (Iv(1.0) - iv_exp(-z)) / e;
    const int N = 12;
    Iv s(0.0), zp(1.0);
    for (int m = 0; m < N; ++m) {
        Iv term = zp * INV_FACT[m + 1];
        s = (m % 2 == 0) ? (s + term) : (s - term);
        zp = zp * z;
    }
    double rem = (zp * INV_FACT[N + 1]).hi;
    return u * (s + Iv(-rem, rem));
}

static Iv phi_point(double u_pt, double e_pt) {
    Iv u(u_pt), e(e_pt);
    if (e_pt == 0.0) return u;
    Iv z = e * u;
    if (z.lo >= 0.05) return (iv_exp(z) - Iv(1.0)) / e;
    const int N = 12;
    Iv s(0.0), zp(1.0);
    for (int m = 0; m < N; ++m) {
        s = s + zp * INV_FACT[m + 1];
        zp = zp * z;
    }
    Iv q = Iv(z.hi) / Iv((double)(N + 2));
    double rem = (zp * INV_FACT[N + 1] / (Iv(1.0) - q)).hi;
    return u * (s + Iv(0.0, rem));
}

static Iv f_dpsi_point(double z_pt) {
    if (z_pt == 0.0) return Iv(0.5);
    Iv z(z_pt);
    if (z.lo >= 0.05) return (Iv(1.0) - (Iv(1.0) + z) * iv_exp(-z)) / iv_sqr(z);
    const int N = 10;
    Iv s(0.0), zp(1.0);
    for (int m = 0; m < N; ++m) {
        Iv term = Iv((double)(m + 1)) * zp * INV_FACT[m + 2];
        s = (m % 2 == 0) ? (s + term) : (s - term);
        zp = zp * z;
    }
    double rem = (Iv((double)(N + 1)) * zp * INV_FACT[N + 2]).hi;
    return s + Iv(-rem, rem);
}

static Iv g_dphi_point(double z_pt) {
    if (z_pt == 0.0) return Iv(0.5);
    Iv z(z_pt);
    if (z.lo >= 0.05) return ((z - Iv(1.0)) * iv_exp(z) + Iv(1.0)) / iv_sqr(z);
    const int N = 10;
    Iv s(0.0), zp(1.0);
    for (int m = 0; m < N; ++m) {
        s = s + Iv((double)(m + 1)) * zp * INV_FACT[m + 2];
        zp = zp * z;
    }
    Iv q = Iv(z.hi) / Iv((double)(N + 3));
    double rem = (Iv((double)(N + 1)) * zp * INV_FACT[N + 2] / (Iv(1.0) - q)).hi;
    return s + Iv(0.0, rem);
}

static Jet3 psi_jet(const Jet3& u, const Jet3& eps) {
    Iv val(psi_point(u.v.lo, eps.v.hi).lo, psi_point(u.v.hi, eps.v.lo).hi);
    Iv dpsi_du = iv_exp(-(eps.v * u.v));
    Iv z_lo = Iv(eps.v.lo) * Iv(u.v.lo);
    Iv z_hi = Iv(eps.v.hi) * Iv(u.v.hi);
    double f_hi = f_dpsi_point(z_lo.lo).hi;
    double f_lo = f_dpsi_point(z_hi.hi).lo;
    Iv dpsi_de((-(iv_sqr(Iv(u.v.hi)) * Iv(f_hi))).lo, (-(iv_sqr(Iv(u.v.lo)) * Iv(f_lo))).hi);
    return Jet3(val,
                dpsi_du * u.ds + dpsi_de * eps.ds,
                dpsi_du * u.dv + dpsi_de * eps.dv,
                dpsi_du * u.de + dpsi_de * eps.de);
}

static Jet3 phi_jet(const Jet3& u, const Jet3& eps) {
    Iv val(phi_point(u.v.lo, eps.v.lo).lo, phi_point(u.v.hi, eps.v.hi).hi);
    Iv dphi_du = iv_exp(eps.v * u.v);
    Iv z_lo = Iv(eps.v.lo) * Iv(u.v.lo);
    Iv z_hi = Iv(eps.v.hi) * Iv(u.v.hi);
    double g_lo = g_dphi_point(z_lo.lo).lo;
    double g_hi = g_dphi_point(z_hi.hi).hi;
    Iv dphi_de((iv_sqr(Iv(u.v.lo)) * Iv(g_lo)).lo, (iv_sqr(Iv(u.v.hi)) * Iv(g_hi)).hi);
    return Jet3(val,
                dphi_du * u.ds + dphi_de * eps.ds,
                dphi_du * u.dv + dphi_de * eps.dv,
                dphi_du * u.de + dphi_de * eps.de);
}

static Iv iv_pow_int(const Iv& x, int n) {
    Iv r(1.0), b = x;
    while (n > 0) {
        if (n & 1) r = r * b;
        b = b * b;
        n >>= 1;
    }
    return r;
}

static void sinhc_half_jet_x(const Jet3& x, const Jet3& eps, Jet3& v0, Jet3& v1, Jet3& v2) {
    Jet3 z = (eps * x) * Iv(0.5);
    Jet3 z2 = j_sqr(z);
    Jet3 s0 = (((z2 * INV_FACT[9] + INV_FACT[7]) * z2 + INV_FACT[5]) * z2 + INV_FACT[3]) * z2 + Iv(1.0);
    Jet3 s1 = (((z2 * (Iv(8.0) * INV_FACT[9]) + Iv(6.0) * INV_FACT[7]) * z2 + Iv(4.0) * INV_FACT[5]) * z2 + Iv(2.0) * INV_FACT[3]) * z;
    Jet3 s2 = (((z2 * (Iv(56.0) * INV_FACT[9]) + Iv(30.0) * INV_FACT[7]) * z2 + Iv(12.0) * INV_FACT[5]) * z2 + Iv(2.0) * INV_FACT[3]);
    Iv zm(z.v.hi);
    Iv q0 = iv_sqr(zm) / Iv(132.0);
    Iv base = INV_FACT[11] / (Iv(1.0) - q0);
    double r0 = (base * iv_pow_int(zm, 10)).hi;
    double r1 = (base * Iv(10.0) * iv_pow_int(zm, 9)).hi;
    double r2 = (base * Iv(90.0) * iv_pow_int(zm, 8)).hi;
    double r3 = (base * Iv(720.0) * iv_pow_int(zm, 7)).hi;
    Jet3 eh = eps * Iv(0.5);
    v0 = j_add_rem(s0, Iv(0.0, r0), Iv(0.0, r1), z, Iv(0.0), eps);
    v1 = j_add_rem(s1, Iv(0.0, r1), Iv(0.0, r2), z, Iv(0.0), eps) * eh;
    v2 = j_add_rem(s2, Iv(0.0, r2), Iv(0.0, r3), z, Iv(0.0), eps) * j_sqr(eh);
}

static void phi_tilde_jet_x(const Jet3& x, const Jet3& eps, Jet3& v0, Jet3& v1, Jet3& v2) {
    const int N = 10;
    Jet3 z = eps * x;
    v0 = Jet3(INV_FACT[N]);
    v1 = Jet3(INV_FACT[N] * Iv((double)(N - 1)));
    v2 = Jet3(INV_FACT[N] * Iv((double)((N - 1) * (N - 2))));
    for (int m = N - 2; m >= 0; --m) {
        Iv c = INV_FACT[m + 1];
        v0 = v0 * z + c;
        if (m >= 1) v1 = v1 * z + c * Iv((double)m);
        if (m >= 2) v2 = v2 * z + c * Iv((double)(m * (m - 1)));
    }
    Iv zm(z.v.hi);
    Iv q0 = zm / Iv((double)(N + 2));
    Iv base = INV_FACT[N + 1] / (Iv(1.0) - q0);
    double r0 = (base * iv_pow_int(zm, N)).hi;
    double r1 = (base * Iv((double)N) * iv_pow_int(zm, N - 1)).hi;
    double r2 = (base * Iv((double)(N * (N - 1))) * iv_pow_int(zm, N - 2)).hi;
    double r3 = (base * Iv((double)(N * (N - 1) * (N - 2))) * iv_pow_int(zm, N - 3)).hi;
    v0 = j_add_rem(v0, Iv(0.0, r0), Iv(0.0, r1), z, Iv(0.0), eps);
    v1 = j_add_rem(v1, Iv(0.0, r1), Iv(0.0, r2), z, Iv(0.0), eps) * eps;
    v2 = j_add_rem(v2, Iv(0.0, r2), Iv(0.0, r3), z, Iv(0.0), eps) * j_sqr(eps);
}

static void P_tilde_jet_x(const Jet3& x, const Jet3& eps, Jet3& v0, Jet3& v1, Jet3& v2) {
    int N = (x.v.hi <= 3.05) ? 14 : N_P_MAX;
    Jet3 cs[N_P_MAX];
    for (int m = 0; m < N; ++m) {
        int L = C_P_LEN[m];
        Jet3 res(Iv(C_P_LO[m][L - 1], C_P_HI[m][L - 1]));
        for (int j = L - 2; j >= 0; --j) {
            res = res * eps + Iv(C_P_LO[m][j], C_P_HI[m][j]);
        }
        cs[m] = res;
    }
    v0 = cs[N - 1];
    v1 = cs[N - 1] * Iv((double)(N - 1));
    v2 = cs[N - 1] * Iv((double)((N - 1) * (N - 2)));
    for (int m = N - 2; m >= 0; --m) {
        v0 = v0 * x + cs[m];
        if (m >= 1) v1 = v1 * x + cs[m] * Iv((double)m);
        if (m >= 2) v2 = v2 * x + cs[m] * Iv((double)(m * (m - 1)));
    }
    Iv xm(x.v.hi), em(eps.v.hi);
    Iv r = TWO_THIRDS + em;
    Iv rx = r * xm;
    Iv q0 = rx / Iv((double)(N + 4));
    Iv base = Iv(14.0) * iv_pow_int(r, 4) * INV_FACT[N + 3] / (Iv(1.0) - q0);
    double r0 = (base * iv_pow_int(rx, N)).hi;
    double r1 = (base * Iv((double)N) * r * iv_pow_int(rx, N - 1)).hi;
    double r2 = (base * Iv((double)(N * (N - 1))) * iv_sqr(r) * iv_pow_int(rx, N - 2)).hi;
    double r3 = (base * Iv((double)(N * (N - 1) * (N - 2))) * iv_pow_int(r, 3) * iv_pow_int(rx, N - 3)).hi;
    Iv base_e = Iv(24.0) * iv_pow_int(r, 3) * INV_FACT[N + 2] / (Iv(1.0) - q0);
    double re0 = (base_e * iv_pow_int(rx, N)).hi;
    double re1 = (base_e * Iv((double)N) * r * iv_pow_int(rx, N - 1)).hi;
    double re2 = (base_e * Iv((double)(N * (N - 1))) * iv_sqr(r) * iv_pow_int(rx, N - 2)).hi;
    v0 = j_add_rem(v0, Iv(-r0, r0), Iv(-r1, r1), x, Iv(-re0, re0), eps);
    v1 = j_add_rem(v1, Iv(-r1, r1), Iv(-r2, r2), x, Iv(-re1, re1), eps);
    v2 = j_add_rem(v2, Iv(-r2, r2), Iv(-r3, r3), x, Iv(-re2, re2), eps);
}

static void sqrt_Ldiag_jet_series(const Jet3& u, const Jet3& eps, Jet3& h, Jet3& hp, Jet3& hpp) {
    Jet3 sc, scp, scpp, Pt, Ptp, Ptpp;
    sinhc_half_jet_x(u, eps, sc, scp, scpp);
    P_tilde_jet_x(u, eps, Pt, Ptp, Ptpp);
    Jet3 sq = j_sqrt(Pt);
    Jet3 inv2sq = Iv(0.5) / sq;
    Jet3 sqp = Ptp * inv2sq;
    Jet3 sqpp = Ptpp * inv2sq - j_sqr(Ptp) / (Iv(4.0) * sq * j_sqr(sq));
    Jet3 f = u * sq;
    Jet3 fp = sq + u * sqp;
    Jet3 fpp = Iv(2.0) * sqp + u * sqpp;
    Jet3 invs = j_inv(sc);
    Jet3 invs2 = j_sqr(invs);
    Jet3 invsp = -scp * invs2;
    Jet3 invspp = (Iv(2.0) * j_sqr(scp) * invs - scpp) * invs2;
    h = f * invs;
    hp = fp * invs + f * invsp;
    hpp = fpp * invs + Iv(2.0) * fp * invsp + f * invspp;
}

static void A_jet_series(const Jet3& t, const Jet3& eps, Jet3& A, Jet3& Ap, Jet3& App) {
    Jet3 h, hp, hpp;
    sqrt_Ldiag_jet_series(t, eps, h, hp, hpp);
    Jet3 et = j_exp(t * (-ONE_THIRD));
    A = et * h;
    Ap = et * (hp - h * ONE_THIRD);
    App = et * (hpp - hp * TWO_THIRDS + h * ONE_NINTH);
}

static void B_jet_series(const Jet3& v, const Jet3& eps, Jet3& B, Jet3& Bp, Jet3& Bpp) {
    Jet3 h, hp, hpp;
    sqrt_Ldiag_jet_series(v, eps, h, hp, hpp);
    Jet3 ev = j_exp(v * ONE_SIXTH);
    B = ev * h;
    Bp = ev * (hp + h * ONE_SIXTH);
    Bpp = ev * (hpp + hp * ONE_THIRD + h * ONE_36TH);
}

static void exp_diff_over_phi_series(const Jet3& u, const Jet3& eps, int alpha_coeff, int N,
                                     Jet3& out0, Jet3& out1, Jet3& out2) {
    Jet3 pt, ptp, ptpp;
    phi_tilde_jet_x(u, eps, pt, ptp, ptpp);
    Jet3 a = eps * Iv((double)alpha_coeff) + Iv(0.5);
    Jet3 apow = a;
    Jet3 cs[20];
    for (int m = 0; m < N; ++m) {
        if (m > 0) apow = apow * a;
        cs[m] = (apow - NEG_HALF_POW[m + 1]) * INV_FACT[m + 1];
    }
    Jet3 v0 = cs[N - 1];
    Jet3 v1 = cs[N - 1] * Iv((double)(N - 1));
    Jet3 v2 = cs[N - 1] * Iv((double)((N - 1) * (N - 2)));
    for (int m = N - 2; m >= 0; --m) {
        v0 = v0 * u + cs[m];
        if (m >= 1) v1 = v1 * u + cs[m] * Iv((double)m);
        if (m >= 2) v2 = v2 * u + cs[m] * Iv((double)(m * (m - 1)));
    }
    Iv um(u.v.hi), am(a.v.hi);
    Iv au = am * um;
    Iv q0 = au / Iv((double)(N + 2));
    Iv base = Iv(2.0) * am * INV_FACT[N + 1] / (Iv(1.0) - q0);
    double r0 = (base * iv_pow_int(au, N)).hi;
    double r1 = (base * Iv((double)N) * am * iv_pow_int(au, N - 1)).hi;
    double r2 = (base * Iv((double)(N * (N - 1))) * iv_sqr(am) * iv_pow_int(au, N - 2)).hi;
    double r3 = (base * Iv((double)(N * (N - 1) * (N - 2))) * iv_pow_int(am, 3) * iv_pow_int(au, N - 3)).hi;
    Iv base_e = Iv((double)alpha_coeff) * INV_FACT[N] / (Iv(1.0) - q0);
    double re0 = (base_e * iv_pow_int(au, N)).hi;
    double re1 = (base_e * Iv((double)N) * am * iv_pow_int(au, N - 1)).hi;
    double re2 = (base_e * Iv((double)(N * (N - 1))) * iv_sqr(am) * iv_pow_int(au, N - 2)).hi;
    v0 = j_add_rem(v0, Iv(-r0, r0), Iv(-r1, r1), u, Iv(-re0, re0), eps);
    v1 = j_add_rem(v1, Iv(-r1, r1), Iv(-r2, r2), u, Iv(-re1, re1), eps);
    v2 = j_add_rem(v2, Iv(-r2, r2), Iv(-r3, r3), u, Iv(-re2, re2), eps);
    Jet3 invp = j_inv(pt);
    Jet3 invp2 = j_sqr(invp);
    Jet3 invpp = -ptp * invp2;
    Jet3 invppp = (Iv(2.0) * j_sqr(ptp) * invp - ptpp) * invp2;
    out0 = v0 * invp;
    out1 = v1 * invp + v0 * invpp;
    out2 = v2 * invp + Iv(2.0) * v1 * invpp + v0 * invppp;
}

// ============================================================================
// 5. ZERO-CANCELLATION CLOSED-FORM EVALUATOR WITH _r_tight CLAMPING
// ============================================================================
struct ClosedData {
    Jet3 dB, dBp, dBpp, eBp, eBpp, fm, fmp, fmpp, c_eps, ps, q, qp, qpp;
    bool ok;
};

static Jet3 r_tight_eps(const Jet3& u, const Jet3& eps, const Jet3& ps,
                        const Jet3& alpha, const Jet3& e23, const Jet3& e1e) {
    Jet3 r = alpha * j_sqr(ps) * e23 + ((eps + Iv(1.0)) * ps + Iv(1.0)) * e1e;
    if (u.v.lo >= 3.0) {
        Iv ua(u.v.lo), ub(u.v.hi), ev = eps.v;
        Iv alpha_v = (ev + Iv(1.0)) * (Iv(2.0) * ev + Iv(1.0)) * Iv(0.5);
        Iv psa(psi_point(u.v.lo, ev.hi).lo, psi_point(u.v.lo, ev.lo).hi);
        Iv psb(psi_point(u.v.hi, ev.hi).lo, psi_point(u.v.hi, ev.lo).hi);
        Iv ra = alpha_v * iv_sqr(psa) * iv_exp(-(ua * TWO_THIRDS)) + ((ev + Iv(1.0)) * psa + Iv(1.0)) * iv_exp(-((ev + Iv(1.0)) * ua));
        Iv rb = alpha_v * iv_sqr(psb) * iv_exp(-(ub * TWO_THIRDS)) + ((ev + Iv(1.0)) * psb + Iv(1.0)) * iv_exp(-((ev + Iv(1.0)) * ub));
        Iv tight(std::max(r.v.lo, rb.lo), std::min(r.v.hi, ra.hi));
        return Jet3(tight, r.ds, r.dv, r.de);
    }
    return r;
}

static ClosedData tilde_dB_jet_closed(const Jet3& u, const Jet3& eps, bool need_eB, bool need_d2) {
    ClosedData out;
    out.ok = false;
    Jet3 ep1 = eps + Iv(1.0);
    Jet3 ep21 = Iv(2.0) * eps + Iv(1.0);
    out.c_eps = Iv(6.0) / (ep1 * ep21);
    out.ps = psi_jet(u, eps);
    Jet3 emev = j_exp(-(eps * u));
    out.q = j_inv(out.ps);
    out.qp = -emev * j_sqr(out.q);
    Jet3 alpha = ep1 * ep21 * Iv(0.5);
    Jet3 e23 = j_exp(u * (-TWO_THIRDS));
    Jet3 e1e = j_exp(-(ep1 * u));
    Jet3 r = r_tight_eps(u, eps, out.ps, alpha, e23, e1e);
    if ((Iv(1.0) - r.v).lo <= 0.0) return out;
    Jet3 w = j_sqrt(Iv(1.0) - r);
    Jet3 rp = Iv(2.0) * alpha * out.ps * ((emev - out.ps * ONE_THIRD) * e23 - e1e);
    Jet3 wp1 = w + Iv(1.0);
    Jet3 h = j_inv(wp1);
    Jet3 denom_hp = Iv(2.0) * w * j_sqr(wp1);
    Jet3 hp = rp / denom_hp;

    Jet3 e16 = j_exp(u * (-ONE_SIXTH));
    Jet3 ep12 = eps + Iv(0.5);
    Jet3 e12e = j_exp(-(ep12 * u));
    Jet3 q_add = out.q + ep1;
    Jet3 N0 = (Iv(3.0) * out.ps) * e16 + out.c_eps * q_add * e12e;
    Jet3 N1 = (Iv(3.0) * emev - out.ps * Iv(0.5)) * e16 + out.c_eps * (out.qp - ep12 * q_add) * e12e;
    out.dB = N0 * h;
    out.dBp = N1 * h + N0 * hp;
    out.fm = e12e * out.q;
    out.fmp = -out.fm * (out.q + Iv(0.5));

    if (!need_d2 && !need_eB) {
        out.ok = true;
        return out;
    }

    out.qpp = emev * (emev + Iv(1.0)) * out.q * j_sqr(out.q);
    Jet3 rpp_poly = Iv(1.0) - (Iv(3.0) * eps + FOUR_THIRDS) * out.ps
                  + (Iv(2.0) * j_sqr(eps) + eps * FOUR_THIRDS + TWO_NINTHS) * j_sqr(out.ps);
    Jet3 rpp = Iv(2.0) * alpha * (rpp_poly * e23 + (ep21 * out.ps - Iv(1.0)) * e1e);

    if (need_d2) {
        Jet3 hpp = rpp / denom_hp + j_sqr(rp) * (Iv(3.0) * w + Iv(1.0)) / (Iv(4.0) * w * j_sqr(w) * wp1 * j_sqr(wp1));
        Jet3 N2 = (out.ps * ONE_TWELFTH - (Iv(3.0) * eps + Iv(1.0)) * emev) * e16
                + out.c_eps * (out.qpp - ep21 * out.qp + j_sqr(ep12) * q_add) * e12e;
        out.dBpp = N2 * h + Iv(2.0) * N1 * hp + N0 * hpp;
    }
    if (need_eB) {
        Jet3 wp = -rp / (Iv(2.0) * w);
        Jet3 wpp = -rpp / (Iv(2.0) * w) - j_sqr(rp) / (Iv(4.0) * w * j_sqr(w));
        Jet3 tA = out.q * w;
        Jet3 tAp = out.qp * w + out.q * wp;
        Jet3 tApp = out.qpp * w + Iv(2.0) * out.qp * wp + out.q * wpp;
        out.eBp = tAp + tA * Iv(0.5);
        out.eBpp = tApp + tAp + tA * Iv(0.25);
    }
    out.fmpp = out.fm * (j_sqr(out.q + Iv(0.5)) + emev * j_sqr(out.q));
    out.ok = true;
    return out;
}

// ============================================================================
// 6. THE FIVE REGION-4 EVALUATORS
// ============================================================================
static bool eval_drho_ds_simplex(const Jet3& s, const Jet3& v, const Jet3& eps, Jet3& out) {
    const int N = 16;
    Jet3 sv2 = s + v * Iv(0.5);
    Jet3 v2 = v * Iv(0.5);
    Jet3 a = j_exp(-(eps * sv2));
    Jet3 b = j_exp(-(eps * v2));
    Jet3 c = j_exp(eps * v2);
    Jet3 Z0 = -psi_jet(sv2, eps);
    Jet3 Z1 = -psi_jet(v2, eps);
    Jet3 Z2 = phi_jet(v2, eps);

    auto div_1mtZ = [&](const Jet3* in, Jet3* dst, const Jet3& Z) {
        dst[0] = in[0];
        for (int n = 1; n < N; ++n) dst[n] = in[n] + Z * dst[n - 1];
    };
    Jet3 base[N], f100[N], f110[N], f111[N], f211[N], f311[N], f411[N];
    Jet3 f321[N], f312[N], f221[N], f231[N], f212[N], f213[N], f222[N];
    base[0] = Jet3(Iv(1.0));
    for (int n = 1; n < N; ++n) base[n] = Jet3(Iv(0.0));
    div_1mtZ(base, f100, Z0);
    div_1mtZ(f100, f110, Z1);
    div_1mtZ(f110, f111, Z2);
    div_1mtZ(f111, f211, Z0);
    div_1mtZ(f211, f311, Z0);
    div_1mtZ(f311, f411, Z0);
    div_1mtZ(f311, f321, Z1);
    div_1mtZ(f311, f312, Z2);
    div_1mtZ(f211, f221, Z1);
    div_1mtZ(f221, f231, Z1);
    div_1mtZ(f211, f212, Z2);
    div_1mtZ(f212, f213, Z2);
    div_1mtZ(f221, f222, Z2);

    Jet3 a2 = j_sqr(a);
    Jet3 c300 = (a2 * a) * Iv(1.5);
    Jet3 c210 = eps * (a2 * b);
    Jet3 c201 = eps * (a2 * c);
    Jet3 c120 = (eps - Iv(0.5)) * (a * j_sqr(b));
    Jet3 c102 = (eps - Iv(0.5)) * (a * j_sqr(c));
    Jet3 c111 = (Iv(2.0) * j_sqr(eps) - Iv(2.0) * eps + Iv(0.5)) * (a * b * c);

    Jet3 tot(Iv(0.0)), prod(Iv(1.0));
    for (int n = 0; n < N; ++n) {
        Jet3 term = c300 * f411[n] + c210 * f321[n] + c201 * f312[n]
                  + c120 * f231[n] + c102 * f213[n] + c111 * f222[n];
        tot = tot + (prod * term) * INV_FACT[n + 5];
        prod = prod * (Iv(1.0) - eps * Iv((double)(n + 3)));
    }

    double P3_ub = (Iv(iv_abs_max(c300.v)) + Iv(iv_abs_max(c210.v)) + Iv(iv_abs_max(c201.v))
                  + Iv(iv_abs_max(c120.v)) + Iv(iv_abs_max(c102.v)) + Iv(iv_abs_max(c111.v))).hi / 20.0;
    double M = std::max(iv_abs_max(Z0.v), std::max(iv_abs_max(Z1.v), iv_abs_max(Z2.v)));
    Iv q = Iv(eps.v.hi) * Iv(M);
    Iv omq = Iv(1.0) - q;
    Iv S_geom = Iv((double)((N + 2) * (N + 1))) / omq
              + Iv((double)(2 * N + 3)) * q / iv_sqr(omq)
              + q * (Iv(1.0) + q) / (omq * iv_sqr(omq));
    double rem = (Iv(P3_ub) * iv_pow_int(Iv(M), 5) * iv_pow_int(q, N - 5) * S_geom / Iv(5040.0)).hi;
    double rem_d = (Iv((double)(N + 4)) * Iv(rem) / omq).hi;
    double rem_de = (Iv((double)(N + 4)) * (Iv(M) + Iv(6.0)) * Iv(rem) / omq).hi;

    Jet3 dF = Jet3(Iv(6.0) * tot.v + Iv(-rem, rem),
                   Iv(6.0) * tot.ds + Iv(-rem_d, rem_d),
                   Iv(6.0) * tot.dv + Iv(-rem_d, rem_d),
                   Iv(6.0) * tot.de + Iv(-rem_de, rem_de))
            - j_exp((Iv(2.0) * s + v) * (-ONE_SIXTH)) * ONE_36TH;

    Jet3 A, Ap, App, B, Bp, Bpp;
    A_jet_series(s + v, eps, A, Ap, App);
    B_jet_series(v, eps, B, Bp, Bpp);
    out = dF - App * Bp - Ap * Bpp;
    return true;
}

static bool eval_drho_ds_mid_v(const Jet3& s, const Jet3& v, const Jet3& eps, Jet3& out) {
    Jet3 c_eps = Iv(6.0) / ((eps + Iv(1.0)) * (Iv(2.0) * eps + Iv(1.0)));
    Jet3 sc = j_sqrt(c_eps);
    Jet3 ps_v = psi_jet(v, eps), emev = j_exp(-(eps * v));
    Jet3 qv = j_inv(ps_v), qvp = -emev * j_sqr(qv), qvpp = emev * (emev + Iv(1.0)) * qv * j_sqr(qv);
    Jet3 ftm = j_exp(-((Iv(2.0) * eps + Iv(0.5)) * v)) * qv;
    Jet3 a_ft = qv + (eps + Iv(0.5));
    Jet3 ftmp = -ftm * a_ft;
    Jet3 ftmpp = ftm * (j_sqr(a_ft) + emev * j_sqr(qv));
    Jet3 epv = j_exp(v * Iv(0.5));
    Jet3 fpp = epv * (qv * Iv(0.5) + qvp);
    Jet3 fppp = epv * (qv * Iv(0.25) + qvp + qvpp);
    Jet3 B, Bp, Bpp;
    B_jet_series(v, eps, B, Bp, Bpp);
    Jet3 G1 = c_eps * (fpp - ftmp) - sc * Bp;
    Jet3 G2 = c_eps * (fppp - ftmpp) - sc * Bpp;

    Jet3 t = s + v;
    Jet3 drho0 = -j_exp(s * (-ONE_THIRD) - v * ONE_SIXTH) * ONE_36TH;
    Jet3 ps_t = psi_jet(t, eps), emet = j_exp(-(eps * t));
    Jet3 qt = j_inv(ps_t), qtp = -emet * j_sqr(qt), qtpp = emet * (emet + Iv(1.0)) * qt * j_sqr(qt);
    Jet3 gt = j_exp(-((eps + Iv(0.5)) * t)) * qt;
    Jet3 gtp = -gt * (qt + Iv(0.5));
    Jet3 gtpp = gt * (j_sqr(qt + Iv(0.5)) + emet * j_sqr(qt));
    Jet3 h, hp, hpp;
    exp_diff_over_phi_series(s, eps, 2, 12, h, hp, hpp);
    Jet3 A, Ap, App;
    A_jet_series(t, eps, A, Ap, App);
    Jet3 dApt = sc * qtp - Ap;
    Jet3 dAppt = sc * qtpp - App;
    out = drho0 + c_eps * (hpp * gtp + hp * gtpp) + qtpp * G1 + qtp * G2 + dAppt * Bp + dApt * Bpp;
    return true;
}

static bool eval_drho_ds_closed(const Jet3& s, const Jet3& v, const Jet3& eps, Jet3& out) {
    ClosedData rv = tilde_dB_jet_closed(v, eps, true, true);
    if (!rv.ok) return false;
    Jet3 emev = j_exp(-(eps * v));
    Jet3 ftm = emev * rv.fm;
    Jet3 a_ft = rv.q + (eps + Iv(0.5));
    Jet3 ftmp = -ftm * a_ft;
    Jet3 ftmpp = ftm * (j_sqr(a_ft) + emev * j_sqr(rv.q));
    Jet3 comb_p = rv.dBp - rv.c_eps * ftmp;
    Jet3 comb_pp = rv.dBpp - rv.c_eps * ftmpp;

    Jet3 t = s + v;
    ClosedData rt = tilde_dB_jet_closed(t, eps, false, true);
    if (!rt.ok) return false;

    Jet3 drho0 = -j_exp(s * (-ONE_THIRD) - v * ONE_SIXTH) * ONE_36TH;
    Jet3 h, hp, hpp;
    exp_diff_over_phi_series(s, eps, 2, 12, h, hp, hpp);
    Jet3 drho123a = rv.c_eps * (hpp * rt.fmp + hp * rt.fmpp) + rt.qpp * comb_p + rt.qp * comb_pp;
    Jet3 edApt = rt.dBp - rt.dB * Iv(0.5);
    Jet3 edAppt = rt.dBpp - rt.dBp + rt.dB * Iv(0.25);
    Jet3 drho3b = j_exp(s * Iv(-0.5)) * (edAppt * rv.eBp + edApt * rv.eBpp);
    out = drho0 + drho123a + drho3b;
    return true;
}

static bool eval_rho_small_v(const Jet3& s, const Jet3& v, const Jet3& eps, Jet3& out) {
    Jet3 c_eps = Iv(6.0) / ((eps + Iv(1.0)) * (Iv(2.0) * eps + Iv(1.0)));
    Jet3 sc = j_sqrt(c_eps);
    Jet3 D, Dp, Dpp, B, Bp, Bpp;
    exp_diff_over_phi_series(v, eps, 1, 16, D, Dp, Dpp);
    B_jet_series(v, eps, B, Bp, Bpp);
    Jet3 G1 = c_eps * Dp - sc * Bp;
    Jet3 G2 = c_eps * Dpp - sc * Bpp;

    Jet3 t = s + v;
    Jet3 rho0 = j_exp(s * (-ONE_THIRD) - v * ONE_SIXTH) * ONE_TWELFTH;
    Jet3 ps_s = psi_jet(s, eps), emes = j_exp(-(eps * s));
    Jet3 qs = j_inv(ps_s), qsp = -emes * j_sqr(qs);
    Jet3 ps_t = psi_jet(t, eps), emet = j_exp(-(eps * t));
    Jet3 qt = j_inv(ps_t), qtp = -emet * j_sqr(qt);

    Jet3 e1es = j_exp(-((eps + Iv(1.0)) * s));
    Jet3 emDs_p = (qsp + qs * Iv(0.5)) - e1es * (qsp - (eps + Iv(0.5)) * qs);
    Jet3 epgt_p = -emet * qt * (qt + Iv(0.5));
    Jet3 rho_cross = c_eps * j_exp(v * Iv(-0.5)) * emDs_p * epgt_p;

    Jet3 dAt, dApt;
    if (t.v.hi <= 4.5) {
        Jet3 At, Apt, Appt;
        A_jet_series(t, eps, At, Apt, Appt);
        dAt = sc * qt - At;
        dApt = sc * qtp - Apt;
    } else {
        ClosedData rt = tilde_dB_jet_closed(t, eps, false, false);
        if (!rt.ok) return false;
        Jet3 emt2 = j_exp(t * Iv(-0.5)) / sc;
        dAt = rt.dB * emt2;
        dApt = (rt.dBp - rt.dB * Iv(0.5)) * emt2;
    }
    out = rho0 + rho_cross + qtp * G1 + qt * G2 + dApt * Bp + dAt * Bpp;
    return true;
}

static bool eval_rho_closed(const Jet3& s, const Jet3& v, const Jet3& eps, Jet3& out) {
    ClosedData rv = tilde_dB_jet_closed(v, eps, true, true);
    if (!rv.ok) return false;
    Jet3 G_lead = rv.dBpp - rv.c_eps * rv.fmpp;
    Jet3 ps_fmpp = rv.fmpp * rv.ps;

    Jet3 t = s + v;
    ClosedData rt = tilde_dB_jet_closed(t, eps, false, false);
    if (!rt.ok) return false;

    Jet3 ps_s = psi_jet(s, eps), emes = j_exp(-(eps * s));
    Jet3 qs = j_inv(ps_s), qsp = -emes * j_sqr(qs);
    Jet3 gs = j_exp(-((eps + Iv(0.5)) * s)) * qs;
    Jet3 gsp = -gs * (qs + Iv(0.5));

    Jet3 rho0 = j_exp(s * (-ONE_THIRD) - v * ONE_SIXTH) * ONE_TWELFTH;
    Jet3 rho1 = -rv.c_eps * gsp * rt.fmp;
    Jet3 rho23a = rt.q * G_lead + rt.qp * rv.dBp + rv.c_eps * (qsp * rv.fmp - (emes * qs * rt.q) * ps_fmpp);
    Jet3 edApt = rt.dBp - rt.dB * Iv(0.5);
    Jet3 rho3b = j_exp(s * Iv(-0.5)) * (edApt * rv.eBp + rt.dB * rv.eBpp);
    out = rho0 + rho1 + rho23a + rho3b;
    return true;
}

// ============================================================================
// 7. ADAPTIVE 3D BISECTION WITH MEAN-VALUE FORM
// ============================================================================
enum EvalKind { K_SIMPLEX, K_MID_V, K_DRHO_CLOSED, K_RHO_SMALL_V, K_RHO_CLOSED };

static bool dispatch_eval(EvalKind kind, const Jet3& s, const Jet3& v, const Jet3& e, Jet3& out) {
    switch (kind) {
        case K_SIMPLEX:     return eval_drho_ds_simplex(s, v, e, out);
        case K_MID_V:       return eval_drho_ds_mid_v(s, v, e, out);
        case K_DRHO_CLOSED: return eval_drho_ds_closed(s, v, e, out);
        case K_RHO_SMALL_V: return eval_rho_small_v(s, v, e, out);
        case K_RHO_CLOSED:  return eval_rho_closed(s, v, e, out);
    }
    return false;
}

struct Box3 {
    double sa, sb, va, vb, ea, eb;
    int depth;
};

struct JobSpec {
    EvalKind kind;
    double s0, s1, v0, v1, e0, e1;
    int ns, nv, ne;
    const char* label;
};

struct JobResult {
    const char* label;
    long long cert;
    long long uncert;
    double min_lb;
    int max_depth;
    double sec;
};

static JobResult run_job(const JobSpec& job) {
    std::fesetround(FE_UPWARD);
    auto t0 = std::chrono::steady_clock::now();
    std::vector<Box3> stack;
    stack.reserve(4096);
    for (int k = 0; k < job.ne; ++k) {
        double ea = (k == 0) ? job.e0 : (job.e0 + (job.e1 - job.e0) * k / job.ne);
        double eb = (k + 1 == job.ne) ? job.e1 : (job.e0 + (job.e1 - job.e0) * (k + 1) / job.ne);
        for (int j = 0; j < job.nv; ++j) {
            double va = (j == 0) ? job.v0 : (job.v0 + (job.v1 - job.v0) * j / job.nv);
            double vb = (j + 1 == job.nv) ? job.v1 : (job.v0 + (job.v1 - job.v0) * (j + 1) / job.nv);
            for (int i = 0; i < job.ns; ++i) {
                double sa = (i == 0) ? job.s0 : (job.s0 + (job.s1 - job.s0) * i / job.ns);
                double sb = (i + 1 == job.ns) ? job.s1 : (job.s0 + (job.s1 - job.s0) * (i + 1) / job.ns);
                stack.push_back({sa, sb, va, vb, ea, eb, 0});
            }
        }
    }

    long long cert = 0, uncert = 0;
    double min_lb = 1e30;
    int max_depth = 0;

    while (!stack.empty()) {
        Box3 b = stack.back();
        stack.pop_back();
        Jet3 sj(Iv(b.sa, b.sb), Iv(1.0), Iv(0.0), Iv(0.0));
        Jet3 vj(Iv(b.va, b.vb), Iv(0.0), Iv(1.0), Iv(0.0));
        Jet3 ej(Iv(b.ea, b.eb), Iv(0.0), Iv(0.0), Iv(1.0));
        Jet3 jet;
        bool ok = dispatch_eval(job.kind, sj, vj, ej, jet);
        double lb = -1.0;
        double err_s = -1.0, err_v = -1.0, err_e = -1.0;
        if (ok) {
            if (jet.v.lo > 0.0) {
                lb = jet.v.lo;
            } else {
                // Midpoint + outward-rounded half-widths
                double sm = 0.5 * (b.sa + b.sb);
                double vm = 0.5 * (b.va + b.vb);
                double em = 0.5 * (b.ea + b.eb);
                double hs = std::max(sm - b.sa, b.sb - sm); // FE_UPWARD rounds UP!
                double hv = std::max(vm - b.va, b.vb - vm);
                double he = std::max(em - b.ea, b.eb - em);
                Jet3 fmid;
                if (dispatch_eval(job.kind, Jet3(Iv(sm)), Jet3(Iv(vm)), Jet3(Iv(em)), fmid)) {
                    err_s = iv_abs_max(jet.ds) * hs;
                    err_v = iv_abs_max(jet.dv) * hv;
                    err_e = iv_abs_max(jet.de) * he;
                    Iv mvf = fmid.v + jet.ds * Iv(-hs, hs) + jet.dv * Iv(-hv, hv) + jet.de * Iv(-he, he);
                    lb = std::max(jet.v.lo, mvf.lo);
                }
            }
        }
        if (lb > 0.0) {
            ++cert;
            if (lb < min_lb) min_lb = lb;
            if (b.depth > max_depth) max_depth = b.depth;
        } else {
            if (b.depth >= 28) {
                ++uncert;
                continue;
            }
            double sm = 0.5 * (b.sa + b.sb);
            double vm = 0.5 * (b.va + b.vb);
            double em = 0.5 * (b.ea + b.eb);
            if (err_s >= 0.0) {
                if (err_s >= err_v && err_s >= err_e) {
                    stack.push_back({b.sa, sm, b.va, b.vb, b.ea, b.eb, b.depth + 1});
                    stack.push_back({sm, b.sb, b.va, b.vb, b.ea, b.eb, b.depth + 1});
                } else if (err_v >= err_s && err_v >= err_e) {
                    stack.push_back({b.sa, b.sb, b.va, vm, b.ea, b.eb, b.depth + 1});
                    stack.push_back({b.sa, b.sb, vm, b.vb, b.ea, b.eb, b.depth + 1});
                } else {
                    stack.push_back({b.sa, b.sb, b.va, b.vb, b.ea, em, b.depth + 1});
                    stack.push_back({b.sa, b.sb, b.va, b.vb, em, b.eb, b.depth + 1});
                }
            } else {
                double ws = b.sb - b.sa, wv = b.vb - b.va, we = (b.eb - b.ea) * 20.0;
                if (wv >= ws && wv >= we) {
                    stack.push_back({b.sa, b.sb, b.va, vm, b.ea, b.eb, b.depth + 1});
                    stack.push_back({b.sa, b.sb, vm, b.vb, b.ea, b.eb, b.depth + 1});
                } else if (ws >= wv && ws >= we) {
                    stack.push_back({b.sa, sm, b.va, b.vb, b.ea, b.eb, b.depth + 1});
                    stack.push_back({sm, b.sb, b.va, b.vb, b.ea, b.eb, b.depth + 1});
                } else {
                    stack.push_back({b.sa, b.sb, b.va, b.vb, b.ea, em, b.depth + 1});
                    stack.push_back({b.sa, b.sb, b.va, b.vb, em, b.eb, b.depth + 1});
                }
            }
        }
    }
    double sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    return {job.label, cert, uncert, min_lb, max_depth, sec};
}


static void verify_cpp_selftest() {
    // 1. Verify IEEE-754 FE_UPWARD directed rounding is genuinely active
    volatile double one = 1.0, tiny = 1e-17, three = 3.0;
    double up = one + tiny;
    double dn = -((-one) + (-tiny));
    if (!(up > 1.0 && dn == 1.0)) {
        std::fprintf(stderr, "FATAL: FE_UPWARD rounding not active!\n");
        std::exit(2);
    }
    Iv third = iv_from_rat(1.0, three);
    if (!(third.lo < third.hi && (third * Iv(3.0)).lo <= 1.0 && (third * Iv(3.0)).hi >= 1.0)) {
        std::fprintf(stderr, "FATAL: Interval outward rounding check failed!\n");
        std::exit(2);
    }
    // 2. Verify all 5 evaluators against 25-digit mpmath.iv reference intervals
    struct Ref { EvalKind k; double s, v, e, rlo, rhi; const char* name; };
    Ref refs[5] = {
        {K_SIMPLEX,     0.4, 1.2, 0.1,        2.512785265237838e-02, 2.512785268723761e-02, "K_SIMPLEX"},
        {K_MID_V,       0.5, 3.2, 1.0 / 7.0,  1.251272802478809e-02, 1.251273365382133e-02, "K_MID_V"},
        {K_DRHO_CLOSED, 0.5, 6.0, 1.0 / 7.0,  6.361987939522251e-03, 6.361987940760372e-03, "K_DRHO_CLOSED"},
        {K_RHO_SMALL_V, 2.0, 1.5, 1.0 / 7.0,  3.110684240853345e-02, 3.110684274845710e-02, "K_RHO_SMALL_V"},
        {K_RHO_CLOSED,  5.0, 8.0, 0.1,        5.100952693902983e-03, 5.100952694020222e-03, "K_RHO_CLOSED"},
    };
    for (const auto& r : refs) {
        Iv e_iv = (r.e == 0.1) ? iv_from_rat(1.0, 10.0) : iv_from_rat(1.0, 7.0);
        Jet3 out;
        if (!dispatch_eval(r.k, Jet3(Iv(r.s)), Jet3(Iv(r.v)), Jet3(e_iv), out)) {
            std::fprintf(stderr, "FATAL: C++ self-test failed eval for %s\n", r.name);
            std::exit(2);
        }
        // Check overlap with mpmath.iv reference enclosure
        if (out.v.hi < r.rlo || out.v.lo > r.rhi) {
            std::fprintf(stderr, "FATAL: C++ self-test mismatch for %s: [%.15e, %.15e] vs [%.15e, %.15e]\n",
                         r.name, out.v.lo, out.v.hi, r.rlo, r.rhi);
            std::exit(2);
        }
    }
    std::printf("  C++ self-test passed: FE_UPWARD active & all 5 evaluators overlap mpmath.iv enclosures!\n");
    std::fflush(stdout);
}

int main() {
    std::fesetround(FE_UPWARD);
    init_constants();
    verify_cpp_selftest();

    double e_hi = E_MAX_HI;
    std::vector<JobSpec> jobs = {
        {K_SIMPLEX,     0.0,  1.0,  0.0,  2.5, 0.0, e_hi, 2,  5, 2, "4a:   d/ds rho [0,1]x[0,2.5]"},
        {K_MID_V,       0.0,  1.0,  2.5,  4.0, 0.0, e_hi, 2,  4, 4, "4b1:  d/ds rho [0,1]x[2.5,4]"},
        {K_DRHO_CLOSED, 0.0,  1.0,  4.0, 30.0, 0.0, e_hi, 2, 16, 4, "4b2:  d/ds rho [0,1]x[4,30]"},
        {K_RHO_SMALL_V, 1.0,  4.0,  0.0,  2.5, 0.0, e_hi, 6,  4, 2, "4c1:  rho [1,4]x[0,2.5]"},
        {K_RHO_SMALL_V, 4.0, 25.0,  0.0,  2.5, 0.0, e_hi, 8,  4, 2, "4c2:  rho [4,25]x[0,2.5]"},
        {K_RHO_CLOSED,  1.0,  8.0,  2.5,  4.5, 0.0, e_hi, 6,  6, 4, "4d1a: rho [1,8]x[2.5,4.5]"},
        {K_RHO_CLOSED,  1.0,  8.0,  4.5, 30.0, 0.0, e_hi, 6, 16, 4, "4d1b: rho [1,8]x[4.5,30]"},
        {K_RHO_CLOSED,  8.0, 25.0,  2.5,  4.5, 0.0, e_hi, 6,  6, 4, "4d2a: rho [8,25]x[2.5,4.5]"},
        {K_RHO_CLOSED,  8.0, 25.0,  4.5, 30.0, 0.0, e_hi, 8, 16, 4, "4d2b: rho [8,25]x[4.5,30]"},
    };

    auto t_all = std::chrono::steady_clock::now();
    std::vector<JobResult> results(jobs.size());
    // Run across 2 worker threads
    int next_idx = 0;
    std::vector<std::thread> workers;
    int n_threads = std::min((int)std::thread::hardware_concurrency(), 4);
    if (n_threads < 1) n_threads = 1;

    // Simple atomic-free static round-robin partition
    for (int t = 0; t < n_threads; ++t) {
        workers.emplace_back([&, t]() {
            for (size_t idx = t; idx < jobs.size(); idx += n_threads) {
                results[idx] = run_job(jobs[idx]);
            }
        });
    }
    for (auto& w : workers) w.join();

    long long tot_cert = 0, tot_uncert = 0;
    for (const auto& r : results) {
        std::printf("  [%-30s] certified=%7lld, uncertified=%lld, min_lb=%.4e, max_depth=%2d, time=%.3fs\n",
                    r.label, r.cert, r.uncert, r.min_lb, r.max_depth, r.sec);
        tot_cert += r.cert;
        tot_uncert += r.uncert;
    }
    double tot_sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - t_all).count();
    std::printf("REGION4_SUMMARY certified=%lld uncertified=%lld runtime=%.3f\n", tot_cert, tot_uncert, tot_sec);
    return (tot_uncert == 0) ? 0 : 1;
}
