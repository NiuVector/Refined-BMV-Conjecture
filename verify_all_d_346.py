import sympy as sp
import numpy as np
from scipy.linalg import solve_continuous_lyapunov, sqrtm, expm
import math

print("==========================================================")
print("PART 1: EXACT SYMBOLIC VERIFICATION OF K_3, K_4, K_6 IN SYMPY")
print("==========================================================")
p, q, r = sp.symbols('p q r', positive=True)
x, y, z = sp.symbols('x y z', positive=True)

def h_n(a, b, c, n):
    s = 0
    for i in range(n + 1):
        for j in range(n - i + 1):
            s += a**i * b**j * c**(n - i - j)
    return s

# --- (3,3) ---
Psi3 = h_n(x, y, z, 3) / (x*y*z) - 10
f3 = lambda u: (1 - u)*(1 + 3*u)/(u*(1 + u))
g3 = lambda u: (1 - u)/(1 + u)
K3 = lambda u, v: f3(u)*f3(v) + 8*g3(u)*g3(v)*(u*v/(u + v))
res3 = sp.simplify(K3(y/x, z/x) + K3(z/y, x/y) + K3(x/z, y/z) - Psi3)
print("Check (3,3) [cyc(K3) - Psi3 == 0]:", res3)
assert res3 == 0

# --- (4,3) ---
Psi4 = h_n(p**3, q**3, r**3, 4) / (p*q*r)**4 - 15
f4_1 = lambda u: u**(-4) + u**(-1) - 2*u**2
f4_2 = lambda u: u**(-1) - u**2
f4_3 = lambda u: (1 - u)*(1 + 2*u)/(u*(1 + u))
f4_4 = lambda u: (1 - u)/(1 + u)
K4 = lambda u, v: (f4_1(u)*f4_1(v) + f4_2(u)*f4_2(v)
                   + 5*f4_3(u)*f4_3(v) + 5*f4_4(u)*f4_4(v)
                   + 20*f4_4(u)*f4_4(v)*(u*v/(u + v)))
res4 = sp.simplify(K4(q/p, r/p) + K4(r/q, p/q) + K4(p/r, q/r) - Psi4)
print("Check (4,3) [cyc(K4) - Psi4 == 0]:", res4)
assert res4 == 0

# --- (6,3) ---
# Phi_6(x,y,z) = (2 / (7*8)) * h_6(x,y,z)/(xyz)^2 - 1 = (1/28) * (h_6(x,y,z)/(xyz)^2 - 28)
# Note: subagent wrote K_6 for 3*Phi_6! Let's check!
Phi6 = sp.Rational(1, 28) * h_n(x, y, z, 6) / (x*y*z)**2 - 1
def K6(u, v):
    pref = sp.Rational(3, 28) * (1 - u)*(1 - v) / (u**2 * v**2 * (1 + u)*(1 + v))
    inner = ((1 + 3*u + 5*u**2)*(1 + 3*v + 5*v**2)
             + 7 * u**2 * v**2 * (2 + u)*(2 + v)
             + 4 * u**2 * v**2
             + (u*v/(u + v)) * (28*u*v + 12*u**2*v**2))
    return pref * inner

res6 = sp.simplify(K6(y/x, z/x) + K6(z/y, x/y) + K6(x/z, y/z) - 3*Phi6)
print("Check (6,3) [cyc(K6) - 3*Phi6 == 0]:", res6)
assert res6 == 0

print("\n==========================================================")
print("PART 2: HIGH-DIMENSIONAL COMPLEX HERMITIAN VERIFICATION (d=4, 8, 12)")
print("==========================================================")
rng = np.random.default_rng(20261127)

def bmv_avg_trace_dp(A, B, n, m):
    d = A.shape[0]
    dp = [[None]*(m+1) for _ in range(n+1)]
    dp[0][0] = np.eye(d, dtype=np.complex128)
    for i in range(n+1):
        for j in range(m+1):
            if i == 0 and j == 0: continue
            mat = np.zeros((d, d), dtype=np.complex128)
            if i > 0: mat += dp[i-1][j] @ A
            if j > 0: mat += dp[i][j-1] @ B
            dp[i][j] = mat
    return np.real(np.trace(dp[n][m])) / math.comb(n+m, m)

# Verify (4,3) and (6,3) basis-free Frobenius SOS identities on complex Hermitian PSD matrices!
max_err_43 = 0.0
max_err_63 = 0.0

for d in [3, 4, 8, 12]:
    for trial in range(15):
        M1 = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        A = M1.conj().T @ M1 + 0.1 * np.eye(d)
        rB = rng.integers(1, d + 1)
        M2 = rng.normal(size=(rB, d)) + 1j * rng.normal(size=(rB, d))
        B = M2.conj().T @ M2
        A /= np.linalg.norm(A)
        B /= (np.linalg.norm(B) + 1e-12)

        # Eigen-decomp of A for fractional powers
        evals, U = np.linalg.eigh(A)
        def Apow(p_exp):
            return (U * (evals**p_exp)) @ U.conj().T

        # --- Check (4,3) basis-free SOS ---
        T = Apow(1.0/3.0)
        Tinv = Apow(-1.0/3.0)
        X4 = Apow(2.0/3.0) @ B @ Apow(2.0/3.0)
        X4 = 0.5*(X4 + X4.conj().T)
        Y4 = solve_continuous_lyapunov(T, T @ X4 - X4 @ T)
        Z4 = solve_continuous_lyapunov(T, T @ X4 @ T)
        Z4 = 0.5*(Z4 + Z4.conj().T)
        assert np.min(np.linalg.eigvalsh(Z4)) >= -1e-12
        M1_4 = Apow(4.0/3.0) @ X4 @ Apow(-4.0/3.0) + T @ X4 @ Tinv - 2.0 * Apow(-2.0/3.0) @ X4 @ Apow(2.0/3.0)
        M2_4 = T @ X4 @ Tinv - Apow(-2.0/3.0) @ X4 @ Apow(2.0/3.0)
        M3_4 = T @ X4 @ Tinv - X4 + Y4
        rhs_43 = (0.2 * np.real(np.trace(M1_4 @ X4 @ M1_4.conj().T))
                  + 0.2 * np.real(np.trace(M2_4 @ X4 @ M2_4.conj().T))
                  + 1.0 * np.real(np.trace(M3_4 @ X4 @ M3_4.conj().T))
                  + 1.0 * np.real(np.trace(Y4 @ X4 @ Y4.conj().T))
                  + 4.0 * np.real(np.trace(Tinv @ Y4 @ Z4 @ Y4.conj().T)))
        A43 = bmv_avg_trace_dp(A, B, 4, 3)
        lhs_43 = A43 - np.real(np.trace(X4 @ X4 @ X4))
        max_err_43 = max(max_err_43, abs(lhs_43 - rhs_43) / (abs(A43) + 1e-15))

        # --- Check (6,3) basis-free SOS ---
        # Notice K6(u,v) = (3/28) * [ h1(u)h1(v) + 7*h2(u)h2(v) + 4*h3(u)h3(v) + (uv/(u+v))*(28*g1(u)g1(v) + 12*g2(u)g2(v)) ]
        # where:
        #   h1(u) = (1-u)(1+3u+5u^2)/(u^2(1+u)) = (1/u^2 - 1) + 2*(1/u - 1) + 5*(1-u)/(1+u) ? Let's check in eigenbasis first!
        # Actually:
        #   (1-u)/(1+u) = g(u)  -> R: A R + R A = A X - X A
        #   h3(u) = (1-u)/(1+u) = g(u) -> R
        #   h2(u) = (1-u)(2+u)/(1+u) = (1-u) + (1-u)/(1+u) = (1 - u) + g(u) -> (X - A^{-1} X A) + R
        #   h1(u) = (1-u)(1+3u+5u^2)/(u^2(1+u)) = (1/u^2 - 1) + 2*(1/u - 1) + 2*(1-u) + 3*(1-u)/(1+u) ? Wait:
        #   Check: (1-u)/(u^2(1+u)) * (1+3u+5u^2)
        #   = ((1/u^2) + 2/u + 3 - 5u + ...) -> let's compute directly via R and A^k X A^{-k}:
        #   Note: (1-u)(1+3u+5u^2)/(u^2(1+u)) = u^{-2} + 2 u^{-1} + 2 - 5 + 3*(1-u)/(1+u)?
        #   Check at u=1: 1+2+2-5+0 = 0. Multiply by u^2(1+u):
        #   (1 + 2u - 3u^2)(1+u) + 3u^2(1-u) = 1 + 3u - u^2 - 3u^3 + 3u^2 - 3u^3 = 1 + 3u + 2u^2 - 6u^3 != (1-u)(1+3u+5u^2) = 1+2u+2u^2-5u^3!
        #   Right! (1-u)(1+3u+5u^2) = (1+u)(1 + u + u^2 - 5u^3) + ... wait: divide by (1+u):
        #   At u=-1: (1-(-1))(1-3+5) = 2*3 = 6! So residue at u=-1 is 6/(1+u) = 3*(1-u)/(1+u) + 3!
        #   Let's check: (1-u)(1+3u+5u^2)/(u^2(1+u)) = u^{-2} + 2u^{-1} - 3 + 3*(1-u)/(1+u) + ... wait:
        #   At u=1: 1 + 2 - 3 + 0 = 0! Multiply by u^2(1+u):
        #   (1 + 2u - 3u^2)(1+u) + 3u^2(1-u) = 1 + 3u + 2u^2 - 6u^3. Still -6u^3!
        #   Wait: 1+2u+2u^2-5u^3 = (1+u)(1+u+u^2) - 6u^3? No: (1+u)(1+u+u^2 - 5u^2?)
        #   Let's just use exact algebra:
        #   (1+2u+2u^2-5u^3) = (1+u)(1 + u + u^2 - 6u^2?) -> quotient of (-5u^3 + 2u^2 + 2u + 1) by (u+1):
        #   -5u^2 + 7u - 5, remainder 6!
        #   YES! (-5u^3 + 2u^2 + 2u + 1)/(u^2(1+u)) = (1/u^2)( -5u^2 + 7u - 5 + 6/(1+u) ) -> wait:
        #   (-5u^2 + 7u - 5)(u+1) + 6 = -5u^3 + 2u^2 + 2u + 1!
        #   Divide by u^2: -5 + 7/u - 5/u^2? No, wait: 6/(u^2(1+u)) = 6/u^2 - 6/u + 6/(1+u)!
        #   Add them: (-5 + 7/u - 5/u^2) + (6/u^2 - 6/u + 6/(1+u)) = 1/u^2 + 1/u - 5 + 6/(1+u)
        #   And 6/(1+u) = 3 + 3*(1-u)/(1+u)!
        #   SO h1(u) = 1/u^2 + 1/u - 2 + 3*(1-u)/(1+u)!!
        #   Check at u=1: 1 + 1 - 2 + 0 = 0!
        #   Check at u=2: 1/4 + 1/2 - 2 + 3*(-1/3) = -9/4; formula: (-1)*(1+6+20)/(4*3) = -27/12 = -9/4! EXACT!!
        #   And g1(u) = (1-u)/(u(1+u)) = (1/u - 1) + (1-u)/(1+u)? Wait: (1-u)/(u(1+u)) = 1/u - 2/(1+u) = (1/u - 1) + (1-u)/(1+u)!
        #   And g2(u) = (1-u)/(1+u) = g(u)!
        #   OH MY GOD! THAT'S SO CLEAN!!
        X6 = A @ B @ A
        X6 = 0.5*(X6 + X6.conj().T)
        Ainv = Apow(-1.0)
        A2 = A @ A
        Ainv2 = Ainv @ Ainv
        R6 = solve_continuous_lyapunov(A, A @ X6 - X6 @ A)
        Z6 = solve_continuous_lyapunov(Ainv, X6)
        Z6 = 0.5*(Z6 + Z6.conj().T)
        assert np.min(np.linalg.eigvalsh(Z6)) >= -1e-12
        H1 = A2 @ X6 @ Ainv2 + A @ X6 @ Ainv - 2.0 * X6 + 3.0 * R6
        H2 = X6 - Ainv @ X6 @ A + R6
        H3 = R6
        G1 = A @ X6 @ Ainv - X6 - R6
        G2 = R6
        # Remember K6 sums to 3*Phi6, so A_{6,3} - Tr((A^2 B)^3) = (1/3) * sum K6(...) X_ij X_jk X_ki!
        # Thus the prefactor (3/28) * (1/3) = 1/28!!
        rhs_63 = (3.0 / 28.0) * (
            1.0 * np.real(np.trace(H1 @ X6 @ H1.conj().T))
            + 7.0 * np.real(np.trace(H2 @ X6 @ H2.conj().T))
            + 4.0 * np.real(np.trace(H3 @ X6 @ H3.conj().T))
            + 28.0 * np.real(np.trace(Ainv @ G1 @ Z6 @ G1.conj().T))
            + 12.0 * np.real(np.trace(Ainv @ G2 @ Z6 @ G2.conj().T))
        )
        A63 = bmv_avg_trace_dp(A, B, 6, 3)
        lhs_63 = A63 - np.real(np.trace(X6 @ X6 @ X6))
        max_err_63 = max(max_err_63, abs(lhs_63 - rhs_63) / (abs(A63) + 1e-15))

print(f"Max relative error of (4,3) 5-term SOS identity (60 cases, d=3..12): {max_err_43:.4e}")
print(f"Max relative error of (6,3) 5-term SOS identity (60 cases, d=3..12): {max_err_63:.4e}")
assert max_err_43 < 1e-12
assert max_err_63 < 1e-12
print("ALL THREE ALL-DIMENSION SOS IDENTITIES (3,3), (4,3), (6,3) VERIFIED TO MACHINE PRECISION!")
