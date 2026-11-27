import sympy as sp
import numpy as np
import math

print("==========================================================")
print("PART 1: EXACT SYMPY VERIFICATION OF (1,4),(2,4),(3,4),(4,4)")
print("==========================================================")
a, b, c, d = sp.symbols('a b c d', positive=True)

def h_n_4(x1, x2, x3, x4, n):
    s = 0
    for i in range(n + 1):
        for j in range(n + 1 - i):
            for k in range(n + 1 - i - j):
                l = n - i - j - k
                s += x1**i * x2**j * x3**k * x4**l
    return s

# --- (4,4) ---
G4_even = sp.Matrix([
    [2*a**8 + 2*a**6*c**2 - 3*a**4*c**4 + 2*a**2*c**6 + 2*c**8, 2*(a**3 - c**3)**2, a**4 - 7*a**2*c**2 + c**4],
    [2*(a**3 - c**3)**2, (a - c)**2*(9*a**2 + 26*a*c + 9*c**2), 2*(a - c)**2],
    [a**4 - 7*a**2*c**2 + c**4, 2*(a - c)**2, 5]
])
G4_odd = 4 * sp.Matrix([
    [a**2*c**2*(a**2 + c**2), -2*a**2*c**2],
    [-2*a**2*c**2, a**2 + c**2]
])

def K4_tilde(b_, d_, a_, c_):
    Ge = G4_even.subs({a: a_, c: c_})
    Go = G4_odd.subs({a: a_, c: c_})
    return (sp.Matrix([1, b_**2, b_**4]).T * Ge * sp.Matrix([1, d_**2, d_**4]))[0] \
         + (sp.Matrix([b_, b_**3]).T * Go * sp.Matrix([d_, d_**3]))[0]

diff4 = sp.expand(K4_tilde(b, d, a, c) + K4_tilde(a, c, b, d) - 2*(h_n_4(a**2, b**2, c**2, d**2, 4) - 35*a**2*b**2*c**2*d**2))
print("(4,4) cyclic residual:", diff4)
assert diff4 == 0
print("(4,4) G_even trailing minors:", G4_even[2,2], "|", sp.factor(G4_even[1:,1:].det()), "|", sp.factor(G4_even.det()))
print("(4,4) G_odd  trailing minors:", G4_odd[1,1], "|", sp.factor(G4_odd.det()))

# --- (3,4) ---
G3_even = sp.Matrix([
    [2*a**12 + 2*a**8*c**4 - 7*a**6*c**6 + 2*a**4*c**8 + 2*c**12, 0, 2*a**8 - 3*a**4*c**4 + 2*c**8, -2*a**3*c**3],
    [0, a**2*c**2*(5*a**4 + 3*a**2*c**2 + 5*c**4), -8*a**3*c**3, -5*a**2*c**2],
    [2*a**8 - 3*a**4*c**4 + 2*c**8, -8*a**3*c**3, 5*a**4 - 3*a**2*c**2 + 5*c**4, 0],
    [-2*a**3*c**3, -5*a**2*c**2, 0, 7]
])
G3_odd = sp.Matrix([[2*(a - c)**2*(a**4 + 2*a**3*c + 7*a**2*c**2 + 2*a*c**3 + c**4)]])

def K3_tilde(b_, d_, a_, c_):
    Ge = G3_even.subs({a: a_, c: c_})
    Go = G3_odd.subs({a: a_, c: c_})
    return (sp.Matrix([1, b_**2, b_**4, b_**6]).T * Ge * sp.Matrix([1, d_**2, d_**4, d_**6]))[0] \
         + (sp.Matrix([b_**3]).T * Go * sp.Matrix([d_**3]))[0]

diff3 = sp.expand(K3_tilde(b, d, a, c) + K3_tilde(a, c, b, d) - 2*(h_n_4(a**4, b**4, c**4, d**4, 3) - 20*(a*b*c*d)**3))
print("(3,4) cyclic residual:", diff3)
assert diff3 == 0

# --- (2,4) ---
G2_even = sp.Matrix([
    [2*a**4 - a**2*c**2 + 2*c**4, a**2 - 5*a*c + c**2],
    [a**2 - 5*a*c + c**2, 3]
])
G2_odd = sp.Matrix([[5*(a - c)**2]])

def K2_tilde(b_, d_, a_, c_):
    Ge = G2_even.subs({a: a_, c: c_})
    Go = G2_odd.subs({a: a_, c: c_})
    return (sp.Matrix([1, b_**2]).T * Ge * sp.Matrix([1, d_**2]))[0] + b_*d_*Go[0,0]

diff2 = sp.expand(K2_tilde(b, d, a, c) + K2_tilde(a, c, b, d) - 2*(h_n_4(a**2, b**2, c**2, d**2, 2) - 10*a*b*c*d))
print("(2,4) cyclic residual:", diff2)
assert diff2 == 0

# --- (1,4) ---
G1_even = sp.Matrix([
    [a**4 - a**2*c**2 + c**4, -a*c],
    [-a*c, 1]
])
G1_odd = sp.Matrix([[(a - c)**2]])

def K1_tilde(b_, d_, a_, c_):
    Ge = G1_even.subs({a: a_, c: c_})
    Go = G1_odd.subs({a: a_, c: c_})
    return (sp.Matrix([1, b_**2]).T * Ge * sp.Matrix([1, d_**2]))[0] + b_*d_*Go[0,0]

diff1 = sp.expand(K1_tilde(b, d, a, c) + K1_tilde(a, c, b, d) - (h_n_4(a**4, b**4, c**4, d**4, 1) - 4*a*b*c*d))
print("(1,4) cyclic residual:", diff1)
assert diff1 == 0

print("\n==========================================================")
print("PART 2: ADVERSARIAL COMPLEX INDEFINITE HERMITIAN CHECK (4,4)")
print("==========================================================")
rng = np.random.default_rng(20261127)
G4_even_fn = sp.lambdify((a, c), G4_even, 'numpy')
G4_odd_fn = sp.lambdify((a, c), G4_odd, 'numpy')

def bmv_avg_trace(A, B, n, m):
    dim = A.shape[0]
    dp = [[None]*(m+1) for _ in range(n+1)]
    dp[0][0] = np.eye(dim, dtype=np.complex128)
    for i in range(n+1):
        for j in range(m+1):
            if i == 0 and j == 0: continue
            mat = np.zeros((dim, dim), dtype=np.complex128)
            if i > 0: mat += dp[i-1][j] @ A
            if j > 0: mat += dp[i][j-1] @ B
            dp[i][j] = mat
    return np.real(np.trace(dp[n][m])) / math.comb(n+m, m)

max_rel_err = 0.0
for dim in [2, 3, 4, 6]:
    for trial in range(15):
        al = np.exp(rng.normal(0, 1.5, dim))
        al /= np.max(al)
        A = np.diag(al**2)
        M = rng.normal(size=(dim, dim)) + 1j * rng.normal(size=(dim, dim))
        X = 0.5 * (M + M.conj().T)  # INDEFINITE complex Hermitian!
        B = np.diag(1.0 / al) @ X @ np.diag(1.0 / al)
        lhs = bmv_avg_trace(A, B, 4, 4) - np.real(np.trace(X @ X @ X @ X))
        rhs = 0.0
        for i1 in range(dim):
            for i3 in range(dim):
                Ge = G4_even_fn(al[i1], al[i3])
                Go = G4_odd_fn(al[i1], al[i3])
                w = X[i1, :] * X[:, i3]
                u_vec = np.array([np.sum((al**(p - 2)) * w) for p in [0, 2, 4]])
                v_vec = np.array([np.sum((al**(q - 2)) * w) for q in [1, 3]])
                term = np.real(u_vec.conj() @ Ge @ u_vec + v_vec.conj() @ Go @ v_vec)
                assert term >= -1e-12
                rhs += term / (al[i1]**2 * al[i3]**2)
        rhs /= 35.0
        err = abs(lhs - rhs) / (abs(lhs) + 1e-15)
        max_rel_err = max(max_rel_err, err)

print(f"(4,4) indefinite complex Hermitian check (60 cases, d=2..6): max_rel_err = {max_rel_err:.4e}")
assert max_rel_err < 1e-12
print("ALL M=4 INTEGER GRAM VERIFICATIONS PASSED 100%!")
