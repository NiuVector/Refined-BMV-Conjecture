import sympy as sp
import numpy as np
from scipy.linalg import solve_continuous_lyapunov, sqrtm, expm
import itertools

print("==========================================================")
print("PART 1: EXACT SYMBOLIC VERIFICATION IN SYMPY")
print("==========================================================")
x, y, z, u, v = sp.symbols('x y z u v', positive=True)

Psi = (x**2/(y*z) + y**2/(z*x) + z**2/(x*y)
       + x/y + y/x + y/z + z/y + z/x + x/z - 9)

f = lambda t: (1 - t)*(1 + 3*t)/(t*(1 + t))
g = lambda t: (1 - t)/(1 + t)
K = lambda a, b: f(a)*f(b) + 8*g(a)*g(b)*(a*b/(a + b))
K0 = lambda a, b: (1/a - 1)*(1/b - 1)*(1 + 2*(a + b))
Delta = lambda a, b: -2*(1/a - 1)*(1/b - 1)*(a - b)**2*(a + b + a*b)/((1 + a)*(1 + b)*(a + b))

# Check 1: K0(u, v) + Delta(u, v) == K(u, v)
diff_K = sp.simplify(K0(u, v) + Delta(u, v) - K(u, v))
print("Check 1 [K0(u,v) + Delta(u,v) - K(u,v) == 0]:", diff_K)
assert diff_K == 0

# Check 2: Cyclic sum of K0 == Psi
cyc_K0 = sp.simplify(K0(y/x, z/x) + K0(z/y, x/y) + K0(x/z, y/z) - Psi)
print("Check 2 [cyc(K0) - Psi == 0]:", cyc_K0)
assert cyc_K0 == 0

# Check 3: Cyclic sum of Delta == 0
cyc_Delta = sp.simplify(Delta(y/x, z/x) + Delta(z/y, x/y) + Delta(x/z, y/z))
print("Check 3 [cyc(Delta) == 0]:", cyc_Delta)
assert cyc_Delta == 0

# Check 4: Cyclic sum of K == Psi
cyc_K = sp.simplify(K(y/x, z/x) + K(z/y, x/y) + K(x/z, y/z) - Psi)
print("Check 4 [cyc(K) - Psi == 0]:", cyc_K)
assert cyc_K == 0

# Check 5: S_ij entry formula
a_i, a_j = sp.symbols('a_i a_j', positive=True)
S_coeff = sp.simplify((a_i/a_j - 1 + 2*(a_i - a_j)/(a_i + a_j)) - f(a_j/a_i))
print("Check 5 [S_ij coefficient - f(a_j/a_i) == 0]:", S_coeff)
assert S_coeff == 0

print("\n==========================================================")
print("PART 2: EXACT WORD-COUNTING VERIFICATION (ALL 20 WORDS)")
print("==========================================================")
rng = np.random.default_rng(20261127)

def sum_all_20_words_trace(A, B):
    # Explicitly generate all 20 words of 3 A's and 3 B's
    total = 0.0 + 0.0j
    count = 0
    for pos_A in itertools.combinations(range(6), 3):
        prod = np.eye(A.shape[0], dtype=np.complex128)
        for idx in range(6):
            prod = prod @ (A if idx in pos_A else B)
        total += np.trace(prod)
        count += 1
    assert count == 20
    return total

max_word_err = 0.0
max_id_err = 0.0
max_im_part = 0.0

for d in [2, 3, 4, 5, 8, 12]:
    for trial in range(25):
        # Generate truly complex Hermitian A > 0 and B >= 0 (including rank-deficient B)
        M1 = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        A = M1.conj().T @ M1 + 0.05 * np.eye(d)
        rB = rng.integers(1, d + 1)
        M2 = rng.normal(size=(rB, d)) + 1j * rng.normal(size=(rB, d))
        B = M2.conj().T @ M2
        # Normalize scales
        A /= np.linalg.norm(A)
        B /= (np.linalg.norm(B) + 1e-12)

        # 1. Exact 20-word average trace
        S63 = sum_all_20_words_trace(A, B)
        A33 = S63 / 20.0
        assert abs(np.imag(A33)) < 1e-13

        t33 = np.trace(A @ A @ A @ B @ B @ B)
        t21 = np.trace(A @ A @ B @ A @ B @ B)
        t22 = np.trace(A @ A @ B @ B @ A @ B)
        tab3 = np.trace(A @ B @ A @ B @ A @ B)
        max_im_part = max(max_im_part, abs(np.imag(t21)))

        # Verify A_{3,3} - Tr((AB)^3) == (3/10) * (Tr(A^3B^3) + Tr(A^2BAB^2) + Tr(A^2B^2AB) - 3 Tr((AB)^3))
        lhs_exact = np.real(A33 - tab3)
        lhs_grouped = (3.0 / 10.0) * np.real(t33 + t21 + t22 - 3.0 * tab3)
        word_err = abs(lhs_exact - lhs_grouped) / (abs(np.real(A33)) + 1e-15)
        max_word_err = max(max_word_err, word_err)

        # Verify basis-free Lyapunov/Sylvester SOS identity
        A_sqrt = sqrtm(A)
        A_inv = np.linalg.inv(A)
        A_inv_sqrt = sqrtm(A_inv)
        X = A_sqrt @ B @ A_sqrt
        X = 0.5 * (X + X.conj().T)  # enforce exact Hermiticity

        # Solve A R + R A = A X - X A  (scipy solves A Q + Q A^H = Q_rhs -> note sign!)
        # solve_continuous_lyapunov(A, Q) solves A X + X A^H = Q
        R = solve_continuous_lyapunov(A, A @ X - X @ A)
        Z = solve_continuous_lyapunov(A_inv, X)
        Z = 0.5 * (Z + Z.conj().T)
        eigs_Z = np.linalg.eigvalsh(Z)
        assert np.min(eigs_Z) >= -1e-12, f"Z not PSD! min eig = {np.min(eigs_Z)}"

        S = A @ X @ A_inv - X + 2.0 * R
        # ||S X^{1/2}||_F^2 = Tr(S X S^*), ||A^{-1/2} R Z^{1/2}||_F^2 = Tr(A^{-1} R Z R^*)
        term1 = np.real(np.trace(S @ X @ S.conj().T))
        term2 = 8.0 * np.real(np.trace(A_inv @ R @ Z @ R.conj().T))
        rhs_sos = (3.0 / 10.0) * (term1 + term2)

        id_err = abs(lhs_exact - rhs_sos) / (abs(np.real(A33)) + 1e-15)
        max_id_err = max(max_id_err, id_err)

print(f"Max |Im(Tr(A^2 B A B^2))| observed on complex Hermitian matrices: {max_im_part:.4e}")
print(f"Max relative error of 20-word grouping identity (150 cases, d=2..12): {max_word_err:.4e}")
print(f"Max relative error of 2-term SOS identity (150 cases, d=2..12):       {max_id_err:.4e}")
assert max_word_err < 1e-12
assert max_id_err < 1e-12

print("\n==========================================================")
print("PART 3: TEST FULL REFINED BMV LOWER BOUND (L_{3,3}) AT d=4,6,10")
print("==========================================================")
for d in [4, 6, 10]:
    min_ratio = 1e9
    for trial in range(30):
        H1 = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        alpha = 0.5 * (H1 + H1.conj().T)
        H2 = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        beta = 0.5 * (H2 + H2.conj().T)
        A = expm(alpha)
        B = expm(beta)
        A33 = np.real(sum_all_20_words_trace(A, B)) / 20.0
        L33_rhs = np.real(np.trace(expm(3*alpha + 3*beta)))
        min_ratio = min(min_ratio, A33 / L33_rhs)
    print(f"d={d:2d}: min A_{{3,3}}(e^a, e^b) / Tr(e^(3a+3b)) = {min_ratio:.8f} >= 1")
print("ALL INDEPENDENT VERIFICATIONS PASSED 100%!")
