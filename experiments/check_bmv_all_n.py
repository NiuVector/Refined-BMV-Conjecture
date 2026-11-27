import numpy as np
import math

def h_n_3_fast(x, y, z, n):
    # Exact formula for h_n(x, y, z) using O(n) loop:
    # h_n(x, y, z) = sum_{k=0}^n z^k h_{n-k}(x, y)
    # where h_m(x, y) = (x^{m+1} - y^{m+1})/(x - y) if x != y else (m+1)*x^m
    if abs(x - y) < 1e-12:
        s = 0.0
        for m in range(n + 1):
            s += (m + 1) * (x ** m) * (z ** (n - m))
        return s
    inv = 1.0 / (y - x)
    s = 0.0
    for m in range(n + 1):
        hm = (y ** (m + 1) - x ** (m + 1)) * inv
        s += hm * (z ** (n - m))
    return s

def delta_n_fast(x, y, z, n):
    avg = 2.0 * h_n_3_fast(x, y, z, n) / ((n + 1) * (n + 2))
    gm = (x * y * z) ** (n / 3.0)
    return avg - gm

def G_n_fast(x, y, n):
    d221 = delta_n_fast(y, y, x, n)
    d331 = delta_n_fast(1.0, 1.0, x, n)
    d112 = delta_n_fast(x, x, y, n)
    d332 = delta_n_fast(1.0, 1.0, y, n)
    d113 = delta_n_fast(x, x, 1.0, n)
    d223 = delta_n_fast(y, y, 1.0, n)
    d123 = delta_n_fast(x, y, 1.0, n)
    s1 = math.sqrt(max(0.0, d221 * d331))
    s2 = math.sqrt(max(0.0, d112 * d332))
    s3 = math.sqrt(max(0.0, d113 * d223))
    return (s1 + s2 + s3) - d123

# Check normalized ratio (s1+s2+s3)/d123 on interior 0 <= x <= y < 1
print("=== Checking min (s1+s2+s3)/d123 on 0 <= x <= y <= 0.99 ===")
for n in [1, 2, 3, 4, 5, 6, 7, 8, 10, 15, 20, 30, 50, 100]:
    min_ratio = 1e9
    min_pt = None
    # Dense grid + edge x=0 + near y=1
    xs = np.concatenate([np.linspace(0, 0.99, 50), [0.0, 1e-4, 0.01, 0.999]])
    ys = np.concatenate([np.linspace(0.01, 0.99, 50), [0.995, 0.999]])
    for x in xs:
        for y in ys:
            if y < x or y >= 1.0:
                continue
            d123 = delta_n_fast(x, y, 1.0, n)
            if d123 <= 1e-15:
                continue
            g = G_n_fast(x, y, n)
            r = (g + d123) / d123
            if r < min_ratio:
                min_ratio = r
                min_pt = (round(float(x), 4), round(float(y), 4))
    print(f"n={n:3d}: min (s1+s2+s3)/d123 = {min_ratio:.8f} at (x,y)={min_pt}")

# Also check if (s1+s2+s3) >= d123 holds when we replace Delta_n by JUST the polynomial part
# P_n(x,y,z) = (2/((n+1)(n+2))) h_n(x,y,z) - ... no, P_n(1,1,1) = 1 != 0.
# What about testing (s1+s2+s3) vs d123 for REAL n (e.g. n = 0.5, 1.5, 2.5)?
# And what about checking the exact structure of Delta_n(x,y,z) as a sum of nonnegative terms?
print("\n=== Checking S1, S2, S3 contributions at tightest points for n=5, 10, 30 ===")
for n in [5, 10, 30]:
    for (x, y) in [(0.0, 0.5), (0.0, 0.8), (0.0, 0.95), (0.2, 0.6), (0.5, 0.8), (0.8, 0.9)]:
        d221 = delta_n_fast(y, y, x, n)
        d331 = delta_n_fast(1.0, 1.0, x, n)
        d112 = delta_n_fast(x, x, y, n)
        d332 = delta_n_fast(1.0, 1.0, y, n)
        d113 = delta_n_fast(x, x, 1.0, n)
        d223 = delta_n_fast(y, y, 1.0, n)
        d123 = delta_n_fast(x, y, 1.0, n)
        s1 = math.sqrt(d221*d331)
        s2 = math.sqrt(d112*d332)
        s3 = math.sqrt(d113*d223)
        print(f"n={n:2d} ({x},{y}): s1/d={s1/d123:.4f}, s2/d={s2/d123:.4f}, s3/d={s3/d123:.4f}, sum/d={(s1+s2+s3)/d123:.6f}")
