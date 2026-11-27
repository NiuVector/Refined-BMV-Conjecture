import numpy as np
import itertools, math

def M_ijk(a, b, c, i, j, k):
    n = i + j + k
    s = 0.0
    for p in itertools.permutations((i, j, k)):
        s += (a**p[0]) * (b**p[1]) * (c**p[2])
    return s / 6.0 - (a * b * c) ** (n / 3.0)

def check_orbit(i, j, k):
    xs = [0.0, 0.01, 0.05, 0.1, 0.2, 0.4, 0.6, 0.8, 0.95]
    ys = [0.01, 0.05, 0.1, 0.2, 0.4, 0.6, 0.8, 0.9, 0.99]
    min_g = 1e9
    min_pt = None
    for x in xs:
        for y in ys:
            if y < x:
                continue
            d221 = M_ijk(y, y, x, i, j, k)
            d331 = M_ijk(1.0, 1.0, x, i, j, k)
            d112 = M_ijk(x, x, y, i, j, k)
            d332 = M_ijk(1.0, 1.0, y, i, j, k)
            d113 = M_ijk(x, x, 1.0, i, j, k)
            d223 = M_ijk(y, y, 1.0, i, j, k)
            d123 = M_ijk(x, y, 1.0, i, j, k)
            s1 = math.sqrt(max(0.0, d221 * d331))
            s2 = math.sqrt(max(0.0, d112 * d332))
            s3 = math.sqrt(max(0.0, d113 * d223))
            g = s1 + s2 + s3 - d123
            if g < min_g:
                min_g = g
                min_pt = (x, y)
    return min_g, min_pt

print("=== Testing S3-symmetrized monomial orbits M_{i,j,k} ===")
for n in range(1, 8):
    for i in range(n + 1):
        for j in range(i, n - i + 1):
            k = n - i - j
            if k < j:
                continue
            if i == j == k:
                continue
            mg, pt = check_orbit(i, j, k)
            status = "PASS" if mg >= -1e-12 else "FAIL"
            if status == "FAIL" or n <= 5:
                print(f"({i},{j},{k}) [n={n}]: {status}  min G = {mg:+.6e} at {pt}")
