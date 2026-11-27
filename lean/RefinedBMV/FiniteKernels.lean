import RefinedBMV.Kernel

/-! The explicit finite-order kernels in the BMV manuscript. The spectral variables
are positive cube roots, so no fractional exponents enter the exact identities. -/

open scoped BigOperators ComplexOrder
open Finset

namespace RefinedBMV

noncomputable section

abbrev PosReal := {x : ℝ // 0 < x}

def ratio (x y : PosReal) : PosReal := ⟨x.1 / y.1, div_pos x.2 y.2⟩

/-- The complete homogeneous polynomial of degree `n` in three variables. -/
def homogeneous (n : ℕ) {R : Type*} [Semiring R] (x y z : R) : R :=
  ∑ p ∈ range (n + 1), ∑ q ∈ range (n - p + 1), x ^ p * y ^ q * z ^ (n - p - q)

/-- `Φₙ(x³,y³,z³)` from the manuscript. -/
def finiteWeight (n : ℕ) (x y z : ℝ) : ℝ :=
  2 / ((n + 1 : ℝ) * (n + 2 : ℝ)) * homogeneous n (x ^ 3) (y ^ 3) (z ^ 3) /
    (x * y * z) ^ n - 1

/-- The scalar part of a finite-order certificate. -/
structure FiniteCertificate (n : ℕ) where
  kernel : PosReal → PosReal → ℝ
  positive : PositiveKernel kernel
  cyclic : ∀ x y z : PosReal,
    kernel (ratio y x) (ratio z x) + kernel (ratio z y) (ratio x y) +
      kernel (ratio x z) (ratio y z) = 3 * finiteWeight n x.1 y.1 z.1

theorem finite_cycle_nonneg {ι : Type} [Fintype ι] {n : ℕ}
    (cert : FiniteCertificate n) (x : ι → PosReal) {X : Matrix ι ι ℂ}
    (hX : X.PosSemidef) :
    0 ≤ cycleSum (fun i j k => finiteWeight n (x i).1 (x j).1 (x k).1) X :=
  cycleSum_nonneg_of_cyclic _ _ X hX
    (fun i => cert.positive ι fun j => ratio (x j) (x i))
    (fun i j k => cert.cyclic (x i) (x j) (x k))

private def rank (f : ℝ → ℝ) (u v : ℝ) : ℝ := f u * f v

private theorem positive_rank (f : ℝ → ℝ) :
    PositiveKernel (fun u v : PosReal => rank f u.1 v.1) :=
  PositiveKernel.rankOne (f ∘ Subtype.val)

def harmonic (u v : ℝ) : ℝ := u * v / (u + v)

theorem positive_harmonic :
    PositiveKernel (fun u v : PosReal => harmonic u.1 v.1) := by
  have h := PositiveKernel.cauchy (fun u : PosReal => u.1⁻¹) (fun u => inv_pos.mpr u.2)
  convert h using 1
  ext u v
  unfold harmonic
  field_simp [u.2.ne', v.2.ne']
  rw [add_comm]

private def f1 (u : ℝ) : ℝ := (u - 1) * (2 * u + 1) / u
private def k1 (u v : ℝ) : ℝ := rank f1 u v * (1 / ((u + 1 / 2) + (v + 1 / 2)))

private theorem k1_positive : PositiveKernel (fun u v : PosReal => k1 u.1 v.1) := by
  exact (positive_rank f1).mul (PositiveKernel.cauchy (fun u : PosReal => u.1 + 1 / 2)
    (fun u => by linarith [u.2]))

private theorem k1_cyclic (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    k1 (y / x) (z / x) + k1 (z / y) (x / y) + k1 (x / z) (y / z) =
      3 * finiteWeight 1 x y z := by
  have rewrite (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
      k1 (b / a) (c / a) =
        (b - a) * (2 * b + a) * (c - a) * (2 * c + a) /
          (a * b * c * (a + b + c)) := by
    unfold k1 rank f1
    field_simp [ha.ne', hb.ne', hc.ne', show a + b + c ≠ 0 by positivity]
    ring
  rw [rewrite x y z hx hy hz, rewrite y z x hy hz hx, rewrite z x y hz hx hy]
  rw [show y * z * x * (y + z + x) = x * y * z * (x + y + z) by ring,
    show z * x * y * (z + x + y) = x * y * z * (x + y + z) by ring]
  norm_num [finiteWeight, homogeneous, sum_range_succ]
  field_simp [hx.ne', hy.ne', hz.ne', show x + y + z ≠ 0 by positivity]
  ring

/-- The exact `(1,3)` certificate. -/
def certificateOne : FiniteCertificate 1 where
  kernel u v := k1 u.1 v.1
  positive := k1_positive
  cyclic x y z := k1_cyclic x.1 y.1 z.1 x.2 y.2 z.2

private def k2 (u v : ℝ) : ℝ := (1 / 2) * k1 (u ^ 2) (v ^ 2) + (1 / 2) * k1 u⁻¹ v⁻¹

private theorem k2_positive : PositiveKernel (fun u v : PosReal => k2 u.1 v.1) := by
  exact ((k1_positive.pullback (fun u : PosReal => (⟨u.1 ^ 2, pow_pos u.2 _⟩ : PosReal))).scale
    (by norm_num : (0 : ℝ) ≤ 1 / 2)).add
    ((k1_positive.pullback (fun u : PosReal => (⟨u.1⁻¹, inv_pos.mpr u.2⟩ : PosReal))).scale
    (by norm_num : (0 : ℝ) ≤ 1 / 2))

private theorem k2_cyclic (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    k2 (y / x) (z / x) + k2 (z / y) (x / y) + k2 (x / z) (y / z) =
      3 * finiteWeight 2 x y z := by
  have hsq := k1_cyclic (x ^ 2) (y ^ 2) (z ^ 2) (pow_pos hx _) (pow_pos hy _) (pow_pos hz _)
  have hinv := k1_cyclic x⁻¹ y⁻¹ z⁻¹ (inv_pos.mpr hx) (inv_pos.mpr hy) (inv_pos.mpr hz)
  simp only [k2, div_pow, inv_div]
  simp only [inv_div_inv] at hinv
  have heq : (1 / 2) * (3 * finiteWeight 1 (x ^ 2) (y ^ 2) (z ^ 2)) +
      (1 / 2) * (3 * finiteWeight 1 x⁻¹ y⁻¹ z⁻¹) = 3 * finiteWeight 2 x y z := by
    norm_num [finiteWeight, homogeneous, sum_range_succ]
    field_simp [hx.ne', hy.ne', hz.ne']
    ring
  linarith only [hsq, hinv, heq]

/-- The exact `(2,3)` certificate. -/
def certificateTwo : FiniteCertificate 2 where
  kernel u v := k2 u.1 v.1
  positive := k2_positive
  cyclic x y z := k2_cyclic x.1 y.1 z.1 x.2 y.2 z.2

private def g (u : ℝ) : ℝ := (1 - u) / (1 + u)
private def f3 (u : ℝ) : ℝ := (1 - u) * (1 + 3 * u) / (u * (1 + u))

private def k3 (u v : ℝ) : ℝ := (3 / 10) * (rank f3 u v + 8 * (rank g u v * harmonic u v))

private theorem k3_positive : PositiveKernel (fun u v : PosReal => k3 u.1 v.1) :=
  ((positive_rank f3).add ((positive_rank g).mul positive_harmonic |>.scale
    (by norm_num : (0 : ℝ) ≤ 8))).scale (by norm_num : (0 : ℝ) ≤ 3 / 10)

private theorem k3_cyclic (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    k3 (y / x) (z / x) + k3 (z / y) (x / y) + k3 (x / z) (y / z) =
      3 * (2 / (4 * 5) * homogeneous 3 x y z / (x * y * z) - 1) := by
  norm_num [k3, rank, f3, g, harmonic, homogeneous, sum_range_succ]
  field_simp (disch := positivity)
  ring

private theorem finiteWeight_mul_three (n : ℕ) (x y z : ℝ) :
    finiteWeight (3 * n) x y z =
      2 / ((↑(3 * n : ℕ) + 1) * (↑(3 * n : ℕ) + 2)) *
        homogeneous (3 * n) (x ^ 3) (y ^ 3) (z ^ 3) / (x ^ 3 * y ^ 3 * z ^ 3) ^ n - 1 := by
  simp [finiteWeight, pow_mul, mul_pow]

private def cube (u : PosReal) : PosReal := ⟨u.1 ^ 3, pow_pos u.2 _⟩

/-- The exact `(3,3)` certificate. -/
def certificateThree : FiniteCertificate 3 where
  kernel u v := k3 (u.1 ^ 3) (v.1 ^ 3)
  positive := k3_positive.pullback cube
  cyclic x y z := by
    change k3 ((y.1 / x.1) ^ 3) ((z.1 / x.1) ^ 3) +
      k3 ((z.1 / y.1) ^ 3) ((x.1 / y.1) ^ 3) +
      k3 ((x.1 / z.1) ^ 3) ((y.1 / z.1) ^ 3) = 3 * finiteWeight (3 * 1) x.1 y.1 z.1
    rw [finiteWeight_mul_three]
    have h := k3_cyclic (x.1 ^ 3) (y.1 ^ 3) (z.1 ^ 3) (pow_pos x.2 _) (pow_pos y.2 _) (pow_pos z.2 _)
    norm_num [div_pow] at h ⊢
    exact h

private def f41 (u : ℝ) : ℝ := 1 / u ^ 4 + 1 / u - 2 * u ^ 2
private def f42 (u : ℝ) : ℝ := 1 / u - u ^ 2
private def f43 (u : ℝ) : ℝ := (1 - u) * (1 + 2 * u) / (u * (1 + u))

private def k4 (u v : ℝ) : ℝ := (1 / 5) *
  (rank f41 u v + rank f42 u v + 5 * rank f43 u v + 5 * rank g u v +
    20 * (rank g u v * harmonic u v))

private theorem k4_positive : PositiveKernel (fun u v : PosReal => k4 u.1 v.1) :=
  (((((positive_rank f41).add (positive_rank f42)).add
    ((positive_rank f43).scale (by norm_num : (0 : ℝ) ≤ 5))).add
    ((positive_rank g).scale (by norm_num : (0 : ℝ) ≤ 5))).add
    ((positive_rank g).mul positive_harmonic |>.scale (by norm_num : (0 : ℝ) ≤ 20))).scale
    (by norm_num : (0 : ℝ) ≤ 1 / 5)

set_option maxHeartbeats 4000000 in
private theorem k4_cyclic (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    k4 (y / x) (z / x) + k4 (z / y) (x / y) + k4 (x / z) (y / z) =
      3 * finiteWeight 4 x y z := by
  norm_num [k4, rank, f41, f42, f43, g, harmonic, finiteWeight, homogeneous, sum_range_succ, div_pow]
  field_simp (disch := positivity)
  ring

/-- The exact `(4,3)` certificate. -/
def certificateFour : FiniteCertificate 4 where
  kernel u v := k4 u.1 v.1
  positive := k4_positive
  cyclic x y z := k4_cyclic x.1 y.1 z.1 x.2 y.2 z.2

private def f61 (u : ℝ) : ℝ := g u * (1 + 3 * u + 5 * u ^ 2) / u ^ 2
private def f62 (u : ℝ) : ℝ := g u * (2 + u)
private def f63 (u : ℝ) : ℝ := g u / u

private def k6 (u v : ℝ) : ℝ := (3 / 28) *
  (rank f61 u v + 7 * rank f62 u v + 4 * rank g u v +
    28 * (rank f63 u v * harmonic u v) + 12 * (rank g u v * harmonic u v))

private theorem k6_positive : PositiveKernel (fun u v : PosReal => k6 u.1 v.1) :=
  (((((positive_rank f61).add ((positive_rank f62).scale (by norm_num : (0 : ℝ) ≤ 7))).add
    ((positive_rank g).scale (by norm_num : (0 : ℝ) ≤ 4))).add
    ((positive_rank f63).mul positive_harmonic |>.scale (by norm_num : (0 : ℝ) ≤ 28))).add
    ((positive_rank g).mul positive_harmonic |>.scale (by norm_num : (0 : ℝ) ≤ 12))).scale
    (by norm_num : (0 : ℝ) ≤ 3 / 28)

set_option maxHeartbeats 4000000 in
private theorem k6_cyclic (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    k6 (y / x) (z / x) + k6 (z / y) (x / y) + k6 (x / z) (y / z) =
      3 * (2 / (7 * 8) * homogeneous 6 x y z / (x * y * z) ^ 2 - 1) := by
  norm_num [k6, rank, f61, f62, f63, g, harmonic, homogeneous, sum_range_succ, div_pow]
  field_simp (disch := positivity)
  ring

/-- The exact `(6,3)` certificate. -/
def certificateSix : FiniteCertificate 6 where
  kernel u v := k6 (u.1 ^ 3) (v.1 ^ 3)
  positive := k6_positive.pullback cube
  cyclic x y z := by
    change k6 ((y.1 / x.1) ^ 3) ((z.1 / x.1) ^ 3) +
      k6 ((z.1 / y.1) ^ 3) ((x.1 / y.1) ^ 3) +
      k6 ((x.1 / z.1) ^ 3) ((y.1 / z.1) ^ 3) = 3 * finiteWeight (3 * 2) x.1 y.1 z.1
    rw [finiteWeight_mul_three]
    have h := k6_cyclic (x.1 ^ 3) (y.1 ^ 3) (z.1 ^ 3) (pow_pos x.2 _) (pow_pos y.2 _) (pow_pos z.2 _)
    norm_num [div_pow] at h ⊢
    exact h

end

end RefinedBMV
