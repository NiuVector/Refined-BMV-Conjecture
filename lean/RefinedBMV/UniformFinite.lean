import RefinedBMV.FamilyA
import RefinedBMV.Words
import Mathlib.Algebra.Ring.GeomSum

/-! Identifying the analytic family at `ε = 1/n` with the finite word coefficient. -/

open scoped BigOperators
open Finset

namespace RefinedBMV

noncomputable section

private def twoHomogeneous (n : ℕ) (a b : ℝ) : ℝ :=
  ∑ i ∈ range (n + 1), a ^ i * b ^ (n - i)

private theorem homogeneous_succ (n : ℕ) (x y z : ℝ) :
    homogeneous (n + 1) x y z = x * homogeneous n x y z + twoHomogeneous (n + 1) y z := by
  unfold homogeneous twoHomogeneous
  rw [sum_range_succ', mul_sum]
  simp only [pow_zero, one_mul, Nat.sub_zero]
  apply congrArg (· + _)
  apply sum_congr rfl
  intro p _
  simp only [Nat.add_sub_add_right, pow_succ' x, mul_assoc, mul_sum]

private theorem twoHomogeneous_mul_sub (n : ℕ) (a b : ℝ) :
    twoHomogeneous n a b * (a - b) = a ^ (n + 1) - b ^ (n + 1) := by
  simpa [twoHomogeneous] using geom_sum₂_mul a b (n + 1)

private theorem homogeneous_all_one (n : ℕ) :
    homogeneous n (1 : ℝ) 1 1 = ((n + 1 : ℝ) * (n + 2 : ℝ)) / 2 := by
  induction n with
  | zero => norm_num [homogeneous, sum_range_succ]
  | succ n ih =>
    rw [homogeneous_succ, one_mul, ih]
    simp [twoHomogeneous, Nat.cast_succ]
    ring

private theorem homogeneous_lower_diag (n : ℕ) (z : ℝ) :
    homogeneous n (1 : ℝ) 1 z * (z - 1) ^ 2 = z ^ (n + 2) - 1 - (n + 2 : ℝ) * (z - 1) := by
  induction n with
  | zero => norm_num [homogeneous, sum_range_succ]; ring
  | succ n ih =>
    rw [homogeneous_succ, one_mul]
    have geom := twoHomogeneous_mul_sub (n + 1) 1 z
    rw [one_pow] at geom
    rw [show n.succ + 2 = (n + 2) + 1 by omega, pow_succ]
    push_cast
    linear_combination ih + (1 - z) * geom

private theorem homogeneous_upper_diag (n : ℕ) (z : ℝ) :
    homogeneous n (1 : ℝ) z z * (z - 1) ^ 2 =
      1 - z ^ (n + 2) + (n + 2 : ℝ) * (z - 1) * z ^ (n + 1) := by
  rw [homogeneous_rotate n 1 z z]
  induction n with
  | zero => norm_num [homogeneous, sum_range_succ]; ring
  | succ n ih =>
    rw [homogeneous_succ]
    have geom := twoHomogeneous_mul_sub (n + 1) z 1
    rw [one_pow] at geom
    rw [show n.succ + 2 = (n + 2) + 1 by omega, show n + 2 = (n + 1) + 1 by omega]
    simp only [pow_succ _ ((n + 1) + 1), pow_succ _ (n + 1), Nat.cast_succ]
    simp only [show n + 2 = (n + 1) + 1 by omega, pow_succ _ (n + 1)] at ih geom
    linear_combination z * ih + (z - 1) * geom

private theorem homogeneous_distinct (n : ℕ) (x y z : ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    homogeneous n x y z = x ^ (n + 2) / ((x - y) * (x - z)) +
      y ^ (n + 2) / ((y - x) * (y - z)) + z ^ (n + 2) / ((z - x) * (z - y)) := by
  have hne₁ := sub_ne_zero.mpr hxy
  have hne₂ := sub_ne_zero.mpr hxz
  have hne₃ := sub_ne_zero.mpr hyz
  have hne₄ := sub_ne_zero.mpr hxy.symm
  have hne₅ := sub_ne_zero.mpr hxz.symm
  have hne₆ := sub_ne_zero.mpr hyz.symm
  induction n with
  | zero =>
    norm_num [homogeneous, sum_range_succ]
    field_simp [hne₁, hne₂, hne₃, hne₄, hne₅, hne₆]
    ring
  | succ n ih =>
    rw [homogeneous_succ, ih]
    have hgeom : twoHomogeneous (n + 1) y z = (y ^ (n + 2) - z ^ (n + 2)) / (y - z) :=
      (eq_div_iff hne₃).mpr (twoHomogeneous_mul_sub (n + 1) y z)
    rw [hgeom, show n.succ + 2 = (n + 2) + 1 by omega]
    simp only [pow_succ _ (n + 2)]
    field_simp [hne₁, hne₂, hne₃, hne₄, hne₅, hne₆]
    ring

private theorem finiteWeight_rotate (n : ℕ) (x y z : ℝ) :
    finiteWeight n x y z = finiteWeight n y z x := by
  unfold finiteWeight
  rw [homogeneous_rotate n (x ^ 3) (y ^ 3) (z ^ 3)]
  rw [show x * y * z = y * z * x by ring]

private theorem finiteWeight_swap (n : ℕ) (x y z : ℝ) :
    finiteWeight n x y z = finiteWeight n y x z := by
  unfold finiteWeight
  rw [homogeneous_swap n (x ^ 3) (y ^ 3) (z ^ 3), mul_comm x y]

private theorem finiteWeight_normalize (n : ℕ) (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    finiteWeight n x y z = finiteWeight n 1 (y / x) (z / x) := by
  have hab (a : ℝ) : (a / x) ^ 3 = (x ^ 3)⁻¹ * a ^ 3 := by
    rw [div_pow, div_eq_mul_inv, mul_comm]
  have hhom : homogeneous n 1 ((y / x) ^ 3) ((z / x) ^ 3) =
      ((x ^ 3)⁻¹) ^ n * homogeneous n (x ^ 3) (y ^ 3) (z ^ 3) := by
    rw [hab y, hab z, ← homogeneous_scale, inv_mul_cancel₀ (pow_ne_zero _ hx)]
  unfold finiteWeight
  rw [one_pow, hhom, one_mul, div_mul_div_comm, div_pow, mul_pow, inv_pow,
    pow_right_comm x 3 n]
  have hx' := pow_ne_zero n hx
  have hy' := pow_ne_zero n hy
  have hz' := pow_ne_zero n hz
  field_simp [hx', hy', hz']
  ring

/-- Logarithmic spectral coordinates for exponent `n`, expressed in terms of the positive cube root. -/
def scaledLog (n : ℕ) (x : ℝ) : ℝ := 3 * (n : ℝ) * Real.log x

private theorem scaledLog_sub (n : ℕ) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    scaledLog n y - scaledLog n x = 3 * (n : ℝ) * Real.log (y / x) := by
  rw [Real.log_div hy.ne' hx.ne']
  unfold scaledLog
  ring

private theorem scale_constants (n : ℕ) (hn : 0 < n) :
    familyPrefactor ((n : ℝ)⁻¹) * ((n : ℝ)⁻¹) ^ 2 = 6 / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold familyPrefactor
  field_simp (disch := positivity)

private theorem familyWeight_sorted (ε x y z : ℝ) (hxy : x ≤ y) (hyz : y ≤ z) :
    familyWeight ε x y z = scaledSorted ε (y - x) (z - x) / 3 := by
  simp only [familyWeight, min_eq_left hyz, min_eq_left hxy, max_eq_right hyz,
    max_eq_right (hxy.trans hyz)]
  rw [show x + y + z - x - z - x = y - x by ring]

set_option maxHeartbeats 5000000 in
private theorem scaled_weight_sorted (n : ℕ) (hn : 0 < n)
    (x y z : ℝ) (hx : 0 < x) (hxy : x ≤ y) (hyz : y ≤ z) :
    scaledSorted ((n : ℝ)⁻¹) (scaledLog n y - scaledLog n x) (scaledLog n z - scaledLog n x) / 3 =
      finiteWeight n x y z := by
  have hy := hx.trans_le hxy
  have hz := hy.trans_le hyz
  let u := y / x
  let v := z / x
  let s := scaledLog n y - scaledLog n x
  let t := scaledLog n z - scaledLog n x
  let ε := (n : ℝ)⁻¹
  let A := u ^ 3
  let B := v ^ 3
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have he : 0 < ε := inv_pos.mpr hN
  have hu : 0 < u := div_pos hy hx
  have hv : 0 < v := div_pos hz hx
  change scaledSorted ε s t / 3 = finiteWeight n x y z
  rw [finiteWeight_normalize n x y z hx.ne' hy.ne' hz.ne']
  change scaledSorted ε s t / 3 = finiteWeight n 1 u v
  have hslog : s = 3 * (n : ℝ) * Real.log u := scaledLog_sub n x y hx hy
  have htlog : t = 3 * (n : ℝ) * Real.log v := scaledLog_sub n x z hx hz
  have hexp (d w : ℝ) (hw : 0 < w) (hd : d = 3 * (n : ℝ) * Real.log w) (k : ℕ) :
      Real.exp ((k : ℝ) * ε * d) = (w ^ 3) ^ k := by
    rw [hd]
    have hmul : (k : ℝ) * ε * (3 * (n : ℝ) * Real.log w) = (k : ℝ) * (3 * Real.log w) := by
      dsimp [ε]
      field_simp [hN.ne']
    rw [hmul, Real.exp_nat_mul]
    rw [show 3 * Real.log w = (↑(3 : ℕ) : ℝ) * Real.log w by rfl,
      Real.exp_nat_mul, Real.exp_log hw]
  have hφ (d w : ℝ) (hw : 0 < w) (hd : d = 3 * (n : ℝ) * Real.log w) :
      scalePhi ε d = (w ^ 3 - 1) / ε := by
    unfold scalePhi
    rw [if_neg he.ne']
    simpa using congrArg (fun a : ℝ => (a - 1) / ε) (hexp d w hw hd 1)
  have hExp2 (d w : ℝ) (hw : 0 < w) (hd : d = 3 * (n : ℝ) * Real.log w) :
      Real.exp ((1 + 2 * ε) * d) = (w ^ 3) ^ (n + 2) := by
    rw [show (1 + 2 * ε) * d = (↑(n + 2 : ℕ) : ℝ) * ε * d by
      dsimp [ε]; push_cast; field_simp [hN.ne']]
    exact hexp d w hw hd (n + 2)
  have hExp1 (d w : ℝ) (hw : 0 < w) (hd : d = 3 * (n : ℝ) * Real.log w) :
      Real.exp ((1 + ε) * d) = (w ^ 3) ^ (n + 1) := by
    rw [show (1 + ε) * d = (↑(n + 1 : ℕ) : ℝ) * ε * d by
      dsimp [ε]; push_cast; field_simp [hN.ne']]
    exact hexp d w hw hd (n + 1)
  have hcenter : Real.exp (-(s + t) / 3) = ((u * v) ^ n)⁻¹ := by
    rw [hslog, htlog, ← Real.exp_log (mul_pos hu hv), Real.log_mul hu.ne' hv.ne'] at ⊢
    rw [show -(3 * (n : ℝ) * Real.log u + 3 * (n : ℝ) * Real.log v) / 3 =
      -((n : ℝ) * (Real.log u + Real.log v)) by ring]
    rw [Real.exp_neg, Real.exp_nat_mul]
  have hu3 : u ^ 3 = A := rfl
  have hv3 : v ^ 3 = B := rfl
  have heC := scale_constants n hn
  change familyPrefactor ε * ε ^ 2 = 6 / ((n + 1 : ℝ) * (n + 2 : ℝ)) at heC
  have hfactor : familyPrefactor ε * ε ^ 2 / 3 = 2 / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
    rw [heC]
    ring
  rcases eq_or_lt_of_le hxy with h | h
  · have hs0 : s = 0 := by simp [s, ← h]
    have hu1 : u = 1 := by simpa [u, ← h] using div_self hx.ne'
    rcases eq_or_lt_of_le hyz with h' | h'
    · have ht0 : t = 0 := by simp [t, ← h', ← h]
      have hv1 : v = 1 := by simpa [v, ← h', ← h] using div_self hx.ne'
      rw [hs0, ht0, hu1, hv1]
      simp only [scaledSorted, lowerDiagonal, if_true, zero_div, finiteWeight, one_pow,
        one_mul, div_one, homogeneous_all_one]
      field_simp (disch := positivity)
      ring
    · have htpos : 0 < t := by
        change 0 < scaledLog n z - scaledLog n x
        unfold scaledLog
        have hl := Real.log_lt_log hx (h.trans_lt h')
        exact sub_pos.mpr (mul_lt_mul_of_pos_left hl (by positivity))
      have hvone : 1 < v := (lt_div_iff₀ hx).mpr (by simpa using h.trans_lt h')
      have hBpos : 1 < B := by
        simpa [B] using pow_lt_pow_left₀ hvone (zero_le_one : (0 : ℝ) ≤ 1) (by decide : (3 : ℕ) ≠ 0)
      have hB : B - 1 ≠ 0 := sub_ne_zero.mpr hBpos.ne'
      have hpoly : homogeneous n (1 : ℝ) 1 B =
          (B ^ (n + 2) - 1 - (n + 2 : ℝ) * (B - 1)) / (B - 1) ^ 2 :=
        (eq_div_iff (pow_ne_zero 2 hB)).mpr (homogeneous_lower_diag n B)
      have hc : Real.exp (-t / 3) = (v ^ n)⁻¹ := by simpa [hs0, hu1] using hcenter
      rw [hs0, hu1]
      simp only [scaledSorted, if_true, finiteWeight, one_pow, one_mul]
      rw [lowerDiagonal, if_neg htpos.ne', hExp2 t v hv htlog, hφ t v hv htlog, hc, hv3, hpoly, ← hfactor]
      have hstep : (1 + 2 * ε) * ((B - 1) / ε) = (n + 2 : ℝ) * (B - 1) := by
        dsimp [ε]
        field_simp [hN.ne']
      rw [hstep]
      field_simp [he.ne', hB, pow_ne_zero n hv.ne']
  · have hspos : 0 < s := by
      change 0 < scaledLog n y - scaledLog n x
      unfold scaledLog
      exact sub_pos.mpr (mul_lt_mul_of_pos_left (Real.log_lt_log hx h) (by positivity))
    have huone : 1 < u := (lt_div_iff₀ hx).mpr (by simpa using h)
    have hApos : 1 < A := by
      simpa [A] using pow_lt_pow_left₀ huone (zero_le_one : (0 : ℝ) ≤ 1) (by decide : (3 : ℕ) ≠ 0)
    have hA : A - 1 ≠ 0 := sub_ne_zero.mpr hApos.ne'
    rcases eq_or_lt_of_le hyz with h' | h'
    · have hst : s = t := by simp [s, t, h']
      have huv : u = v := by simp [u, v, h']
      have hpoly : homogeneous n (1 : ℝ) A A =
          (1 - A ^ (n + 2) + (n + 2 : ℝ) * (A - 1) * A ^ (n + 1)) / (A - 1) ^ 2 :=
        (eq_div_iff (pow_ne_zero 2 hA)).mpr (homogeneous_upper_diag n A)
      have hc : Real.exp (-2 * s / 3) = ((u * u) ^ n)⁻¹ := by
        rw [← hst, ← huv] at hcenter
        rw [← hcenter]
        congr 1
        ring
      rw [← hst, ← huv]
      simp only [scaledSorted, if_neg hspos.ne', if_true, finiteWeight, one_pow, one_mul]
      rw [upperDiagonal, if_neg hspos.ne', hExp2 s u hu hslog, hExp1 s u hu hslog,
        hφ s u hu hslog, hc, hu3, hpoly, ← hfactor]
      have hstep : (1 + 2 * ε) * ((A - 1) / ε) = (n + 2 : ℝ) * (A - 1) := by
        dsimp [ε]
        field_simp [hN.ne']
      rw [hstep]
      field_simp [he.ne', hA, pow_ne_zero n (mul_ne_zero hu.ne' hu.ne')]
    · have hst : s < t := by
        change scaledLog n y - scaledLog n x < scaledLog n z - scaledLog n x
        unfold scaledLog
        exact sub_lt_sub_right (mul_lt_mul_of_pos_left (Real.log_lt_log hy h') (by positivity)) _
      have huv : u < v := div_lt_div_of_pos_right h' hx
      have hAB : A < B := by dsimp [A, B]; exact pow_lt_pow_left₀ huv hu.le (by decide)
      have hBpos := hApos.trans hAB
      have hpoly := homogeneous_distinct n 1 A B hApos.ne hBpos.ne hAB.ne
      have hB : B - 1 ≠ 0 := sub_ne_zero.mpr hBpos.ne'
      have hD : A - B ≠ 0 := sub_ne_zero.mpr hAB.ne
      have hD' : B - A ≠ 0 := sub_ne_zero.mpr hAB.ne'
      have hA' : 1 - A ≠ 0 := sub_ne_zero.mpr hApos.ne
      have hB' : 1 - B ≠ 0 := sub_ne_zero.mpr hBpos.ne
      simp only [scaledSorted, if_neg hspos.ne', if_neg hst.ne, scaledDistinct, finiteWeight,
        one_pow, one_mul]
      rw [hφ s u hu hslog, hφ t v hv htlog, hExp2 s u hu hslog, hExp2 t v hv htlog,
        hcenter, hu3, hv3, hpoly, one_pow, ← hfactor]
      rw [show (A - 1) / ε - (B - 1) / ε = (A - B) / ε by ring,
        show (B - 1) / ε - (A - 1) / ε = (B - A) / ε by ring]
      field_simp [he.ne', hA, hB, hA', hB', hD, hD', pow_ne_zero n (mul_ne_zero hu.ne' hv.ne')]
      ring

/-- The exact finite specialization of the uniform family, including repeated eigenvalues. -/
theorem familyWeight_eq_finiteWeight (n : ℕ) (hn : 0 < n)
    (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    familyWeight ((n : ℝ)⁻¹) (scaledLog n x) (scaledLog n y) (scaledLog n z) = finiteWeight n x y z := by
  let P (a b c : ℝ) := 0 < a → 0 < b → 0 < c →
    familyWeight ((n : ℝ)⁻¹) (scaledLog n a) (scaledLog n b) (scaledLog n c) = finiteWeight n a b c
  have hrot (a b c : ℝ) : P a b c ↔ P b c a := by
    dsimp [P]
    rw [familyWeight_rotate ((n : ℝ)⁻¹) (scaledLog n a) (scaledLog n b) (scaledLog n c),
      finiteWeight_rotate n a b c]
    tauto
  have hswap (a b c : ℝ) : P a b c ↔ P b a c := by
    dsimp [P]
    rw [familyWeight_swap ((n : ℝ)⁻¹) (scaledLog n a) (scaledLog n b) (scaledLog n c),
      finiteWeight_swap n a b c]
    tauto
  have sorted {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : P a b c := by
    intro ha hb _
    have hN : 0 < (n : ℝ) := by exact_mod_cast hn
    have h₁ : scaledLog n a ≤ scaledLog n b :=
      mul_le_mul_of_nonneg_left (Real.log_le_log ha hab) (by positivity)
    have h₂ : scaledLog n b ≤ scaledLog n c :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hb hbc) (by positivity)
    rw [familyWeight_sorted _ _ _ _ h₁ h₂]
    exact scaled_weight_sorted n hn a b c ha hab hbc
  exact of_sorted_triple hrot hswap sorted x y z hx hy hz

/-- A positive residual in the source construction gives an exact finite-order certificate. -/
def certificate_of_residual (n : ℕ) (hn : 0 < n)
    (hdiag : ∀ x, 0 < x → 0 ≤ lowerDiagonal ((n : ℝ)⁻¹) x)
    (hres : PositiveKernel (fun s t : PosReal => residual ((n : ℝ)⁻¹) s.1 t.1)) :
    FiniteCertificate n where
  kernel u v := blockKernel ((n : ℝ)⁻¹) (scaledLog n u.1) (scaledLog n v.1)
  positive := (positive_block _ hres).pullback (fun x : PosReal => scaledLog n x.1)
  cyclic x y z := by
    have hlog (a b : PosReal) : scaledLog n (ratio a b).1 = scaledLog n a.1 - scaledLog n b.1 :=
      (scaledLog_sub n b.1 a.1 b.2 a.2).symm
    simp only [hlog]
    rw [← familyWeight_eq_finiteWeight n hn x.1 y.1 z.1 x.2 y.2 z.2]
    exact block_cyclic_identity ((n : ℝ)⁻¹) (scaledLog n x.1) (scaledLog n y.1) (scaledLog n z.1) hdiag

end

end RefinedBMV
