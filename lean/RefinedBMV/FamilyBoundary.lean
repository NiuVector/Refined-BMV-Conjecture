import RefinedBMV.FamilyA
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Elementary positivity of the repeated-low diagonal throughout the uniform family. -/

open Set Filter
open scoped Topology

namespace RefinedBMV

noncomputable section

theorem hasDerivAt_scalePhi (ε x : ℝ) : HasDerivAt (scalePhi ε) (Real.exp (ε * x)) x := by
  change HasDerivAt (fun t => scalePhi ε t) _ _
  by_cases h : ε = 0
  · subst ε
    simpa [scalePhi] using hasDerivAt_id x
  · have hd := ((((hasDerivAt_id x).const_mul ε).exp).sub_const 1).div_const ε
    simpa [scalePhi, h, mul_div_cancel_right₀] using hd

theorem hasDerivAt_scalePsi (ε x : ℝ) : HasDerivAt (scalePsi ε) (Real.exp (-ε * x)) x := by
  change HasDerivAt (fun t => scalePsi ε t) _ _
  by_cases h : ε = 0
  · subst ε
    simpa [scalePsi] using hasDerivAt_id x
  · have hd := (((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).const_mul (-ε)).exp)).div_const ε
    have hh : (0 - Real.exp (-ε * x) * -ε) / ε = Real.exp (-ε * x) := by
      field_simp [h]
      ring
    simpa [scalePsi, h, hh] using hd

theorem scalePhi_zero (ε : ℝ) : scalePhi ε 0 = 0 := by by_cases h : ε = 0 <;> simp [scalePhi, h]
theorem scalePsi_zero (ε : ℝ) : scalePsi ε 0 = 0 := by by_cases h : ε = 0 <;> simp [scalePsi, h]

theorem scalePhi_pos (ε : ℝ) {x : ℝ} (hx : 0 < x) : 0 < scalePhi ε x := by
  have hmono : StrictMono (scalePhi ε) :=
    strictMono_of_deriv_pos fun z => by
      rw [(hasDerivAt_scalePhi ε z).deriv]
      exact Real.exp_pos _
  simpa [scalePhi_zero] using hmono hx

theorem scalePsi_pos (ε : ℝ) {x : ℝ} (hx : 0 < x) : 0 < scalePsi ε x := by
  have hmono : StrictMono (scalePsi ε) :=
    strictMono_of_deriv_pos fun z => by
      rw [(hasDerivAt_scalePsi ε z).deriv]
      exact Real.exp_pos _
  simpa [scalePsi_zero] using hmono hx

theorem scalePsi_mono (ε : ℝ) : StrictMono (scalePsi ε) :=
  strictMono_of_deriv_pos fun z => by
    rw [(hasDerivAt_scalePsi ε z).deriv]
    exact Real.exp_pos _

theorem le_scalePhi (ε x : ℝ) (hε : 0 ≤ ε) : x ≤ scalePhi ε x := by
  rcases hε.eq_or_lt with h | h
  · simp [scalePhi, ← h]
  · rw [scalePhi, if_neg h.ne', le_div_iff₀ h]
    linarith [Real.add_one_le_exp (ε * x)]

theorem scalePsi_le_self (ε x : ℝ) (hε : 0 ≤ ε) : scalePsi ε x ≤ x := by
  rcases hε.eq_or_lt with h | h
  · simp [scalePsi, ← h]
  · rw [scalePsi, if_neg h.ne', div_le_iff₀ h]
    linarith [Real.add_one_le_exp (-ε * x)]

theorem scalePsi_mul_exp (ε x : ℝ) : scalePsi ε x * Real.exp (ε * x) = scalePhi ε x := by
  by_cases h : ε = 0
  · simp [scalePsi, scalePhi, h]
  rw [scalePsi, scalePhi, if_neg h, if_neg h, div_mul_eq_mul_div, sub_mul,
    one_mul, ← Real.exp_add, show -ε * x + ε * x = 0 by ring, Real.exp_zero]

private theorem scalePsi_exp_sub (ε x : ℝ) : Real.exp (-ε * x) = 1 - ε * scalePsi ε x := by
  by_cases h : ε = 0
  · simp [h]
  rw [scalePsi, if_neg h]
  field_simp [h]
  ring

private theorem scalePhi_gap (ε s v : ℝ) :
    scalePhi ε (s + v) - scalePhi ε s = Real.exp (ε * (s + v)) * scalePsi ε v := by
  by_cases h : ε = 0
  · simp [scalePhi, scalePsi, h]
  rw [scalePhi, scalePhi, scalePsi, if_neg h, if_neg h, if_neg h, ← sub_div, ← mul_div_assoc,
    mul_sub, mul_one, ← Real.exp_add, show ε * (s + v) + -ε * v = ε * s by ring]
  ring

private def tailRatio (ε x : ℝ) : ℝ :=
  (1 + ε) * (1 + 2 * ε) / 2 * scalePsi ε x ^ 2 * Real.exp (-2 * x / 3) +
    ((1 + ε) * scalePsi ε x + 1) * Real.exp (-(1 + ε) * x)

private theorem tailRatio_zero (ε : ℝ) : tailRatio ε 0 = 1 := by
  simp [tailRatio, scalePsi_zero]

private theorem tailRatio_nonneg {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) : 0 ≤ tailRatio ε x := by
  unfold tailRatio
  have := scalePsi_pos ε hx
  positivity

private theorem hasDerivAt_tailRatio (ε x : ℝ) : HasDerivAt (tailRatio ε)
    ((1 + ε) * (1 + 2 * ε) * scalePsi ε x * Real.exp (-(2 / 3 + ε) * x) *
      (1 - Real.exp (-x / 3) - scalePhi ε x / 3)) x := by
  let κ : ℝ := (1 + ε) * (1 + 2 * ε)
  have hexp (c : ℝ) : HasDerivAt (fun t => Real.exp (c * t)) (Real.exp (c * x) * c) x := by
    simpa using ((hasDerivAt_id x).const_mul c).exp
  have h₀ := (((hasDerivAt_scalePsi ε x).pow 2).const_mul (κ / 2)).mul (hexp (-2 / 3))
  have h₁ := (((hasDerivAt_scalePsi ε x).const_mul (1 + ε)).add_const 1).mul (hexp (-(1 + ε)))
  have h₂ : Real.exp (-(2 / 3 + ε) * x) * Real.exp (-x / 3) =
      Real.exp (-(1 + ε) * x) := by rw [← Real.exp_add]; congr 1; ring
  have h₃ : Real.exp (-(2 / 3 + ε) * x) * Real.exp (ε * x) = Real.exp (-2 * x / 3) := by
    rw [← Real.exp_add]; congr 1; ring
  have h₄ : Real.exp (-2 * x / 3) * Real.exp (-ε * x) = Real.exp (-(2 / 3 + ε) * x) := by
    rw [← Real.exp_add]; congr 1; ring
  have h₅ : Real.exp (-2 / 3 * x) = Real.exp (-2 * x / 3) := by congr 1; ring
  have hd : HasDerivAt (tailRatio ε)
      (κ / 2 * ((2 : ℕ) * scalePsi ε x ^ (2 - 1) * Real.exp (-ε * x)) *
          Real.exp (-2 / 3 * x) +
        κ / 2 * scalePsi ε x ^ 2 * (Real.exp (-2 / 3 * x) * (-2 / 3)) +
        ((1 + ε) * Real.exp (-ε * x) * Real.exp (-(1 + ε) * x) +
          ((1 + ε) * scalePsi ε x + 1) *
            (Real.exp (-(1 + ε) * x) * -(1 + ε)))) x := by
    change HasDerivAt (fun z => tailRatio ε z) _ x
    have hfun : (fun z => tailRatio ε z) =
        ((fun z => κ / 2 * (scalePsi ε ^ 2) z) * fun z => Real.exp (-2 / 3 * z)) +
          ((fun z => (1 + ε) * scalePsi ε z + 1) * fun z => Real.exp (-(1 + ε) * z)) := by
      funext z
      simp only [tailRatio, κ, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
      rw [show (-2 : ℝ) * z / 3 = -2 / 3 * z by ring]
    rw [hfun]
    simpa only [Pi.pow_apply] using h₀.add h₁
  convert hd using 1
  rw [h₅]
  norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
  rw [show (1 + ε) * Real.exp (-ε * x) * Real.exp (-(1 + ε) * x) +
          ((1 + ε) * scalePsi ε x + 1) * (Real.exp (-(1 + ε) * x) * -(1 + ε)) =
        -κ * scalePsi ε x * Real.exp (-(1 + ε) * x) by
      rw [scalePsi_exp_sub]
      unfold κ
      ring]
  rw [show κ / 2 * (2 * scalePsi ε x * Real.exp (-ε * x)) * Real.exp (-2 * x / 3) =
    κ * scalePsi ε x * (Real.exp (-2 * x / 3) * Real.exp (-ε * x)) by ring, h₄]
  rw [← scalePsi_mul_exp ε x]
  unfold κ
  linear_combination (-(1 + ε) * (1 + 2 * ε) * scalePsi ε x) * h₂ +
    (-(1 + ε) * (1 + 2 * ε) * scalePsi ε x ^ 2 / 3) * h₃

private theorem tailRatio_lt_one {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) : tailRatio ε x < 1 := by
  have hd : Differentiable ℝ (tailRatio ε) := fun z => (hasDerivAt_tailRatio ε z).differentiableAt
  have hneg (z : ℝ) (hz : 0 < z) : deriv (tailRatio ε) z < 0 := by
    rw [(hasDerivAt_tailRatio ε z).deriv]
    have h₁ := Real.add_one_lt_exp (show -z / 3 ≠ 0 by linarith)
    have h₂ := le_scalePhi ε z hε
    have h₃ := scalePsi_pos ε hz
    exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
  obtain ⟨z, hz, heq⟩ := exists_deriv_eq_slope (f := tailRatio ε) hx hd.continuous.continuousOn hd.differentiableOn
  have h := hneg z hz.1
  rw [heq, tailRatio_zero, sub_zero] at h
  exact sub_neg.mp (by simpa using (div_lt_iff₀ hx).mp h)

private theorem lowerDiagonal_factor {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) :
    lowerDiagonal ε x =
      familyPrefactor ε * Real.exp (2 * x / 3) / scalePsi ε x ^ 2 * (1 - tailRatio ε x) := by
  have hp := scalePsi_pos ε hx
  have hmain : Real.exp (-x / 3) * Real.exp ((1 + 2 * ε) * x) =
      Real.exp (2 * x / 3) * (Real.exp (ε * x))^2 := by
    rw [pow_two, ← mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have hneg : Real.exp (2 * x / 3) * Real.exp (-2 * x / 3) = 1 := by
    rw [← Real.exp_add, show 2 * x / 3 + -2 * x / 3 = 0 by ring, Real.exp_zero]
  have hmix : Real.exp (2 * x / 3) * Real.exp (-(1 + ε) * x) * Real.exp (ε * x) ^ 2 =
      Real.exp (-x / 3) * Real.exp (ε * x) := by
    rw [pow_two, ← mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have hsimple : 1 + (1 + 2 * ε) * (scalePsi ε x * Real.exp (ε * x)) =
      ((1 + ε) * scalePsi ε x + 1) * Real.exp (ε * x) := by
    have hinv : Real.exp (-ε * x) * Real.exp (ε * x) = 1 := by
      rw [← Real.exp_add, show -ε * x + ε * x = 0 by ring, Real.exp_zero]
    rw [scalePsi_exp_sub] at hinv
    linear_combination -hinv
  unfold lowerDiagonal tailRatio
  rw [if_neg hx.ne', ← scalePsi_mul_exp, sub_sub, hsimple]
  unfold familyPrefactor
  field_simp (disch := positivity)
  ring_nf at hmain hmix hneg ⊢
  linear_combination 12 * hmain + 12 * ((1 + ε) * scalePsi ε x + 1) * hmix +
    6 * (1 + ε) * (1 + 2 * ε) * scalePsi ε x ^ 2 * Real.exp (x * ε) ^ 2 * hneg

/-- The rank-one block's diagonal is strictly positive for every nonnegative
    family parameter, including the Duhamel endpoint. -/
theorem lowerDiagonal_pos {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) : 0 < lowerDiagonal ε x := by
  rw [lowerDiagonal_factor hε hx]
  have := scalePsi_pos ε hx
  exact mul_pos (by unfold familyPrefactor; positivity) (sub_pos.mpr (tailRatio_lt_one hε hx))

/-- The gauge of the residual kernel used in the mixed-derivative test. -/
def gaugedResidual (ε s t : ℝ) : ℝ :=
  Real.exp (-(s + t) / 6) * residual ε s t

private def tailRoot (ε x : ℝ) : ℝ := Real.sqrt (1 - tailRatio ε x)

private theorem sqrt_lowerDiagonal {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 < x) :
    Real.sqrt (lowerDiagonal ε x) =
      Real.sqrt (familyPrefactor ε) * Real.exp (x / 3) / scalePsi ε x * tailRoot ε x := by
  have hp := scalePsi_pos ε hx
  have hc : 0 ≤ familyPrefactor ε := by unfold familyPrefactor; positivity
  have he : Real.sqrt (Real.exp (2 * x / 3)) = Real.exp (x / 3) := by
    rw [show 2 * x / 3 = x / 3 + x / 3 by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [lowerDiagonal_factor hε hx, Real.sqrt_mul (by positivity), Real.sqrt_div (by positivity),
    Real.sqrt_mul hc, he, Real.sqrt_sq_eq_abs, abs_of_pos hp, tailRoot]

private theorem exp_mul_exp (a b c : ℝ) (h : a + b = c) :
    Real.exp a * Real.exp b = Real.exp c := by rw [← Real.exp_add, h]

private theorem gaugedResidual_split {ε s v : ℝ} (hε : 0 ≤ ε) (hs : 0 < s) (hv : 0 < v) :
    gaugedResidual ε s (s+v) = familyPrefactor ε *
      (Real.exp (-(s+(s+v))/2) / (scalePhi ε s * scalePhi ε (s+v)) -
        Real.exp (-(1/2+ε)*v) / (scalePsi ε s * scalePsi ε v) +
        Real.exp (v/2) / (scalePsi ε (s+v) * scalePsi ε v) *
          (1 - tailRoot ε (s+v) * tailRoot ε v)) -
      3 * Real.exp (-(s+(s+v))/6) := by
  let t := s + v
  have ht : 0 < t := add_pos hs hv
  have hst : s < t := lt_add_of_pos_right _ hv
  have hsφ := scalePhi_pos ε hs
  have htφ := scalePhi_pos ε ht
  have hsψ := scalePsi_pos ε hs
  have htψ := scalePsi_pos ε ht
  have hvψ := scalePsi_pos ε hv
  have hgap : scalePhi ε t - scalePhi ε s = Real.exp (ε * t) * scalePsi ε v :=
    scalePhi_gap ε s v
  have hrev : scalePhi ε s - scalePhi ε t = -(Real.exp (ε * t) * scalePsi ε v) := by linarith
  have hc : 0 ≤ familyPrefactor ε := by unfold familyPrefactor; positivity
  have hcenter : Real.exp (-(s+t)/6) * Real.exp (-(s+t)/3) = Real.exp (-(s+t)/2) :=
    exp_mul_exp _ _ _ (by ring)
  have h₂ : Real.exp (-(s+t)/2) * Real.exp ((1+2*ε)*s) =
      Real.exp (-(1/2+ε)*v) * Real.exp (ε*s) * Real.exp (ε*t) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  have h₃ : Real.exp (-(s+t)/2) * Real.exp ((1+2*ε)*t) =
      Real.exp (v/2) * (Real.exp (ε*t))^2 := by
    rw [pow_two, ← mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  have h₄ : Real.exp (-(s+t)/6) * Real.exp (t/3) * Real.exp (v/3) = Real.exp (v/2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  have hdiff : t - s = v := by dsimp [t]; ring
  change gaugedResidual ε s t = _
  unfold gaugedResidual residual
  rw [min_eq_left hst.le, max_eq_right hst.le, hdiff, abs_of_pos hv,
    scaledSorted, if_neg hs.ne', if_neg hst.ne, sqrt_lowerDiagonal hε ht, sqrt_lowerDiagonal hε hv,
    scaledDistinct, hgap, hrev, ← scalePsi_mul_exp ε s, ← scalePsi_mul_exp ε t]
  have hleft : Real.exp (-(s+t)/6) *
    (familyPrefactor ε * Real.exp (-(s+t)/3) *
      (1 / ((scalePsi ε s * Real.exp (ε*s)) * (scalePsi ε t * Real.exp (ε*t))) +
        Real.exp ((1+2*ε)*s) / ((scalePsi ε s * Real.exp (ε*s)) * -(Real.exp (ε*t) * scalePsi ε v)) +
        Real.exp ((1+2*ε)*t) / ((scalePsi ε t * Real.exp (ε*t)) * (Real.exp (ε*t) * scalePsi ε v))) - 3 -
      Real.sqrt (familyPrefactor ε) * Real.exp (t/3) / scalePsi ε t * tailRoot ε t *
        (Real.sqrt (familyPrefactor ε) * Real.exp (v/3) / scalePsi ε v * tailRoot ε v)) =
    familyPrefactor ε * (Real.exp (-(s+t)/2) /
      ((scalePsi ε s * Real.exp (ε*s)) * (scalePsi ε t * Real.exp (ε*t))) -
      Real.exp (-(1/2+ε)*v) / (scalePsi ε s * scalePsi ε v) +
      Real.exp (v/2) / (scalePsi ε t * scalePsi ε v) *
        (1 - tailRoot ε t * tailRoot ε v)) - 3 * Real.exp (-(s+t)/6) := by
    -- Expose the three exponential products before cancelling denominators.
    rw [mul_sub, mul_sub]
    have center_eq (a : ℝ) :
        Real.exp (-(s+t)/6) * (familyPrefactor ε * Real.exp (-(s+t)/3) * a) =
          familyPrefactor ε * Real.exp (-(s+t)/2) * a := by
      calc
        _ = familyPrefactor ε * (Real.exp (-(s+t)/6) * Real.exp (-(s+t)/3)) * a := by ring
        _ = _ := by rw [hcenter]
    rw [center_eq]
    have hsqrt := Real.sq_sqrt hc
    field_simp (disch := positivity)
    ring_nf at h₂ h₃ h₄ hsqrt ⊢
    rw [hsqrt]
    linear_combination
      (-(familyPrefactor ε) * scalePsi ε t * Real.exp (t*ε)) * h₂ +
      (familyPrefactor ε * scalePsi ε s * Real.exp (s*ε)) * h₃ -
      (familyPrefactor ε * scalePsi ε s * Real.exp (s*ε) *
        Real.exp (t*ε)^2 * tailRoot ε t * tailRoot ε v) * h₄
  simpa only [t, scalePsi_mul_exp] using hleft

private theorem tendsto_exp_neg_mul (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-c * x)) atTop (𝓝 0) := by
  have h := (tendsto_id.const_mul_atTop hc)
  simpa only [Function.comp_apply, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp h

private theorem tendsto_pow_mul_exp_neg (n : ℕ) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => x^n * Real.exp (-c*x)) atTop (𝓝 0) := by
  simpa only [Real.rpow_natCast] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) c hc

private theorem tendsto_scaled_tailRatio (ε : ℝ) (hε : 0 ≤ ε) :
    Tendsto (fun x : ℝ => Real.exp (x/2) * tailRatio ε x) atTop (𝓝 0) := by
  let κ : ℝ := (1 + ε) * (1 + 2 * ε) / 2
  have hk : 0 ≤ κ := by dsimp [κ]; positivity
  have hc : 0 < (1/2+ε : ℝ) := by positivity
  have h₁ := (tendsto_pow_mul_exp_neg 2 (1/6) (by norm_num)).const_mul κ
  have h₂ := (tendsto_pow_mul_exp_neg 1 (1/2+ε) hc).const_mul (1+ε)
  have h₃ := tendsto_exp_neg_mul (1/2+ε) hc
  have hb : Tendsto (fun x : ℝ => κ * (x^2 * Real.exp (-(1/6)*x)) +
      (1+ε) * (x * Real.exp (-(1/2+ε)*x)) + Real.exp (-(1/2+ε)*x)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, pow_one] using (h₁.add h₂).add h₃
  refine squeeze_zero' ?_ ?_ hb
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (Real.exp_pos _).le (tailRatio_nonneg hε hx)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hs := scalePsi_le_self ε x hε
    have hs' := (scalePsi_pos ε hx).le
    have he₁ := exp_mul_exp (x/2) (-2*x/3) (-(1/6)*x) (by ring)
    have he₂ := exp_mul_exp (x/2) (-(1+ε)*x) (-(1/2+ε)*x) (by ring)
    unfold tailRatio
    rw [mul_add]
    have hp := pow_le_pow_left₀ hs' hs 2
    calc
      _ = κ * (scalePsi ε x^2 * Real.exp (-(1/6)*x)) +
          (1+ε) * (scalePsi ε x * Real.exp (-(1/2+ε)*x)) + Real.exp (-(1/2+ε)*x) := by
        dsimp [κ]
        linear_combination ((1+ε)*(1+2*ε)/2 * scalePsi ε x^2) * he₁ +
          ((1+ε)*scalePsi ε x+1) * he₂
      _ ≤ _ := by gcongr

private theorem tendsto_inv_scalePsi (ε : ℝ) (hε : 0 ≤ ε) :
    Tendsto (fun x : ℝ => (scalePsi ε x)⁻¹) atTop (𝓝 ε) := by
  rcases hε.eq_or_lt with h | h
  · subst ε
    simpa [scalePsi] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  · have he : Tendsto (fun x : ℝ => 1 - Real.exp (-ε*x)) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub (tendsto_exp_neg_mul ε h)
    have hdiv := (tendsto_const_nhds (x := ε)).div he (one_ne_zero : (1 : ℝ) ≠ 0)
    simpa [scalePsi, h.ne', inv_div] using (hdiv :
      Tendsto (fun x : ℝ => ε / (1 - Real.exp (-ε*x))) atTop (𝓝 (ε / 1)))

private theorem tendsTo_tail_defect {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 < s) :
    Tendsto (fun v : ℝ => Real.exp (v/2) *
      (1 - tailRoot ε (s+v) * tailRoot ε v)) atTop (𝓝 0) := by
  have ht : Tendsto (fun v : ℝ => s+v) atTop atTop := by
    exact tendsto_atTop_add_const_left atTop s tendsto_id
  have hv := tendsto_scaled_tailRatio ε hε
  have hshift : Tendsto (fun v : ℝ => Real.exp (v/2) * tailRatio ε (s+v)) atTop (𝓝 0) := by
    have hh := (hv.comp ht).const_mul (Real.exp (-s/2))
    have hEq : (fun v : ℝ => Real.exp (-s/2) * (Real.exp ((s+v)/2) * tailRatio ε (s+v))) =
        fun v : ℝ => Real.exp (v/2) * tailRatio ε (s+v) := by
      funext v
      rw [← mul_assoc, exp_mul_exp (-s/2) ((s+v)/2) (v/2) (by ring)]
    simpa only [mul_zero, Function.comp_apply, hEq] using hh
  have hsum : Tendsto (fun v : ℝ => Real.exp (v/2) *
      (tailRatio ε (s+v) + tailRatio ε v)) atTop (𝓝 0) := by
    simpa only [mul_add, add_zero] using hshift.add hv
  have hw (x : ℝ) (hx : 0 < x) :
      0 ≤ tailRoot ε x ∧ tailRoot ε x ≤ 1 ∧ 1 - tailRoot ε x ≤ tailRatio ε x := by
    have ht := tailRatio_nonneg hε hx
    have hr := (tailRatio_lt_one hε hx).le
    have hn : 0 ≤ tailRoot ε x := Real.sqrt_nonneg _
    have hsq : tailRoot ε x ^ 2 = 1 - tailRatio ε x := Real.sq_sqrt (sub_nonneg.mpr hr)
    have hle : tailRoot ε x ≤ 1 := by nlinarith
    exact ⟨hn, hle, by nlinarith [mul_nonneg hn (sub_nonneg.mpr hle)]⟩
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
    have ⟨hu₁,hu₂,_⟩ := hw (s+v) (add_pos hs hv)
    have ⟨hv₁,hv₂,_⟩ := hw v hv
    have h := mul_le_mul hu₂ hv₂ hv₁ (zero_le_one : (0 : ℝ) ≤ 1)
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
    have ⟨_,hu₂,hu₃⟩ := hw (s+v) (add_pos hs hv)
    have ⟨_,hv₂,hv₃⟩ := hw v hv
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    nlinarith [mul_nonneg (sub_nonneg.mpr hu₂) (sub_nonneg.mpr hv₂)]

/-- The gauged residual tends to zero at the right boundary. -/
theorem gaugedResidual_tendsto_top {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 < s) :
    Tendsto (gaugedResidual ε s) atTop (𝓝 0) := by
  have ht : Tendsto (fun v : ℝ => s+v) atTop atTop := by
    exact tendsto_atTop_add_const_left atTop s tendsto_id
  have ht' : Tendsto (fun t : ℝ => t-s) atTop atTop := by simpa [sub_eq_add_neg] using
    (tendsto_atTop_add_const_right atTop (-s) tendsto_id)
  suffices h : Tendsto (fun v : ℝ => gaugedResidual ε s (s+v)) atTop (𝓝 0) by
    have he : (fun t : ℝ => gaugedResidual ε s (s + (t-s))) = gaugedResidual ε s := by
      funext t
      rw [show s+(t-s)=t by ring]
    have ht := h.comp ht'
    change Tendsto (fun t : ℝ => gaugedResidual ε s (s + (t-s))) atTop (𝓝 0) at ht
    rwa [he] at ht
  have hq := tendsto_inv_scalePsi ε hε
  have hq' : Tendsto (fun v : ℝ => (scalePsi ε (s+v))⁻¹) atTop (𝓝 ε) := hq.comp ht
  have hφ : Tendsto (fun v : ℝ => (scalePhi ε (s+v))⁻¹) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp ht)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
      exact (inv_pos.mpr (scalePhi_pos ε (add_pos hs hv))).le
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
      exact inv_anti₀ (add_pos hs hv) (le_scalePhi ε (s+v) hε)
  have hn (c : ℝ) (hc : 0 < c) : Tendsto (fun v : ℝ => Real.exp (-(s+(s+v))/c)) atTop (𝓝 0) := by
    have hv := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_atTop_add_const_left atTop s ht).atTop_div_const hc)
    simpa only [Function.comp_apply, neg_div] using hv
  have hfirst : Tendsto (fun v : ℝ => Real.exp (-(s+(s+v))/2) /
      (scalePhi ε s * scalePhi ε (s+v))) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
      ((hn 2 (by norm_num)).mul (hφ.const_mul (scalePhi ε s)⁻¹))
  have hsecond : Tendsto (fun v : ℝ => Real.exp (-(1/2+ε)*v) /
      (scalePsi ε s * scalePsi ε v)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
      ((tendsto_exp_neg_mul (1/2+ε) (by positivity)).mul (hq.const_mul (scalePsi ε s)⁻¹))
  have hthird : Tendsto (fun v : ℝ => Real.exp (v/2) / (scalePsi ε (s+v) * scalePsi ε v) *
      (1 - tailRoot ε (s+v)*tailRoot ε v)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using
      (tendsTo_tail_defect hε hs).mul (hq'.mul hq)
  have h := (((hfirst.sub hsecond).add hthird).const_mul (familyPrefactor ε)).sub
    ((hn 6 (by norm_num)).const_mul 3)
  have heq : (fun v : ℝ => gaugedResidual ε s (s+v)) =ᶠ[atTop] fun v : ℝ =>
      familyPrefactor ε *
      (Real.exp (-(s+(s+v))/2) / (scalePhi ε s * scalePhi ε (s+v)) -
        Real.exp (-(1/2+ε)*v) / (scalePsi ε s * scalePsi ε v) +
        Real.exp (v/2) / (scalePsi ε (s+v) * scalePsi ε v) *
          (1-tailRoot ε (s+v)*tailRoot ε v)) - 3*Real.exp (-(s+(s+v))/6) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
    exact gaugedResidual_split hε hs hv
  apply Tendsto.congr' heq.symm
  simpa only [sub_zero, add_zero, mul_zero] using h

end

end RefinedBMV
