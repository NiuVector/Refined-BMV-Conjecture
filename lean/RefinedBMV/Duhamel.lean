import RefinedBMV.Exponential
import RefinedBMV.WordCoefficient
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv

/-! Recover the third derivative of the exponential trace from the finite word
averages. The approximation converges uniformly on compact complex sets, so
the derivatives converge by the Cauchy integral formula. -/

open Matrix NormedSpace Filter Set
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.Operator

namespace RefinedBMV

noncomputable section

variable {d : ℕ}

local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

private def affineStep (H B : Mat) (n : ℕ) (z : ℂ) : Mat :=
  exp ((n : ℝ)⁻¹ • H) + (n : ℝ)⁻¹ • (z • B)

private theorem exp_continuousMap_apply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : C(X, Mat)) (x : X) : (exp f) x = exp (f x) := by
  let e : C(X, Mat) →+* Mat := (Pi.evalRingHom (fun _ : X => Mat) x).comp ContinuousMap.coeFnRingHom
  have he : Continuous e := by change Continuous fun f : C(X, Mat) => f x; fun_prop
  exact NormedSpace.map_exp e he f

private theorem affinePower_locallyUniform [NeZero d] (H B : Mat) :
    TendstoLocallyUniformlyOn (fun n z => affineStep H B n z ^ (n+3))
      (fun z : ℂ => exp (H + z • B)) atTop univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  by_cases h0 : K.Nonempty
  · letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    letI : Nonempty K := ⟨⟨h0.choose, h0.choose_spec⟩⟩
    let a : C(K, Mat) := ContinuousMap.const K H
    let b : C(K, Mat) := ⟨fun z => (z : ℂ) • B, by fun_prop⟩
    have h := NormedSpace.exponential_affine_power_limit a b 3
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp h ε hε] with n hn z hz
    rw [dist_comm, dist_eq_norm] at hn
    rw [dist_eq_norm]
    let x : K := ⟨z, hz⟩
    have hnorm := ContinuousMap.norm_coe_le_norm
      (exp (a+b) - (exp ((n : ℝ)⁻¹ • a) + (n : ℝ)⁻¹ • b)^(n+3)) x
    refine (le_of_eq ?_).trans_lt (hnorm.trans_lt hn)
    simp [exp_continuousMap_apply, affineStep, a, b, x]
  · have h0' : K = ∅ := Set.not_nonempty_iff_eq_empty.mp h0
    simp [h0', TendstoUniformlyOn]

private theorem iteratedDeriv_along_real (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z) (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => f x) = fun x : ℝ => iteratedDeriv k f x := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have he : deriv (fun x : ℝ => f x) = fun x : ℝ => deriv f x := by
      funext x
      exact ((hf (x : ℂ)).differentiableAt.hasDerivAt.comp_ofReal).deriv
    rw [he, ih (deriv f) (fun z => (hf z).deriv)]
    simp only [iteratedDeriv_succ']

private theorem affine_trace_derivative_limit [NeZero d] (H B : Mat) :
    Tendsto (fun n => iteratedDeriv 3 (fun z => trace (affineStep H B n z ^ (n+3))) 0)
      atTop (𝓝 (iteratedDeriv 3 (fun z : ℂ => trace (exp (H + z • B))) 0)) := by
  let F (n : ℕ) (z : ℂ) := trace (affineStep H B n z ^ (n+3))
  let f (z : ℂ) := trace (exp (H+z • B))
  let L := (Matrix.traceLinearMap (n := Fin d) (α := ℂ) (R := ℂ)).toContinuousLinearMap
  have hu : TendstoLocallyUniformlyOn F f atTop univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K hKU hK
    exact L.uniformContinuous.comp_tendstoUniformlyOn
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp
        (affinePower_locallyUniform H B) K hKU hK)
  have ha (n : ℕ) (z : ℂ) : AnalyticAt ℂ (F n) z := by
    change AnalyticAt ℂ (fun z => L (affineStep H B n z ^ (n+3))) z
    apply (L.analyticAt _).comp
    unfold affineStep
    fun_prop
  have h₁ := hu.deriv (.of_forall fun n z _ => (ha n z).differentiableAt.differentiableWithinAt) isOpen_univ
  have h₂ := h₁.deriv (.of_forall fun n z _ => (ha n z).deriv.differentiableAt.differentiableWithinAt) isOpen_univ
  have h₃ := h₂.deriv (.of_forall fun n z _ => (ha n z).deriv.deriv.differentiableAt.differentiableWithinAt) isOpen_univ
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, F, f, Function.comp_apply] using h₃.tendsto_at (mem_univ 0)

private def normalization (n : ℕ) : ℂ :=
  (1 + (n : ℂ)⁻¹) * ((1 + 2 * (n : ℂ)⁻¹) * (1 + 3 * (n : ℂ)⁻¹))

private theorem normalization_tendsto : Tendsto normalization atTop (𝓝 1) := by
  have h := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)
  simpa [normalization, mul_assoc] using
    (h.const_add 1).mul (((h.const_mul 2).const_add 1).mul ((h.const_mul 3).const_add 1))

private theorem affine_derivative_eq (H B : Mat) {n : ℕ} (hn : 0 < n) :
    iteratedDeriv 3 (fun z => trace (affineStep H B n z ^ (n+3))) 0 =
      normalization n * wordAverage n (exp ((n : ℝ)⁻¹ • H)) B := by
  let A := exp ((n : ℝ)⁻¹ • H)
  let f (z : ℂ) := trace ((A + z • B) ^ (n+3))
  have hf : ContDiff ℂ 3 f := by
    let L := (Matrix.traceLinearMap (n := Fin d) (α := ℂ) (R := ℂ)).toContinuousLinearMap
    change ContDiff ℂ 3 (fun z => L ((A + z • B) ^ (n+3)))
    exact L.contDiff.comp (by fun_prop)
  have he : (fun z : ℂ => trace (affineStep H B n z ^ (n+3))) = fun z => f ((n : ℂ)⁻¹ * z) := by
    funext z
    unfold affineStep f A
    rw [SemigroupAction.mul_smul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    rfl
  rw [he, iteratedDeriv_comp_const_mul hf]
  change (n : ℂ)⁻¹ ^ 3 * iteratedDeriv 3 f ((n : ℂ)⁻¹ * 0) = _
  rw [mul_zero]
  change (n : ℂ)⁻¹ ^ 3 * iteratedDeriv 3 (fun z : ℂ => trace ((A+z • B)^(n+3))) 0 = _
  rw [affine_trace_third_derivative n A B]
  have hh : (6 : ℂ) * ↑((n+3).choose 3) = (n+1)*(n+2)*(n+3) := by
    have h : 6 * (n+3).choose 3 = (n+1)*(n+2)*(n+3) := by
      rw [show (6 : ℕ) = Nat.factorial 3 by decide, ← Nat.descFactorial_eq_factorial_mul_choose]
      rw [show (n+3).descFactorial 3 = (n+1)*((n+2)*(n+3)) by
        simp [Nat.descFactorial_succ]]
      ring
    exact_mod_cast h
  rw [← mul_assoc, hh]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  congr 1
  unfold normalization
  field_simp [hn']

/-- The normalized cubic word trace converges to the actual real third
derivative of the exponential trace. -/
theorem wordAverage_tendsto_duhamel (H B : Mat) :
    Tendsto (fun n : ℕ => wordAverage n (exp ((n : ℝ)⁻¹ • H)) B)
      atTop (𝓝 (iteratedDeriv 3 (fun t : ℝ => trace (exp (H + t • B))) 0)) := by
  by_cases hd : d = 0
  · subst d
    have h : (fun n : ℕ => wordAverage n (exp ((n : ℝ)⁻¹ • H)) B) = fun _ => 0 := by
      funext n
      unfold wordAverage
      change _ * ∑ p : Gap4 n, trace _ = _
      simp [trace_eq_zero_of_isEmpty]
    simp [h, trace_eq_zero_of_isEmpty]
  letI : NeZero d := ⟨hd⟩
  let f (z : ℂ) := trace (exp (H+z • B))
  let L := (Matrix.traceLinearMap (n := Fin d) (α := ℂ) (R := ℂ)).toContinuousLinearMap
  have ha (z : ℂ) : AnalyticAt ℂ f z := by
    change AnalyticAt ℂ (fun z => L (exp (H+z • B))) z
    exact (L.analyticAt _).comp ((exp_analytic (𝕂 := ℂ) _).comp (by fun_prop))
  have hr := congrFun (iteratedDeriv_along_real f ha 3) 0
  change iteratedDeriv 3 (fun t : ℝ => trace (exp (H + t • B))) 0 =
    iteratedDeriv 3 f (↑(0 : ℝ)) at hr
  rw [hr, Complex.ofReal_zero]
  have h := (affine_trace_derivative_limit H B).div normalization_tendsto one_ne_zero
  rw [div_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change iteratedDeriv 3 (fun z => trace (affineStep H B n z ^ (n+3))) 0 / normalization n = _
  rw [affine_derivative_eq H B hn]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn1 (a : ℕ) : (1 : ℂ) + (a : ℂ) * (n : ℂ)⁻¹ ≠ 0 := by
    intro h0
    have he : (n : ℂ) + a = 0 := by
      have hm := congrArg ((n : ℂ) * ·) h0
      field_simp [hn'] at hm
      linear_combination hm
    have hn0 : (n+a : ℕ) ≠ 0 := by omega
    exact hn0 (by exact_mod_cast he)
  have he : normalization n ≠ 0 := by
    unfold normalization
    have ha : 1 + (n : ℂ)⁻¹ ≠ 0 := by simpa only [Nat.cast_one, one_mul] using hn1 1
    exact mul_ne_zero ha (mul_ne_zero (hn1 2) (hn1 3))
  field_simp [he]

/-- A single eventual cubic word lower bound implies the Duhamel derivative
inequality, by taking the verified limit of the normalized coefficients. -/
theorem duhamel_of_eventually_even_word (H B : Mat) (hH : H.IsHermitian)
    (hword : ∀ᶠ n : ℕ in atTop,
      trace ((spectralPower (exp ((n : ℝ)⁻¹ • H)) (n/3) * B)^3) ≤
        wordAverage n (exp ((n : ℝ)⁻¹ • H)) B) :
    trace ((exp ((1/3 : ℝ) • H) * B)^3) ≤
      iteratedDeriv 3 (fun t : ℝ => trace (exp (H+t • B))) 0 := by
  refine ge_of_tendsto (wordAverage_tendsto_duhamel H B) ?_
  filter_upwards [hword, eventually_gt_atTop (0 : ℕ)] with n hn hn'
  have hHerm : (((n : ℝ)⁻¹) • H).IsHermitian := by
    change (((n : ℝ)⁻¹) • H)ᴴ = _
    rw [conjTranspose_smul, hH.eq]
    simp
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn'.ne'
  rw [spectralPower_exp _ hHerm, smul_smul,
    show (n/3 : ℝ) * (n : ℝ)⁻¹ = (1/3 : ℝ) by field_simp [hnR]] at hn
  exact hn

/-- The original derivative-form Duhamel inequality follows from the finite
scalar sign at reciprocal integers of order at least seven. -/
theorem duhamel_of_uniform_mixedDensity (H B : Mat) (hH : H.IsHermitian) (hB : B.PosSemidef)
    (hρ : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1/7 → MixedDensityNonneg ε) :
    trace ((exp ((1/3 : ℝ) • H) * B)^3) ≤
      iteratedDeriv 3 (fun t : ℝ => trace (exp (H+t • B))) 0 := by
  apply duhamel_of_eventually_even_word H B hH
  filter_upwards [eventually_ge_atTop (7 : ℕ)] with n hn
  have hn' : 0 < n := by omega
  have ha : (((n : ℝ)⁻¹) • H).IsHermitian := by
    change (((n : ℝ)⁻¹) • H)ᴴ = _
    rw [conjTranspose_smul, hH.eq]
    simp
  exact even_word_m3_of_mixedDensity n hn' _ _ (exp_posDef _ ha).posSemidef hB
    (hρ _ (by positivity) (by
      have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
      rw [one_div]
      exact inv_anti₀ (by norm_num) hnR))

end

end RefinedBMV
