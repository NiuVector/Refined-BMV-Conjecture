import RefinedBMV.FamilyBoundary
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! The analytic regularity needed for the finite rectangle argument. -/

open Filter Set
open scoped Topology

namespace RefinedBMV

noncomputable section

private theorem phi_strictMono (ε : ℝ) : StrictMono (scalePhi ε) :=
  strictMono_of_deriv_pos fun x => by rw [(hasDerivAt_scalePhi ε x).deriv]; exact Real.exp_pos _

private theorem phi_smooth (ε : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (scalePhi ε) := by
  change ContDiff ℝ n (fun x => scalePhi ε x)
  by_cases h : ε = 0
  · simpa only [scalePhi, if_pos h] using (contDiff_id : ContDiff ℝ n (id : ℝ → ℝ))
  · simp only [scalePhi, if_neg h]
    fun_prop

private theorem lowerDiagonal_smooth {ε x : ℝ} (hx : 0 < x) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (lowerDiagonal ε) x := by
  have hφ := (phi_smooth ε (n := n)).contDiffAt (x := x)
  have hne : scalePhi ε x ^ 2 ≠ 0 := pow_ne_zero _ (scalePhi_pos ε hx).ne'
  let f (z : ℝ) := familyPrefactor ε * Real.exp (-z / 3) *
    (Real.exp ((1 + 2 * ε) * z) - 1 - (1 + 2 * ε) * scalePhi ε z) /
    scalePhi ε z ^ 2 - 3
  have hf : ContDiffAt ℝ n f x := by unfold f; fun_prop (disch := assumption)
  apply hf.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with z hz
  exact if_neg (ne_of_gt hz)

private def nodeExp (ε x : ℝ) : ℝ := Real.exp ((1 + 2 * ε) * x)

private def nodeSlope (ε x y : ℝ) : ℝ :=
  (nodeExp ε y - nodeExp ε x) / (scalePhi ε y - scalePhi ε x)

private theorem nodeSlope_comm (ε x y : ℝ) : nodeSlope ε x y = nodeSlope ε y x := by
  unfold nodeSlope
  rw [← neg_sub (nodeExp ε x), ← neg_sub (scalePhi ε x), neg_div_neg_eq]

private theorem tendsto_nodeSlope (ε x : ℝ) :
    Tendsto (nodeSlope ε x) (𝓝[≠] x)
      (𝓝 ((1 + 2 * ε) * Real.exp ((1 + ε) * x))) := by
  have hA : HasDerivAt (nodeExp ε) (Real.exp ((1 + 2 * ε) * x) * (1 + 2 * ε)) x := by
    simpa [nodeExp, id_eq] using ((hasDerivAt_id x).const_mul (1 + 2 * ε)).exp
  have h := hA.tendsto_slope.div (hasDerivAt_scalePhi ε x).tendsto_slope (Real.exp_pos _).ne'
  rw [show Real.exp ((1 + 2 * ε) * x) * (1 + 2 * ε) / Real.exp (ε * x) =
      (1 + 2 * ε) * Real.exp ((1 + ε) * x) by
    rw [mul_comm (Real.exp _), mul_div_assoc, ← Real.exp_sub]
    congr 2
    ring] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hy
  simp only [Pi.div_apply, slope_def_field, nodeSlope]
  rw [div_div_div_cancel_right₀ hne]

private theorem nodeSlope_continuousAt_right {ε x y : ℝ} (hxy : x ≠ y) :
    ContinuousAt (nodeSlope ε x) y := by
  have hφ : ContinuousAt (scalePhi ε) y := (hasDerivAt_scalePhi ε y).continuousAt
  have hne : scalePhi ε y - scalePhi ε x ≠ 0 :=
    sub_ne_zero.mpr (fun h => hxy ((phi_strictMono ε).injective h).symm)
  change ContinuousAt (fun z => nodeSlope ε x z) y
  unfold nodeSlope nodeExp
  fun_prop (disch := assumption)

private theorem scaledDistinct_eq {ε s t : ℝ} (hs : 0 < s) (hst : s < t) :
    scaledDistinct ε s t = familyPrefactor ε * Real.exp (-(s+t)/3) *
      ((nodeSlope ε s t - nodeSlope ε 0 s) / scalePhi ε t) - 3 := by
  have ht := hs.trans hst
  have hφs := scalePhi_pos ε hs
  have hφt := scalePhi_pos ε ht
  have hφlt := phi_strictMono ε hst
  have hsbt := sub_ne_zero.mpr hφlt.ne
  have htbs := sub_ne_zero.mpr hφlt.ne'
  unfold scaledDistinct nodeSlope nodeExp
  simp only [scalePhi_zero, sub_zero, mul_zero, Real.exp_zero]
  congr 2
  field_simp [hφs.ne', hφt.ne', hsbt, htbs]
  ring

private theorem tendsto_scaled_left (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun s => scaledSorted ε s t) (𝓝[>] 0) (𝓝 (lowerDiagonal ε t)) := by
  have h₂ : Tendsto (fun s => nodeSlope ε s t) (𝓝[>] 0) (𝓝 (nodeSlope ε 0 t)) := by
    simpa only [nodeSlope_comm ε _ t] using
      (nodeSlope_continuousAt_right (ε := ε) ht.ne').continuousWithinAt
  have h₀ : Tendsto (nodeSlope ε 0) (𝓝[>] 0) (𝓝 (1 + 2 * ε)) := by
    simpa using (tendsto_nodeSlope ε 0).mono_left (nhdsGT_le_nhdsNE 0)
  have hb : Tendsto (fun s => familyPrefactor ε * Real.exp (-(s+t)/3)) (𝓝[>] (0 : ℝ))
      (𝓝 (familyPrefactor ε * Real.exp (-t/3))) := by
    have h : Continuous (fun s : ℝ => familyPrefactor ε * Real.exp (-(s+t)/3)) := by fun_prop
    have hh : Tendsto _ (𝓝[>] (0 : ℝ))
        (𝓝 (familyPrefactor ε * Real.exp (-(0+t)/3))) := h.continuousAt.continuousWithinAt
    simpa only [zero_add] using hh
  have h := (hb.mul ((h₂.sub h₀).div_const (scalePhi ε t))).sub_const 3
  have hvalue : familyPrefactor ε * Real.exp (-t/3) * ((nodeSlope ε 0 t - (1+2*ε)) / scalePhi ε t) - 3 =
      lowerDiagonal ε t := by
    unfold nodeSlope nodeExp lowerDiagonal
    simp only [scalePhi_zero, sub_zero, mul_zero, Real.exp_zero, if_neg ht.ne']
    field_simp [(scalePhi_pos ε ht).ne']
  rw [← hvalue]
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT ht] with s hs
  rw [scaledSorted, if_neg hs.1.ne', if_neg hs.2.ne, scaledDistinct_eq hs.1 hs.2]

private theorem tendsto_scaled_diagonal (ε : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (scaledSorted ε s) (𝓝[>] s) (𝓝 (upperDiagonal ε s)) := by
  have h₂ := (tendsto_nodeSlope ε s).mono_left (nhdsGT_le_nhdsNE s)
  have hφ : Tendsto (scalePhi ε) (𝓝[>] s) (𝓝 (scalePhi ε s)) :=
    (hasDerivAt_scalePhi ε s).continuousAt.continuousWithinAt
  have hb : Tendsto (fun t => familyPrefactor ε * Real.exp (-(s+t)/3)) (𝓝[>] s)
      (𝓝 (familyPrefactor ε * Real.exp (-2*s/3))) := by
    have h : Continuous (fun t : ℝ => familyPrefactor ε * Real.exp (-(s+t)/3)) := by fun_prop
    have hh : Tendsto _ (𝓝[>] s)
        (𝓝 (familyPrefactor ε * Real.exp (-(s+s)/3))) := h.continuousAt.continuousWithinAt
    simpa only [show -(s+s)/3 = -2*s/3 by ring] using hh
  have h := (hb.mul ((h₂.sub_const (nodeSlope ε 0 s)).div hφ (scalePhi_pos ε hs).ne')).sub_const 3
  have hvalue : familyPrefactor ε * Real.exp (-2*s/3) *
      (((1 + 2 * ε) * Real.exp ((1 + ε) * s) - nodeSlope ε 0 s) / scalePhi ε s) - 3 =
      upperDiagonal ε s := by
    unfold nodeSlope nodeExp upperDiagonal
    simp only [scalePhi_zero, sub_zero, mul_zero, Real.exp_zero, if_neg hs.ne']
    field_simp [(scalePhi_pos ε hs).ne']
    ring
  rw [← hvalue]
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [scaledSorted, if_neg hs.ne', if_neg ht.ne, scaledDistinct_eq hs ht]
  rfl

/-- The left boundary of the gauged residual has zero limit. -/
theorem gaugedResidual_tendsto_left {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) :
    Tendsto (fun s => gaugedResidual ε s t) (𝓝[>] 0) (𝓝 0) := by
  have hbound : Tendsto (fun s => Real.exp (-(s+t)/6)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.exp (-t/6))) := by
    have h : Continuous (fun s : ℝ => Real.exp (-(s+t)/6)) := by fun_prop
    have hh : Tendsto _ (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp (-(0+t)/6))) :=
      h.continuousAt.continuousWithinAt
    simpa only [zero_add] using hh
  have hs : Tendsto (fun s => Real.sqrt (lowerDiagonal ε (t-s))) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (lowerDiagonal ε t))) := by
    have hf : ContinuousAt (lowerDiagonal ε) t := (lowerDiagonal_smooth (n := 0) ht).continuousAt
    have hin : ContinuousAt (fun s : ℝ => t-s) 0 := by fun_prop
    have hd : ContinuousAt (lowerDiagonal ε) ((fun s : ℝ => t-s) 0) := by simpa using hf
    have h : ContinuousAt (fun s => Real.sqrt (lowerDiagonal ε (t-s))) 0 :=
      Real.continuous_sqrt.continuousAt.comp (hd.comp hin)
    have hh : Tendsto _ (𝓝[>] (0 : ℝ)) (𝓝 (√(lowerDiagonal ε (t-0)))) := h.continuousWithinAt
    simpa only [sub_zero] using hh
  have h := hbound.mul ((tendsto_scaled_left ε ht).sub (hs.const_mul (Real.sqrt (lowerDiagonal ε t))))
  rw [Real.mul_self_sqrt (lowerDiagonal_pos hε ht).le, sub_self, mul_zero] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT ht] with s hs
  simp [gaugedResidual, residual, min_eq_left hs.2.le, max_eq_right hs.2.le,
    abs_of_pos (sub_pos.mpr hs.2)]

private theorem tendsto_lowerDiagonal_zero (ε : ℝ) (hε : 0 ≤ ε) :
    Tendsto (lowerDiagonal ε) (𝓝[≠] 0) (𝓝 0) := by
  -- This removable singularity uses the normalised second derivative at zero.
  have hφ : HasDerivAt (scalePhi ε) 1 0 := by simpa using hasDerivAt_scalePhi ε 0
  let q (x : ℝ) := Real.exp ((1+2*ε)*x) - 1 - (1+2*ε)*scalePhi ε x
  have hq (x : ℝ) : HasDerivAt q
      ((1+2*ε) * (Real.exp ((1+2*ε)*x) - Real.exp (ε*x))) x := by
    have ha := (((hasDerivAt_id x).const_mul (1+2*ε)).exp).sub_const 1
    have hb := (hasDerivAt_scalePhi ε x).const_mul (1+2*ε)
    convert ha.sub hb using 1; simp only [id_eq]; ring
  have hq₀ : q 0 = 0 := by simp [q, scalePhi_zero]
  have hq'₀ : deriv q 0 = 0 := by rw [(hq 0).deriv]; simp
  have hq'' : HasDerivAt (deriv q) ((1+ε)*(1+2*ε)) 0 := by
    have hd : deriv q = fun x => (1+2*ε) * (Real.exp ((1+2*ε)*x) - Real.exp (ε*x)) :=
      funext fun x => (hq x).deriv
    rw [hd]
    have ha := ((hasDerivAt_id (0 : ℝ)).const_mul (1+2*ε)).exp
    have hb := ((hasDerivAt_id (0 : ℝ)).const_mul ε).exp
    convert (ha.sub hb).const_mul (1+2*ε) using 1; simp; ring
  have hquot : Tendsto (fun x : ℝ => q x / x^2) (𝓝[≠] 0)
      (𝓝 (((1+ε)*(1+2*ε))/2)) := by
    -- L'Hôpital can be applied to the real functions on a punctured neighbourhood.
    have h₁ := hq''.tendsto_slope
    rw [slope_fun_def_field, hq'₀] at h₁
    have h₂ : Tendsto (fun x : ℝ => deriv q x / (2*x)) (𝓝[≠] 0)
        (𝓝 (((1+ε)*(1+2*ε))/2)) := by
      convert h₁.div_const 2 using 1
      funext x
      simp only [sub_zero]
      ring
    refine HasDerivAt.lhopital_zero_nhdsNE (f' := deriv q) (g' := fun x => 2*x) ?_ ?_ ?_ ?_ ?_ h₂
    · filter_upwards with x using (hq x).congr_deriv (hq x).deriv.symm
    · filter_upwards with x
      simpa using (hasDerivAt_id x).pow 2
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero (by norm_num) hx
    · have hh : Tendsto q (𝓝[≠] 0) (𝓝 (q 0)) := (hq 0).continuousAt.continuousWithinAt
      rwa [hq₀] at hh
    · have hc : Continuous (fun x : ℝ => x^2) := by fun_prop
      have hh : Tendsto (fun x : ℝ => x^2) (𝓝[≠] 0) (𝓝 ((0:ℝ)^2)) :=
        hc.continuousAt.continuousWithinAt
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using hh
  have hφq := hφ.tendsto_slope
  rw [slope_fun_def_field, scalePhi_zero] at hφq
  simp only [sub_zero] at hφq
  have h₃ := hquot.div (hφq.pow 2) (by norm_num)
  have hEq : (fun x : ℝ => q x / x^2 / (scalePhi ε x / x)^2) =ᶠ[𝓝[≠] 0]
      fun x => q x / scalePhi ε x^2 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [div_pow, div_div_div_cancel_right₀ (pow_ne_zero 2 hx)]
  have h₃ := h₃.congr' hEq
  have he : Tendsto (fun x : ℝ => familyPrefactor ε * Real.exp (-x/3)) (𝓝[≠] 0)
      (𝓝 (familyPrefactor ε)) := by
    have h : Continuous (fun x : ℝ => familyPrefactor ε * Real.exp (-x/3)) := by fun_prop
    have hh : Tendsto _ (𝓝[≠] (0 : ℝ)) (𝓝 (familyPrefactor ε * Real.exp (-0/3))) :=
      h.continuousAt.continuousWithinAt
    simpa only [neg_zero, zero_div, Real.exp_zero, mul_one] using hh
  -- The only use of the prefactor is exactly the cancellation at x=0.
  have hcancel : familyPrefactor ε * (((1+ε)*(1+2*ε))/2) - 3 = 0 := by
    unfold familyPrefactor
    field_simp (disch := positivity); norm_num
  have h₄ := (he.mul h₃).sub_const 3
  simp only [one_pow, div_one, hcancel] at h₄
  apply h₄.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change x ≠ 0 at hx
  simp [lowerDiagonal, if_neg hx, q, mul_div_assoc]

private theorem lowerDiagonal_continuousAt_zero (ε : ℝ) (hε : 0 ≤ ε) :
    ContinuousAt (lowerDiagonal ε) 0 := by
  rw [continuousAt_iff_punctured_nhds]
  simpa only [show lowerDiagonal ε 0 = 0 by simp [lowerDiagonal]] using tendsto_lowerDiagonal_zero ε hε

private theorem gaugedResidual_tendsto_diagonal {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 < s) :
    Tendsto (gaugedResidual ε s) (𝓝[>] s) (𝓝 (gaugedResidual ε s s)) := by
  let e (t : ℝ) := Real.exp (-(s+t)/6)
  have hEx : Continuous e := by unfold e; fun_prop
  have hD : ContinuousAt (fun t => lowerDiagonal ε (t-s)) s := by
    have h : ContinuousAt (fun t : ℝ => t-s) s := by fun_prop
    have h₀ : ContinuousAt (lowerDiagonal ε) ((fun t : ℝ => t-s) s) :=
      by simpa only [sub_self] using lowerDiagonal_continuousAt_zero ε hε
    exact ContinuousAt.comp (g := lowerDiagonal ε) (f := fun t : ℝ => t-s) h₀ h
  have hS := Real.continuous_sqrt.continuousAt.comp hD
  have hS₀ : Tendsto (fun t => Real.sqrt (lowerDiagonal ε (t-s))) (𝓝[>] s) (𝓝 0) := by
    have hh : Tendsto _ (𝓝[>] s) (𝓝 (√(lowerDiagonal ε (s-s)))) := hS.continuousWithinAt
    simpa only [sub_self, show lowerDiagonal ε 0 = 0 by simp [lowerDiagonal], Real.sqrt_zero] using hh
  have hSt : Tendsto (fun t => Real.sqrt (lowerDiagonal ε t)) (𝓝[>] s)
      (𝓝 (Real.sqrt (lowerDiagonal ε s))) :=
    (Real.continuous_sqrt.continuousAt.comp (lowerDiagonal_smooth (n := 0) hs).continuousAt).continuousWithinAt
  have he : Tendsto e (𝓝[>] s) (𝓝 (e s)) := hEx.continuousAt.continuousWithinAt
  have h := he.mul ((tendsto_scaled_diagonal ε hs).sub (hSt.mul hS₀))
  have hEq : gaugedResidual ε s s = e s * (upperDiagonal ε s - Real.sqrt (lowerDiagonal ε s)*0) := by
    simp [e, gaugedResidual, residual, scaledSorted, lowerDiagonal, hs.ne']
  rw [hEq]
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change s < t at ht
  simp [e, gaugedResidual, residual, min_eq_left ht.le, max_eq_right ht.le,
    abs_of_pos (sub_pos.mpr ht)]

/-- Joint smoothness on the open upper triangle. -/
theorem gaugedResidual_contDiffAt {ε s t : ℝ} (hε : 0 ≤ ε) (hs : 0 < s) (hst : s < t) :
    ContDiffAt ℝ 2 (Function.uncurry (gaugedResidual ε)) (s,t) := by
  have ht := hs.trans hst
  have hst' : 0 < t-s := sub_pos.mpr hst
  have hl := (phi_strictMono ε hst)
  have hsφ := (scalePhi_pos ε hs).ne'
  have htφ := (scalePhi_pos ε ht).ne'
  have hsub := (sub_ne_zero.mpr hl.ne : scalePhi ε s - scalePhi ε t ≠ 0)
  have hsub' := (sub_ne_zero.mpr hl.ne' : scalePhi ε t - scalePhi ε s ≠ 0)
  have hsφt : scalePhi ε s * scalePhi ε t ≠ 0 := mul_ne_zero hsφ htφ
  have hssub : scalePhi ε s * (scalePhi ε s - scalePhi ε t) ≠ 0 := mul_ne_zero hsφ hsub
  have htsub : scalePhi ε t * (scalePhi ε t - scalePhi ε s) ≠ 0 := mul_ne_zero htφ hsub'
  have hP : ContDiff ℝ 2 (scalePhi ε) := phi_smooth ε
  have hD : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.sqrt (lowerDiagonal ε p.2)) (s,t) :=
    ContDiffAt.fun_comp (g := fun x : ℝ => Real.sqrt (lowerDiagonal ε x)) (s,t)
      ((lowerDiagonal_smooth ht).sqrt (lowerDiagonal_pos hε ht).ne')
      (show ContDiffAt ℝ 2 (Prod.snd : ℝ × ℝ → ℝ) (s,t) from contDiffAt_snd)
  have hD' : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.sqrt (lowerDiagonal ε (p.2-p.1))) (s,t) :=
    ContDiffAt.fun_comp (g := fun x : ℝ => Real.sqrt (lowerDiagonal ε x)) (s,t)
      ((lowerDiagonal_smooth hst').sqrt (lowerDiagonal_pos hε hst').ne')
      (show ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.2-p.1) (s,t) by fun_prop)
  let f (p : ℝ × ℝ) := Real.exp (-(p.1+p.2)/6) *
    (scaledDistinct ε p.1 p.2 - Real.sqrt (lowerDiagonal ε p.2) *
      Real.sqrt (lowerDiagonal ε (p.2-p.1)))
  have hf : ContDiffAt ℝ 2 f (s,t) := by unfold f scaledDistinct; fun_prop (disch := assumption)
  apply hf.congr_of_eventuallyEq
  have ha : {p : ℝ × ℝ | 0 < p.1} ∈ 𝓝 (s,t) :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hs
  have hb : {p : ℝ × ℝ | p.1 < p.2} ∈ 𝓝 (s,t) :=
    (isOpen_lt continuous_fst continuous_snd).mem_nhds hst
  filter_upwards [ha, hb] with p hp hq
  change 0 < p.1 at hp
  change p.1 < p.2 at hq
  simp [Function.uncurry, gaugedResidual, residual, min_eq_left hq.le, max_eq_right hq.le,
    scaledSorted, hp.ne', hq.ne, abs_of_pos (sub_pos.mpr hq), f]

/-- Symmetry of the gauged residual. -/
theorem gaugedResidual_symm (ε s t : ℝ) : gaugedResidual ε s t = gaugedResidual ε t s := by
  simp [gaugedResidual, residual, min_comm, max_comm, abs_sub_comm, add_comm]

/-- Continuity up to and including the diagonal along the upper coordinate. -/
theorem gaugedResidual_continuousOn {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 < s) :
    ContinuousOn (gaugedResidual ε s) (Ici s) := by
  intro t ht
  change s ≤ t at ht
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    rw [← show insert s (Ioi s) = Ici s by ext y; simp [le_iff_eq_or_lt]]
    rw [continuousWithinAt_insert_self]
    exact gaugedResidual_tendsto_diagonal hε hs
  · have h' := ((gaugedResidual_contDiffAt hε hs h).comp t
      (show ContDiffAt ℝ 2 (fun y : ℝ => (s,y)) t by fun_prop))
    exact h'.continuousAt.continuousWithinAt

/-- The partial derivative in the upper coordinate and its differentiability
    in the lower coordinate, away from the diagonal. -/
theorem gaugedResidual_partial₂ {ε s t : ℝ} (hε : 0 ≤ ε) (hs : 0 < s) (hst : s < t) :
    HasDerivAt (gaugedResidual ε s) (deriv (gaugedResidual ε s) t) t ∧
      DifferentiableAt ℝ (fun a => deriv (gaugedResidual ε a) t) s := by
  have h := gaugedResidual_contDiffAt hε hs hst
  constructor
  · have h' := h.comp t
      (show ContDiffAt ℝ 2 (fun y : ℝ => (s,y)) t by fun_prop)
    exact (h'.differentiableAt (by norm_num)).hasDerivAt
  · have h' := ContDiffAt.fderiv_succ (m := 1) (g := fun _ : ℝ => t)
      (f := gaugedResidual ε) h contDiffAt_const
    have he := h'.clm_apply (g := fun _ : ℝ => (1 : ℝ)) contDiffAt_const
    simpa only [fderiv_apply_one_eq_deriv] using he.differentiableAt (by norm_num)

end

end RefinedBMV
