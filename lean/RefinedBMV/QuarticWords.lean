import RefinedBMV.Words
import RefinedBMV.QuarticKernel

/-! Exact word counting and the antipodal four-cycle trace argument. -/

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace RefinedBMV

noncomputable section

private def q₁ {n : ℕ} (p : Gap4 n) : ℕ := p.1.1
private def q₂ {n : ℕ} (p : Gap4 n) : ℕ := p.1.2.1
private def q₃ {n : ℕ} (p : Gap4 n) : ℕ := p.1.2.2.1
private def q₄ {n : ℕ} (p : Gap4 n) : ℕ := p.1.2.2.2

private def rotate4 {n : ℕ} : Gap4 n ≃ Gap4 n where
  toFun p := ⟨(p.1.2.1, p.1.2.2.1, p.1.2.2.2, p.1.1), by have := p.2; dsimp; omega⟩
  invFun p := ⟨(p.1.2.2.2, p.1.1, p.1.2.1, p.1.2.2.1), by have := p.2; dsimp; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

def enumerate4 (n : ℕ) : Gap4 n ≃
    Σ a : Fin (n + 1), Σ b : Fin (n - (a : ℕ) + 1), Fin (n - (a : ℕ) - (b : ℕ) + 1) where
  toFun p := ⟨p.1.1, ⟨⟨p.1.2.1, by have := p.2; omega⟩,
    ⟨p.1.2.2.1, by have := p.2; dsimp; omega⟩⟩⟩
  invFun p := by
    have h₁ := p.1.isLt
    have h₂ := p.2.1.isLt
    have h₃ := p.2.2.isLt
    exact ⟨(p.1, ⟨p.2.1, by omega⟩, ⟨p.2.2, by omega⟩,
      ⟨n - (p.1 : ℕ) - (p.2.1 : ℕ) - (p.2.2 : ℕ), by omega⟩), by dsimp; omega⟩
  left_inv p := by
    apply Subtype.ext
    have := p.2
    ext <;> first | rfl | (dsimp; omega)
  right_inv _ := rfl

private theorem homogeneousFour_eq (n : ℕ) (a b c d : ℝ) :
    homogeneousFour n a b c d = ∑ p : Gap4 n, a ^ q₁ p * b ^ q₂ p * c ^ q₃ p * d ^ q₄ p := by
  symm
  rw [Fintype.sum_equiv (enumerate4 n) _ (fun p => a ^ (p.1 : ℕ) * b ^ (p.2.1 : ℕ) *
    c ^ (p.2.2 : ℕ) * d ^ (n - (p.1 : ℕ) - (p.2.1 : ℕ) - (p.2.2 : ℕ)))]
  · rw [Fintype.sum_sigma]
    simp_rw [Fintype.sum_sigma]
    unfold homogeneousFour homogeneous
    simp only [mul_sum, mul_assoc]
    rw [Fin.sum_univ_eq_sum_range (fun p => ∑ q : Fin (n - p + 1),
      ∑ r : Fin (n - p - (q : ℕ) + 1), a ^ p *
        (b ^ (q : ℕ) * (c ^ (r : ℕ) * d ^ (n - p - (q : ℕ) - (r : ℕ)))))]
    apply sum_congr rfl
    intro p _
    rw [Fin.sum_univ_eq_sum_range (fun q => ∑ r : Fin (n - p - q + 1),
      a ^ p * (b ^ q * (c ^ (r : ℕ) * d ^ (n - p - q - (r : ℕ)))))]
    apply sum_congr rfl
    intro q _
    exact Fin.sum_univ_eq_sum_range (fun r => a ^ p * (b ^ q * (c ^ r * d ^ (n - p - q - r)))) _
  · intro p
    change a ^ q₁ p * b ^ q₂ p * c ^ q₃ p * d ^ q₄ p =
      a ^ q₁ p * b ^ q₂ p * c ^ q₃ p * d ^ (n - q₁ p - q₂ p - q₃ p)
    have h : q₁ p + q₂ p + q₃ p + q₄ p = n := p.2
    rw [show n - q₁ p - q₂ p - q₃ p = q₄ p by omega]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def fourTrace {n : ℕ} (A B : Matrix ι ι ℂ) (p : Gap4 n) : ℂ :=
  trace ((A ^ q₁ p * B) * (A ^ q₂ p * B) * (A ^ q₃ p * B) * (A ^ q₄ p * B))

private def fiveGapTrace {n : ℕ} (A B : Matrix ι ι ℂ) (p : Gap4 n) (k : ℕ) : ℂ :=
  trace ((A ^ k * B) * (A ^ q₂ p * B) * (A ^ q₃ p * B) *
    (A ^ q₄ p * B) * A ^ (q₁ p - k))

/-- The average of the words containing `n` A's and four B's. The first and
    last A-gaps have a combined size of `q₁ p`, with all splits counted. -/
def quarticWordAverage (n : ℕ) (A B : Matrix ι ι ℂ) : ℂ :=
  (↑((n + 4).choose 4) : ℂ)⁻¹ * ∑ p : Gap4 n, ∑ k : Fin (q₁ p + 1), fiveGapTrace A B p k

private theorem fiveGapTrace_merge {n : ℕ} (A B : Matrix ι ι ℂ) (p : Gap4 n) (k : Fin (q₁ p + 1)) :
    fiveGapTrace A B p k = fourTrace A B p := by
  unfold fiveGapTrace fourTrace
  rw [trace_mul_comm]
  simp only [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp k.isLt)]

private theorem rotate4_trace {n : ℕ} (A B : Matrix ι ι ℂ) (p : Gap4 n) :
    fourTrace A B (rotate4 p) = fourTrace A B p := by
  unfold fourTrace
  rw [trace_mul_comm]
  simp only [← mul_assoc]
  rfl

private theorem quarticWordAverage_eq (n : ℕ) (A B : Matrix ι ι ℂ) :
    quarticWordAverage n A B = (↑((n + 3).choose 3) : ℂ)⁻¹ * ∑ p : Gap4 n, fourTrace A B p := by
  classical
  let T := fun p : Gap4 n => fourTrace A B p
  have rot (f : Gap4 n → ℂ) : (∑ p, f p * T p) = ∑ p, f (rotate4 p) * T p := by
    refine Fintype.sum_equiv rotate4.symm _ _ (fun p => ?_)
    change f p * fourTrace A B p = f (rotate4 (rotate4.symm p)) * fourTrace A B (rotate4.symm p)
    rw [Equiv.apply_symm_apply]
    have h := rotate4_trace A B (rotate4.symm p)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
  have h₂ := rot (fun p => (q₁ p : ℂ) + 1)
  have h₃ := rot (fun p => (q₂ p : ℂ) + 1)
  have h₄ := rot (fun p => (q₃ p : ℂ) + 1)
  change (∑ p, ((q₁ p : ℂ) + 1) * T p) = ∑ p, ((q₂ p : ℂ) + 1) * T p at h₂
  change (∑ p, ((q₂ p : ℂ) + 1) * T p) = ∑ p, ((q₃ p : ℂ) + 1) * T p at h₃
  change (∑ p, ((q₃ p : ℂ) + 1) * T p) = ∑ p, ((q₄ p : ℂ) + 1) * T p at h₄
  have hav : 4 * (∑ p : Gap4 n, ((q₁ p : ℂ) + 1) * T p) =
      (n + 4 : ℂ) * ∑ p : Gap4 n, T p := by
    calc
      _ = (∑ p, ((q₁ p : ℂ) + 1) * T p) + (∑ p, ((q₂ p : ℂ) + 1) * T p) +
          (∑ p, ((q₃ p : ℂ) + 1) * T p) + (∑ p, ((q₄ p : ℂ) + 1) * T p) := by
        rw [← h₄, ← h₃, ← h₂]
        ring
      _ = _ := by
        simp only [← sum_add_distrib, mul_sum, ← add_mul]
        apply sum_congr rfl
        intro p _
        have hp : (q₁ p : ℂ) + (q₂ p : ℂ) + (q₃ p : ℂ) + (q₄ p : ℂ) = n := by
          exact_mod_cast (p.2 : q₁ p + q₂ p + q₃ p + q₄ p = n)
        linear_combination T p * hp
  have hc : (n + 4 : ℂ) * (↑((n + 3).choose 3) : ℂ) = (↑((n + 4).choose 4) : ℂ) * 4 := by
    exact_mod_cast Nat.add_one_mul_choose_eq (n + 3) 3
  have hc₃ : (↑((n + 3).choose 3) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show 3 ≤ n + 3 by omega)
  have hc₄ : (↑((n + 4).choose 4) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show 4 ≤ n + 4 by omega)
  unfold quarticWordAverage
  simp_rw [fiveGapTrace_merge]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hc₃, hc₄]
  linear_combination ((↑((n + 3).choose 3) : ℂ) * hav + (∑ p : Gap4 n, T p) * hc) / 4

/-- A weighted four-cycle sum. -/
def fourCycleSum (W : ι → ι → ι → ι → ℝ) (X : Matrix ι ι ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, (W i j k l : ℂ) * X i j * X j k * X k l * X l i

omit [DecidableEq ι] in
private theorem trace_four_mul (P Q R S : Matrix ι ι ℂ) :
    trace (P * Q * R * S) = ∑ i, ∑ j, ∑ k, ∑ l, P i j * Q j k * R k l * S l i := by
  simp only [trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  apply sum_congr rfl
  intro i _
  calc
    _ = ∑ l, ∑ j, ∑ k, P i j * Q j k * R k l * S l i :=
      sum_congr rfl fun l _ => sum_comm
    _ = ∑ j, ∑ l, ∑ k, P i j * Q j k * R k l * S l i := sum_comm
    _ = _ := sum_congr rfl fun j _ => sum_comm

private theorem trace_four_diagonal (a b c d : ι → ℝ) (B : Matrix ι ι ℂ) :
    trace ((diagReal a * B) * (diagReal b * B) * (diagReal c * B) * (diagReal d * B)) =
      fourCycleSum (fun i j k l => a i * b j * c k * d l) B := by
  rw [trace_four_mul]
  simp only [diagReal, Matrix.diagonal_mul, fourCycleSum, Complex.ofReal_mul]
  congr! 4
  ring

private theorem quarticWordAverage_diagonal (n : ℕ) (a : ι → ℝ) (B : Matrix ι ι ℂ)
    (C : ℝ) (hc : C = ↑((n + 3).choose 3)) :
    quarticWordAverage n (diagReal a) B =
      fourCycleSum (fun i j k l => C⁻¹ * homogeneousFour n (a i) (a j) (a k) (a l)) B := by
  rw [quarticWordAverage_eq, hc]
  simp_rw [fourTrace, diagReal_pow, trace_four_diagonal, homogeneousFour_eq, fourCycleSum]
  push_cast
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  rw [sum_comm]
  congr! 2
  ring

omit [DecidableEq ι] in
private theorem fourCycle_rotate (W : ι → ι → ι → ι → ℝ) (X : Matrix ι ι ℂ) :
    fourCycleSum (fun i j k l => W j k l i) X = fourCycleSum W X := by
  unfold fourCycleSum
  calc
    _ = ∑ j, ∑ i, ∑ k, ∑ l, (W j k l i : ℂ) * X i j * X j k * X k l * X l i := sum_comm
    _ = ∑ j, ∑ k, ∑ i, ∑ l, (W j k l i : ℂ) * X i j * X j k * X k l * X l i :=
      sum_congr rfl fun j _ => sum_comm
    _ = ∑ j, ∑ k, ∑ l, ∑ i, (W j k l i : ℂ) * X i j * X j k * X k l * X l i :=
      sum_congr rfl fun j _ => sum_congr rfl fun k _ => sum_comm
    _ = _ := by congr! 4; ring

omit [DecidableEq ι] in
/-- Pairing the two half-paths gives a PSD quadratic form for every Hermitian `X`. -/
theorem four_cycle_nonneg_of_cyclic (W K : ι → ι → ι → ι → ℝ)
    (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (hK : ∀ i k, (Matrix.of fun j l => (K i j k l : ℂ)).PosSemidef)
    (hcyc : ∀ i j k l, K i j k l + K j k l i = 2 * W i j k l) :
    0 ≤ fourCycleSum W X := by
  classical
  have hrotate := fourCycle_rotate K X
  have heq : fourCycleSum (fun i j k l => K i j k l + K j k l i) X =
      fourCycleSum (fun i j k l => 2 * W i j k l) X := by
    exact congrArg (fun V => fourCycleSum V X)
      (funext fun i => funext fun j => funext fun k => funext fun l => hcyc i j k l)
  simp only [fourCycleSum, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
    add_mul, sum_add_distrib] at heq
  have hscale : (∑ i, ∑ j, ∑ k, ∑ l, (2 * (W i j k l : ℂ)) * X i j * X j k * X k l * X l i) =
      2 * fourCycleSum W X := by
    simp [fourCycleSum, mul_sum, mul_assoc]
  change fourCycleSum K X + fourCycleSum (fun i j k l => K j k l i) X = _ at heq
  rw [hrotate, hscale] at heq
  have hab : fourCycleSum W X = fourCycleSum K X := by linear_combination -heq / 2
  rw [hab]
  unfold fourCycleSum
  apply sum_nonneg
  intro i _
  rw [sum_comm]
  apply sum_nonneg
  intro k _
  let v (j : ι) := X k j * X j i
  have hstar (a b : ι) : star (X b a) = X a b := congrFun (congrFun hX.eq a) b
  simpa [v, dotProduct, mulVec, Finset.mul_sum, StarMul.star_mul, hstar, mul_assoc, mul_comm, mul_left_comm]
    using (hK i k).dotProduct_mulVec_nonneg v

private def quarticWeight (n p q : ℕ) (a b c d : ℝ) : ℝ :=
  (↑((n + 3).choose 3) : ℝ)⁻¹ * homogeneousFour n (a^p) (b^p) (c^p) (d^p) / (a*b*c*d)^q - 1

private def normalizedQuartic {n p q : ℕ} (cert : QuarticCertificate n p q) (a b c d : ℝ) : ℝ :=
  cert.kernel a c b d / ((↑((n + 3).choose 3) : ℝ) * (a*b*c*d)^q)

private theorem positive_normalizedQuartic {n p q : ℕ} (cert : QuarticCertificate n p q)
    (a c : PosReal) :
    PositiveKernel (fun b d : PosReal => normalizedQuartic cert a.1 b.1 c.1 d.1) := by
  have hc : 0 < (↑((n + 3).choose 3) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 3 ≤ n + 3 by omega)
  have hscale : 0 ≤ (1 / ((↑((n + 3).choose 3) : ℝ) * (a.1 * c.1) ^ q)) := by
    have := a.2
    have := c.2
    positivity
  have h := (((cert.positive _ _ a.2 c.2).pullback (Subtype.val : PosReal → ℝ)).mul
    (PositiveKernel.rankOne (fun b : PosReal => 1 / b.1 ^ q))).scale hscale
  convert h using 1
  ext b d
  unfold normalizedQuartic
  have ha := a.2
  have hb := b.2
  have hc' := c.2
  have hd := d.2
  field_simp (disch := positivity)
  ring

private theorem normalizedQuartic_cyclic {n p q : ℕ} (cert : QuarticCertificate n p q)
    (a b c d : PosReal) :
    normalizedQuartic cert a.1 b.1 c.1 d.1 + normalizedQuartic cert b.1 c.1 d.1 a.1 =
      2 * quarticWeight n p q a.1 b.1 c.1 d.1 := by
  have hc : 0 < (↑((n + 3).choose 3) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 3 ≤ n + 3 by omega)
  have ha := a.2
  have hb := b.2
  have hc' := c.2
  have hd := d.2
  unfold normalizedQuartic quarticWeight
  have hsymm : cert.kernel b.1 d.1 c.1 a.1 = cert.kernel b.1 d.1 a.1 c.1 := by
    let args : Bool → ℝ := fun i => if i then a.1 else c.1
    have hM := (cert.positive b.1 d.1 b.2 d.2 Bool args).isHermitian
    have h : star (↑(cert.kernel b.1 d.1 a.1 c.1) : ℂ) = ↑(cert.kernel b.1 d.1 c.1 a.1) :=
      congrFun (congrFun hM.eq false) true
    simpa [Complex.star_def] using (congrArg Complex.re h).symm
  rw [show b.1*c.1*d.1*a.1 = a.1*b.1*c.1*d.1 by ring, hsymm, ← add_div, cert.cyclic]
  field_simp (disch := positivity)

private theorem quartic_gap_eq (n p q : ℕ) (x : ι → PosReal) (B : Matrix ι ι ℂ) :
    quarticWordAverage n (diagReal (fun i => (x i).1 ^ p)) B -
      trace ((diagReal (fun i => (x i).1 ^ q) * B) ^ 4) =
    fourCycleSum (fun i j k l => quarticWeight n p q (x i).1 (x j).1 (x k).1 (x l).1)
      (diagReal (fun i => Real.sqrt ((x i).1 ^ q)) * B *
        diagReal (fun i => Real.sqrt ((x i).1 ^ q))) := by
  rw [quarticWordAverage_diagonal n _ B _ rfl, pow_succ _ 3, pow_succ _ 2,
    pow_succ _ 1, pow_one, trace_four_diagonal]
  simp only [fourCycleSum, ← sum_sub_distrib, diagReal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro l _
  let t (l : ι) : ℂ := Real.sqrt ((x l).1 ^ q)
  have ht (l : ι) : t l ^ 2 = ((x l).1 : ℂ) ^ q := by
    unfold t
    rw [← Complex.ofReal_pow, Real.sq_sqrt (pow_nonneg (x l).2.le _), Complex.ofReal_pow]
  let v : ℂ := (((x i).1 : ℂ) * ((x j).1 : ℂ) * ((x k).1 : ℂ) * ((x l).1 : ℂ)) ^ q
  have prod_eq : (↑((x i).1 ^ q * (x j).1 ^ q * (x k).1 ^ q * (x l).1 ^ q) : ℂ) = v := by
    simp [v, mul_pow]
  have hne (r : ι) : ((x r).1 : ℂ) ≠ 0 := by exact_mod_cast (x r).2.ne'
  have hv : v ≠ 0 := by simp [v, hne]
  let M : ℂ := ↑((↑((n + 3).choose 3) : ℝ)⁻¹ *
    homogeneousFour n ((x i).1 ^ p) ((x j).1 ^ p) ((x k).1 ^ p) ((x l).1 ^ p))
  change _ = (↑(quarticWeight n p q (x i).1 (x j).1 (x k).1 (x l).1) : ℂ) *
    (t i * B i j * t j) * (t j * B j k * t k) * (t k * B k l * t l) * (t l * B l i * t i)
  have hw : (↑(quarticWeight n p q (x i).1 (x j).1 (x k).1 (x l).1) : ℂ) = M / v - 1 := by
    unfold quarticWeight M v
    push_cast
    rfl
  rw [prod_eq, hw]
  calc
    _ = (M - v) * B i j * B j k * B k l * B l i := by unfold M; ring
    _ = (M / v - 1) * v * B i j * B j k * B k l * B l i := by
      simp only [sub_mul, div_mul_cancel₀ _ hv, one_mul]
    _ = _ := by unfold v; simp only [mul_pow, ← ht]; ring

private theorem diagonal_quartic_positive {n p q : ℕ} (cert : QuarticCertificate n p q)
    (x : ι → PosReal) (B : Matrix ι ι ℂ) (hB : B.IsHermitian) :
    trace ((diagReal (fun i => (x i).1) ^ q * B) ^ 4) ≤
      quarticWordAverage n (diagReal (fun i => (x i).1) ^ p) B := by
  simp only [diagReal_pow]
  rw [← sub_nonneg, quartic_gap_eq]
  let D := diagReal (fun i => Real.sqrt ((x i).1 ^ q))
  have hD : Dᴴ = D := by simp [D, diagReal, diagonal_conjTranspose]
  have hX : (D * B * D).IsHermitian := by
    simpa only [hD] using isHermitian_conjTranspose_mul_mul D hB
  exact four_cycle_nonneg_of_cyclic _ _ _ hX
    (fun i k => positive_normalizedQuartic cert (x i) (x k) ι x)
    (fun i j k l => normalizedQuartic_cyclic cert (x i) (x j) (x k) (x l))

private theorem diagonal_quartic_nonneg {n p q : ℕ} (cert : QuarticCertificate n p q)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (B : Matrix ι ι ℂ) (hB : B.IsHermitian) :
    trace ((diagReal x ^ q * B) ^ 4) ≤ quarticWordAverage n (diagReal x ^ p) B := by
  let D (t : ℝ) := diagReal (fun i => x i + t)
  have hD : Continuous D := Continuous.matrix_diagonal (continuous_pi fun i => by fun_prop)
  have ht : D 0 = diagReal x := by simp [D, diagReal]
  have hW : Continuous fun t : ℝ => quarticWordAverage n (D t ^ p) B := by
    unfold quarticWordAverage fiveGapTrace
    fun_prop
  have hE : Continuous fun t : ℝ => trace ((D t ^ q * B) ^ 4) := by fun_prop
  rw [← ht]
  apply le_of_tendsto_of_tendsto (hE.continuousAt.continuousWithinAt :
    ContinuousWithinAt _ (Set.Ioi (0 : ℝ)) 0) hW.continuousAt.continuousWithinAt
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact diagonal_quartic_positive cert (fun i => ⟨x i + t, add_pos_of_nonneg_of_pos (hx i) ht⟩) B hB

private theorem quarticAverage_conj (n : ℕ) (U : unitary (Matrix ι ι ℂ)) (A B : Matrix ι ι ℂ) :
    quarticWordAverage n (Unitary.conjStarAlgAut ℂ _ U A) (Unitary.conjStarAlgAut ℂ _ U B) =
      quarticWordAverage n A B := by
  unfold quarticWordAverage
  apply congrArg fun z : ℂ => (↑((n + 4).choose 4) : ℂ)⁻¹ * z
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro k _
  unfold fiveGapTrace
  simp only [← map_pow, ← map_mul]
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

/-- A quartic certificate proves `(Eₙ,₄)` for positive semidefinite `A` and
    arbitrary Hermitian `B`, in every finite dimension. -/
theorem quartic_word_of_certificate {n p q : ℕ} (cert : QuarticCertificate n p q)
    (hp : p ≠ 0) (hpq : p * n = 4 * q) (A B : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.IsHermitian) :
    trace ((spectralPower A (n / 4) * B) ^ 4) ≤ quarticWordAverage n A B := by
  let U := hA.1.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ _ U
  let x (i : ι) := hA.1.eigenvalues i ^ ((p : ℝ)⁻¹)
  let D := diagReal x
  let C := f.symm B
  have hBC : f C = B := StarAlgEquiv.apply_symm_apply _ _
  have hC : C.IsHermitian := by
    simpa only [C, f, Unitary.conjStarAlgAut_symm_apply, Matrix.star_eq_conjTranspose] using
      isHermitian_conjTranspose_mul_mul (U : Matrix ι ι ℂ) hB
  have hx (i : ι) : 0 ≤ x i := Real.rpow_nonneg (hA.eigenvalues_nonneg i) _
  have hxpow (i : ι) : x i ^ p = hA.1.eigenvalues i := Real.rpow_inv_natCast_pow (hA.eigenvalues_nonneg i) hp
  have hAeq : f (D ^ p) = A := by
    simp only [D, diagReal_pow, hxpow]
    exact hA.1.spectral_theorem.symm
  have hcoef : ((p : ℝ)⁻¹) * q = (n / 4 : ℝ) := by
    have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
    have h : (p : ℝ) * n = 4 * q := by exact_mod_cast hpq
    field_simp [hp']
    linarith
  have hpow : f (D ^ q) = spectralPower A (n / 4) := by
    unfold spectralPower
    rw [hA.1.cfc_eq]
    unfold Matrix.IsHermitian.cfc
    change f (diagReal x ^ q) = f (diagReal fun i => hA.1.eigenvalues i ^ (n / 4 : ℝ))
    rw [diagReal_pow]
    apply congrArg f
    apply congrArg diagReal
    funext i
    dsimp [x]
    rw [← Real.rpow_mul_natCast (hA.eigenvalues_nonneg i), hcoef]
  have htrace (P : Matrix ι ι ℂ) : trace (f P) = trace P := by
    unfold f
    rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
  rw [← hpow, ← hAeq, ← hBC]
  simp only [← map_pow, ← map_mul, htrace]
  rw [show quarticWordAverage n (f (D ^ p)) (f C) = quarticWordAverage n (D ^ p) C from
    quarticAverage_conj n U (D ^ p) C]
  exact diagonal_quartic_nonneg cert _ hx C hC

end

end RefinedBMV
