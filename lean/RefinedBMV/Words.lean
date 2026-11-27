import RefinedBMV.FiniteKernels

/-! The word average and the exact reindexing by the three cyclic gaps between B's. -/

open scoped BigOperators ComplexOrder
open Matrix

namespace RefinedBMV

noncomputable section

private abbrev Gap3 (n : ℕ) :=
  {p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) //
    (p.1 : ℕ) + (p.2.1 : ℕ) + (p.2.2 : ℕ) = n}

abbrev Gap4 (n : ℕ) :=
  {p : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) //
    (p.1 : ℕ) + (p.2.1 : ℕ) + (p.2.2.1 : ℕ) + (p.2.2.2 : ℕ) = n}

private def Gap3.first {n : ℕ} (p : Gap3 n) : ℕ := p.1.1
private def Gap3.second {n : ℕ} (p : Gap3 n) : ℕ := p.1.2.1
private def Gap3.third {n : ℕ} (p : Gap3 n) : ℕ := p.1.2.2

private theorem Gap3.total {n : ℕ} (p : Gap3 n) : p.first + p.second + p.third = n := p.2

private def rotate {n : ℕ} : Gap3 n ≃ Gap3 n where
  toFun p := ⟨(p.1.2.1, p.1.2.2, p.1.1), by have := p.2; dsimp; omega⟩
  invFun p := ⟨(p.1.2.2, p.1.1, p.1.2.1), by have := p.2; dsimp; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def splitGap (n : ℕ) : Gap4 n ≃ Σ p : Gap3 n, Fin (p.first + 1) where
  toFun q := by
    have h := q.2
    exact ⟨⟨(⟨(q.1.1 : ℕ) + (q.1.2.2.2 : ℕ), by omega⟩, q.1.2.1, q.1.2.2.1), by
      dsimp; omega⟩, ⟨q.1.1, by change (q.1.1 : ℕ) < (q.1.1 : ℕ) + (q.1.2.2.2 : ℕ) + 1; omega⟩⟩
  invFun q := by
    have h := q.1.2
    have hi := q.2.isLt
    change (q.2 : ℕ) < (q.1.1.1 : ℕ) + 1 at hi
    exact ⟨(⟨q.2, by omega⟩, q.1.1.2.1, q.1.1.2.2, ⟨(q.1.1.1 : ℕ) - (q.2 : ℕ), by omega⟩), by
      dsimp; omega⟩
  left_inv q := by
    apply Subtype.ext
    ext <;> first | rfl | (dsimp; omega)
  right_inv q := by
    rcases q with ⟨⟨⟨a, b, c⟩, h⟩, k⟩
    have hk : (k : ℕ) ≤ (a : ℕ) := Nat.lt_succ_iff.mp k.isLt
    have hfst : (⟨(↑k + ((↑a : ℕ) - ↑k)), by omega⟩ : Fin (n + 1)) = a :=
      Fin.ext (by dsimp; omega)
    have fin_heq {m l : ℕ} (hm : m = l) (i : Fin m) (j : Fin l)
        (hij : (i : ℕ) = (j : ℕ)) : HEq i j := by
      subst l
      exact (Fin.ext hij).heq
    refine Sigma.ext ?_ ?_
    · apply Subtype.ext
      exact Prod.ext hfst rfl
    ·
      refine fin_heq ?_ _ _ ?_
      · dsimp [Gap3.first]
        omega
      · rfl

private def enumerateGap (n : ℕ) : Gap3 n ≃ Σ p : Fin (n + 1), Fin (n - (p : ℕ) + 1) where
  toFun p := ⟨p.1.1, ⟨p.1.2.1, by have := p.2; omega⟩⟩
  invFun p := ⟨(p.1, ⟨p.2, by have := p.2.isLt; omega⟩,
    ⟨n - (p.1 : ℕ) - (p.2 : ℕ), by omega⟩), by
    have h₁ := p.1.isLt
    have h₂ := p.2.isLt
    dsimp
    omega⟩
  left_inv p := by
    apply Subtype.ext
    have := p.2
    ext <;> first | rfl | (dsimp; omega)
  right_inv _ := rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def tripleTrace {n : ℕ} (A B : Matrix ι ι ℂ) (p : Gap3 n) : ℂ :=
  trace ((A ^ p.first * B) * (A ^ p.second * B) * (A ^ p.third * B))

private def quadTrace {n : ℕ} (A B : Matrix ι ι ℂ) (p : Gap4 n) : ℂ :=
  trace ((A ^ (p.1.1 : ℕ) * B) * (A ^ (p.1.2.1 : ℕ) * B) *
    (A ^ (p.1.2.2.1 : ℕ) * B) * A ^ (p.1.2.2.2 : ℕ))

/-- The normalized trace of all words with `n` A's and three B's.
    The four gaps of A's split the word at its three B's. -/
def wordAverage (n : ℕ) (A B : Matrix ι ι ℂ) : ℂ :=
  (↑((n + 3).choose 3) : ℂ)⁻¹ * ∑ p : Gap4 n, quadTrace A B p

private lemma trace_rotate {n : ℕ} (A B : Matrix ι ι ℂ) (p : Gap3 n) :
    tripleTrace A B (rotate p) = tripleTrace A B p := by
  change trace ((A ^ p.second * B) * (A ^ p.third * B) * (A ^ p.first * B)) = _
  exact trace_mul_cycle (A ^ p.second * B) (A ^ p.third * B) (A ^ p.first * B)

private lemma merge_trace {n : ℕ} (A B : Matrix ι ι ℂ) (q : Gap4 n) :
    quadTrace A B q = tripleTrace A B (splitGap n q).1 := by
  unfold quadTrace tripleTrace
  change trace ((A ^ (q.1.1 : ℕ) * B) * (A ^ (q.1.2.1 : ℕ) * B) *
    (A ^ (q.1.2.2.1 : ℕ) * B) * A ^ (q.1.2.2.2 : ℕ)) =
      trace ((A ^ ((q.1.1 : ℕ) + (q.1.2.2.2 : ℕ)) * B) * (A ^ (q.1.2.1 : ℕ) * B) *
        (A ^ (q.1.2.2.1 : ℕ) * B))
  rw [trace_mul_comm]
  simp only [← mul_assoc, ← pow_add]
  rw [Nat.add_comm (q.1.2.2.2 : ℕ) (q.1.1 : ℕ)]

private theorem wordAverage_eq (n : ℕ) (A B : Matrix ι ι ℂ) :
    wordAverage n A B = (2 / ((n + 1 : ℂ) * (n + 2 : ℂ))) *
      ∑ p : Gap3 n, tripleTrace A B p := by
  classical
  let T := fun p : Gap3 n => tripleTrace A B p
  have hw : (∑ q : Gap4 n, quadTrace A B q) = ∑ p : Gap3 n, ((p.first : ℂ) + 1) * T p := by
    rw [Fintype.sum_equiv (splitGap n) _ (fun q => T q.1) (merge_trace A B)]
    rw [Fintype.sum_sigma]
    simp [nsmul_eq_mul, Nat.cast_add]
  have rot (f : Gap3 n → ℂ) : (∑ p, f p * T p) = ∑ p, f (rotate p) * T p := by
    refine Fintype.sum_equiv rotate.symm _ _ (fun p => ?_)
    change f p * tripleTrace A B p = f (rotate (rotate.symm p)) * tripleTrace A B (rotate.symm p)
    rw [Equiv.apply_symm_apply]
    have h := trace_rotate A B (rotate.symm p)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
  have h₂ : (∑ p : Gap3 n, ((p.first : ℂ) + 1) * T p) =
      ∑ p : Gap3 n, ((p.second : ℂ) + 1) * T p := rot (fun p => (p.first : ℂ) + 1)
  have h₃ : (∑ p : Gap3 n, ((p.second : ℂ) + 1) * T p) =
      ∑ p : Gap3 n, ((p.third : ℂ) + 1) * T p := rot (fun p => (p.second : ℂ) + 1)
  have hav : 3 * (∑ p : Gap3 n, ((p.first : ℂ) + 1) * T p) =
      (n + 3 : ℂ) * ∑ p : Gap3 n, T p := by
    calc
      _ = (∑ p : Gap3 n, ((p.first : ℂ) + 1) * T p) +
          (∑ p : Gap3 n, ((p.second : ℂ) + 1) * T p) +
          (∑ p : Gap3 n, ((p.third : ℂ) + 1) * T p) := by rw [← h₃, ← h₂]; ring
      _ = _ := by
        simp only [← Finset.sum_add_distrib, Finset.mul_sum, ← add_mul]
        apply Finset.sum_congr rfl
        intro p _
        have hp : (p.first : ℂ) + (p.second : ℂ) + (p.third : ℂ) = n := by
          exact_mod_cast p.total
        linear_combination T p * hp
  have hc₁ : (n + 3 : ℂ) * (↑((n + 2).choose 2) : ℂ) =
      (↑((n + 3).choose 3) : ℂ) * 3 := by
    exact_mod_cast Nat.add_one_mul_choose_eq (n + 2) 2
  have hc₂ : (n + 2 : ℂ) * (n + 1 : ℂ) = (↑((n + 2).choose 2) : ℂ) * 2 := by
    exact_mod_cast (by simpa only [Nat.choose_one_right] using Nat.add_one_mul_choose_eq (n + 1) 1 :
      (n + 2) * (n + 1) = (n + 2).choose 2 * 2)
  have hn : (↑((n + 3).choose 3) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show 3 ≤ n + 3 by omega)
  have hn₁ : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hn₂ : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  rw [wordAverage, hw]
  field_simp [hn, hn₁, hn₂]
  linear_combination (n + 1 : ℂ) * (n + 2 : ℂ) / 3 * hav +
    (∑ p : Gap3 n, T p) * ((n + 3 : ℂ) * hc₂ + 2 * hc₁) / 3

private theorem homogeneous_eq_sum {R : Type*} [Semiring R] (n : ℕ) (a b c : R) :
    homogeneous n a b c = ∑ p : Gap3 n, a ^ p.first * b ^ p.second * c ^ p.third := by
  symm
  rw [Fintype.sum_equiv (enumerateGap n) _
    (fun p => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ) * c ^ (n - (p.1 : ℕ) - (p.2 : ℕ)))]
  · rw [Fintype.sum_sigma]
    unfold homogeneous
    rw [Fin.sum_univ_eq_sum_range (fun p =>
      ∑ q : Fin (n - p + 1), a ^ p * b ^ (q : ℕ) * c ^ (n - p - (q : ℕ)))]
    apply Finset.sum_congr rfl
    intro p _
    exact Fin.sum_univ_eq_sum_range (fun q => a ^ p * b ^ q * c ^ (n - p - q)) _
  · intro p
    change a ^ p.first * b ^ p.second * c ^ p.third =
      a ^ p.first * b ^ p.second * c ^ (n - p.first - p.second)
    have := p.total
    rw [show n - p.first - p.second = p.third by omega]

/-- Cyclic permutation of the variables of the complete homogeneous polynomial. -/
theorem homogeneous_rotate (n : ℕ) (a b c : ℝ) :
    homogeneous n a b c = homogeneous n b c a := by
  rw [homogeneous_eq_sum, homogeneous_eq_sum]
  apply Fintype.sum_equiv rotate
  intro p
  change a ^ p.first * b ^ p.second * c ^ p.third = b ^ p.second * c ^ p.third * a ^ p.first
  ring

/-- Transposition of the first two variables. -/
theorem homogeneous_swap (n : ℕ) (a b c : ℝ) :
    homogeneous n a b c = homogeneous n b a c := by
  let sw : Gap3 n ≃ Gap3 n :=
    { toFun := fun p => ⟨(p.1.2.1, p.1.1, p.1.2.2), by have := p.2; dsimp; omega⟩
      invFun := fun p => ⟨(p.1.2.1, p.1.1, p.1.2.2), by have := p.2; dsimp; omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [homogeneous_eq_sum, homogeneous_eq_sum]
  apply Fintype.sum_equiv sw
  intro p
  change a ^ p.first * b ^ p.second * c ^ p.third = b ^ p.second * a ^ p.first * c ^ p.third
  ring

/-- Homogeneity, including the zero scale. -/
theorem homogeneous_scale (n : ℕ) (a b c t : ℝ) :
    homogeneous n (t * a) (t * b) (t * c) = t ^ n * homogeneous n a b c := by
  rw [homogeneous_eq_sum, homogeneous_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [mul_pow]
  have h : t ^ n = t ^ p.first * t ^ p.second * t ^ p.third := by
    rw [← pow_add, ← pow_add, p.total]
  rw [h]
  ring

def diagReal (a : ι → ℝ) : Matrix ι ι ℂ := diagonal fun i => (a i : ℂ)

theorem diagReal_pow (a : ι → ℝ) (n : ℕ) :
    diagReal a ^ n = diagReal (fun i => a i ^ n) := by
  simp [diagReal, diagonal_pow]

omit [DecidableEq ι] in
private theorem trace_three_mul (P Q R : Matrix ι ι ℂ) :
    trace (P * Q * R) = ∑ i, ∑ j, ∑ k, P i j * Q j k * R k i := by
  simp only [trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

private theorem trace_three_diagonal (a b c : ι → ℝ) (B : Matrix ι ι ℂ) :
    trace ((diagReal a * B) * (diagReal b * B) * (diagReal c * B)) =
      cycleSum (fun i j k => a i * b j * c k) B := by
  rw [trace_three_mul]
  simp only [diagReal, Matrix.diagonal_mul, cycleSum, Complex.ofReal_mul]
  congr! 3
  ring

private theorem trace_diagonal_wordAverage (n : ℕ) (a : ι → ℝ) (B : Matrix ι ι ℂ) :
    wordAverage n (diagReal a) B = cycleSum (fun i j k =>
      2 / ((n + 1 : ℝ) * (n + 2 : ℝ)) * homogeneous n (a i) (a j) (a k)) B := by
  classical
  rw [wordAverage_eq]
  have hfactor : (↑(2 / ((n + 1 : ℝ) * (n + 2 : ℝ))) : ℂ) =
      2 / ((n + 1 : ℂ) * (n + 2 : ℂ)) := by push_cast; rfl
  rw [← hfactor, cycleSum_scale]
  ·
    simp_rw [tripleTrace, diagReal_pow, trace_three_diagonal, cycleSum, homogeneous_eq_sum]
    congr 1
    simp only [Complex.ofReal_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_comm

private theorem weighted_gap_eq (n : ℕ) (x : ι → PosReal) (B : Matrix ι ι ℂ) :
    wordAverage n (diagReal (fun i => (x i).1 ^ 3)) B -
      trace ((diagReal (fun i => (x i).1 ^ n) * B) ^ 3) =
    cycleSum (fun i j k => finiteWeight n (x i).1 (x j).1 (x k).1)
      (diagReal (fun i => Real.sqrt ((x i).1 ^ n)) * B *
        diagReal (fun i => Real.sqrt ((x i).1 ^ n))) := by
  rw [trace_diagonal_wordAverage, pow_succ, pow_succ, pow_one, trace_three_diagonal]
  simp only [cycleSum, ← Finset.sum_sub_distrib, diagReal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  let d (l : ι) : ℂ := Real.sqrt ((x l).1 ^ n)
  have hd (l : ι) : d l ^ 2 = ((x l).1 : ℂ) ^ n := by
    unfold d
    rw [← Complex.ofReal_pow, Real.sq_sqrt (pow_nonneg (x l).2.le _), Complex.ofReal_pow]
  have hi : ((x i).1 : ℂ) ≠ 0 := by exact_mod_cast (x i).2.ne'
  have hj : ((x j).1 : ℂ) ≠ 0 := by exact_mod_cast (x j).2.ne'
  have hk : ((x k).1 : ℂ) ≠ 0 := by exact_mod_cast (x k).2.ne'
  change _ = (↑(finiteWeight n (x i).1 (x j).1 (x k).1) : ℂ) *
    (d i * B i j * d j) * (d j * B j k * d k) * (d k * B k i * d i)
  calc
    _ = (↑(2 / ((n + 1 : ℝ) * (n + 2 : ℝ)) *
          homogeneous n ((x i).1 ^ 3) ((x j).1 ^ 3) ((x k).1 ^ 3)) -
        (((x i).1 : ℂ) ^ n * ((x j).1 : ℂ) ^ n * ((x k).1 : ℂ) ^ n)) *
        B i j * B j k * B k i := by push_cast; ring
    _ = (↑(finiteWeight n (x i).1 (x j).1 (x k).1) : ℂ) *
        (((x i).1 : ℂ) ^ n * ((x j).1 : ℂ) ^ n * ((x k).1 : ℂ) ^ n) *
        B i j * B j k * B k i := by
      simp only [finiteWeight]
      push_cast
      rw [mul_pow, mul_pow]
      simp only [sub_mul, div_mul_cancel₀ _
        (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hi) (pow_ne_zero _ hj)) (pow_ne_zero _ hk)), one_mul]
    _ = _ := by rw [← hd i, ← hd j, ← hd k]; ring

private theorem diagonal_even_word_pos {n : ℕ} (cert : FiniteCertificate n)
    (x : ι → PosReal) (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    trace ((diagReal (fun i => (x i).1) ^ n * B) ^ 3) ≤
      wordAverage n (diagReal (fun i => (x i).1) ^ 3) B := by
  simp only [diagReal_pow]
  rw [← sub_nonneg, weighted_gap_eq]
  apply finite_cycle_nonneg cert x
  let d := diagReal (fun i => Real.sqrt ((x i).1 ^ n))
  have hd : dᴴ = d := by simp [d, diagReal, diagonal_conjTranspose]
  simpa only [hd] using hB.conjTranspose_mul_mul_same d

private theorem wordAverage_conj (n : ℕ) (U : unitary (Matrix ι ι ℂ)) (A B : Matrix ι ι ℂ) :
    wordAverage n (Unitary.conjStarAlgAut ℂ _ U A) (Unitary.conjStarAlgAut ℂ _ U B) =
    wordAverage n A B := by
  unfold wordAverage
  apply congrArg fun z : ℂ => (↑((n + 3).choose 3) : ℂ)⁻¹ * z
  apply Finset.sum_congr rfl
  intro p _
  unfold quadTrace
  simp only [← map_pow, ← map_mul]
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

private theorem diagonal_even_word_nonneg {n : ℕ} (cert : FiniteCertificate n)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    trace ((diagReal x ^ n * B) ^ 3) ≤ wordAverage n (diagReal x ^ 3) B := by
  let D (t : ℝ) := diagReal (fun i => x i + t)
  have hD : Continuous D := Continuous.matrix_diagonal (continuous_pi fun i => by fun_prop)
  have ht : D 0 = diagReal x := by simp [D, diagReal]
  have hW : Continuous fun t : ℝ => wordAverage n (D t ^ 3) B := by
    unfold wordAverage quadTrace
    fun_prop
  have hE : Continuous fun t : ℝ => trace ((D t ^ n * B) ^ 3) := by fun_prop
  rw [← ht]
  apply le_of_tendsto_of_tendsto (hE.continuousAt.continuousWithinAt :
    ContinuousWithinAt _ (Set.Ioi (0 : ℝ)) 0) hW.continuousAt.continuousWithinAt
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact diagonal_even_word_pos cert (fun i => ⟨x i + t, add_pos_of_nonneg_of_pos (hx i) ht⟩) B hB

/-- The manuscript's evenly-spread inequality from a finite certificate.
    `T` is the positive semidefinite cube root of `A`. -/
theorem even_word_of_certificate {n : ℕ} (cert : FiniteCertificate n)
    (T B : Matrix ι ι ℂ) (hT : T.PosSemidef) (hB : B.PosSemidef) :
    trace ((T ^ n * B) ^ 3) ≤ wordAverage n (T ^ 3) B := by
  let U := hT.1.eigenvectorUnitary
  let D := diagReal hT.1.eigenvalues
  let C := (Unitary.conjStarAlgAut ℂ _ U).symm B
  have hTC : Unitary.conjStarAlgAut ℂ _ U D = T := hT.1.spectral_theorem.symm
  have hBC : Unitary.conjStarAlgAut ℂ _ U C = B := StarAlgEquiv.apply_symm_apply _ _
  have hC : C.PosSemidef := by
    simpa only [C, Unitary.conjStarAlgAut_symm_apply, Matrix.star_eq_conjTranspose, mul_assoc] using
      hB.conjTranspose_mul_mul_same (U : Matrix ι ι ℂ)
  have htrace (P : Matrix ι ι ℂ) : trace (Unitary.conjStarAlgAut ℂ _ U P) = trace P := by
    rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
  rw [← hTC, ← hBC]
  simp only [← map_pow, ← map_mul, htrace, wordAverage_conj]
  exact diagonal_even_word_nonneg cert _ hT.eigenvalues_nonneg C hC

/-- Spectral power of a Hermitian matrix. The exponent used in `(Eₙ,₃)` is `n/3`. -/
def spectralPower (A : Matrix ι ι ℂ) (r : ℝ) : Matrix ι ι ℂ :=
  cfc (fun x : ℝ => x ^ r) A

/-- `(Eₙ,₃)` for arbitrary complex Hermitian positive semidefinite `A` and `B`,
    including singular matrices, whenever the exact scalar certificate is supplied. -/
theorem even_word_of_certificate_matrix {n : ℕ} (cert : FiniteCertificate n)
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace ((spectralPower A (n / 3) * B) ^ 3) ≤ wordAverage n A B := by
  let U := hA.1.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ _ U
  let x (i : ι) := hA.1.eigenvalues i ^ (1 / 3 : ℝ)
  let D := diagReal x
  let T := f D
  have hD : D.PosSemidef := Matrix.PosSemidef.diagonal (fun i =>
    Complex.zero_le_real.mpr (Real.rpow_nonneg (hA.eigenvalues_nonneg i) _))
  have hT : T.PosSemidef := by
    simpa only [T, f, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hD.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ)
  have cube (i : ι) : x i ^ (3 : ℕ) = hA.1.eigenvalues i := by
    simpa [x, one_div] using
      Real.rpow_inv_natCast_pow (hA.eigenvalues_nonneg i) (by decide : (3 : ℕ) ≠ 0)
  have hcube : T ^ 3 = A := by
    simp only [T, ← map_pow, D, diagReal_pow, cube]
    exact hA.1.spectral_theorem.symm
  have hpow : T ^ n = spectralPower A (n / 3) := by
    unfold spectralPower
    rw [hA.1.cfc_eq]
    unfold Matrix.IsHermitian.cfc
    rw [show T ^ n = f (D ^ n) from (map_pow f D n).symm]
    change f (diagReal x ^ n) = f (diagReal fun i => hA.1.eigenvalues i ^ (n / 3 : ℝ))
    rw [diagReal_pow]
    apply congrArg f
    apply congrArg diagReal
    funext i
    dsimp [x]
    rw [← Real.rpow_mul_natCast (hA.eigenvalues_nonneg i)]
    rw [show (1 / 3 : ℝ) * (n : ℝ) = (n : ℝ) / 3 by ring]
  simpa only [hcube, hpow] using even_word_of_certificate cert T B hT hB

end

end RefinedBMV
