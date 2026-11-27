import RefinedBMV.QuarticWords
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The third derivative of the finite matrix polynomial is the normalized
cubic word trace multiplied by the falling factorial. -/

open Matrix Polynomial Finset

namespace RefinedBMV

noncomputable section

private def gapCoefficient {R : Type*} [Semiring R] (A B : R) : ℕ → ℕ → R
  | 0, n => A ^ n
  | k + 1, n => ∑ i ∈ range (n + 1), A ^ i * B * gapCoefficient A B k (n - i)

private theorem gapCoefficient_succ {R : Type*} [Semiring R] (A B : R) (k n : ℕ) :
    gapCoefficient A B (k + 1) (n + 1) =
      A * gapCoefficient A B (k + 1) n + B * gapCoefficient A B k (n + 1) := by
  rw [gapCoefficient, sum_range_succ', gapCoefficient, mul_sum]
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.succ_sub_succ_eq_sub, pow_succ', mul_assoc]

private theorem gapCoefficient_zero {R : Type*} [Semiring R] (A B : R) (k : ℕ) :
    gapCoefficient A B k 0 = B ^ k := by
  induction k with
  | zero => simp [gapCoefficient]
  | succ k ih => simp [gapCoefficient, ih, pow_succ']

private theorem natDegree_affine_le {R : Type*} [Semiring R] (A B : R) :
    (C A + C B * X : R[X]).natDegree ≤ 1 := by
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simp
  · exact (natDegree_C_mul_le _ _).trans (natDegree_le_of_degree_le (by simpa using (degree_X_le (R := R))))

private theorem affine_coeff {R : Type*} [Semiring R] (A B : R) (k n : ℕ) :
    ((C A + C B * X) ^ (n+k) : R[X]).coeff k = gapCoefficient A B k n := by
  let p : R[X] := C A + C B * X
  have hp : p.natDegree ≤ 1 := natDegree_affine_le A B
  change (p ^ (n+k)).coeff k = _
  induction k generalizing n with
  | zero =>
    rw [Nat.add_zero, gapCoefficient]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', show p = C A + C B * X from rfl, add_mul]
      simp only [coeff_add, coeff_C_mul, mul_assoc, coeff_X_mul_zero, mul_zero, add_zero]
      rw [pow_succ']
      exact congrArg (A * ·) ih
  | succ k ih =>
    induction n with
    | zero =>
      rw [Nat.zero_add, gapCoefficient_zero]
      have he := coeff_pow_of_natDegree_le (m := k+1) hp
      simp [p] at he
      exact he
    | succ n ihn =>
      have he : n + 1 + (k + 1) = n + (k + 1) + 1 := by omega
      rw [he, pow_succ', show p = C A + C B * X from rfl, add_mul]
      simp only [coeff_add, coeff_C_mul, mul_assoc, coeff_X_mul]
      rw [show ((C A + C B * X) ^ (n+(k+1)) : R[X]).coeff (k+1) =
          gapCoefficient A B (k+1) n from ihn]
      rw [show n+(k+1) = n+1+k by omega, show ((C A + C B * X) ^ (n+1+k) : R[X]).coeff k =
        gapCoefficient A B k (n+1) from ih (n+1)]
      exact (gapCoefficient_succ A B k n).symm

variable {d : ℕ}

local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

private theorem trace_gapCoefficient (n : ℕ) (A B : Mat) :
    trace (gapCoefficient A B 3 n) = ((↑((n+3).choose 3) : ℂ)) * wordAverage n A B := by
  classical
  unfold wordAverage
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (Nat.choose_pos (by omega : 3 ≤ n+3)).ne'), one_mul]
  change trace (gapCoefficient A B 3 n) =
    ∑ p : Gap4 n, trace ((A ^ (p.1.1 : ℕ)*B)*(A ^ (p.1.2.1 : ℕ)*B)*
      (A ^ (p.1.2.2.1 : ℕ)*B)*A ^ (p.1.2.2.2 : ℕ))
  let T (a b c : ℕ) : ℂ := trace ((A^a*B)*((A^b*B)*((A^c*B)*A^(n-a-b-c))))
  let f (p : Σ a : Fin (n+1), Σ b : Fin (n-(a:ℕ)+1), Fin (n-(a:ℕ)-(b:ℕ)+1)) : ℂ :=
    T p.1 p.2.1 p.2.2
  rw [Fintype.sum_equiv (enumerate4 n) _ f]
  · simp only [Fintype.sum_sigma, f, gapCoefficient, mul_sum, trace_sum]
    change (∑ a ∈ range (n+1), ∑ b ∈ range (n-a+1), ∑ c ∈ range (n-a-b+1), T a b c) =
      ∑ a : Fin (n+1), ∑ b : Fin (n-(a:ℕ)+1), ∑ c : Fin (n-(a:ℕ)-(b:ℕ)+1), T a b c
    rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin (n-a+1), ∑ c : Fin (n-a-(b:ℕ)+1),
      T a b c) (n+1)]
    apply sum_congr rfl
    intro a _
    rw [Fin.sum_univ_eq_sum_range (fun b => ∑ c : Fin (n-a-b+1),
      T a b c) (n-a+1)]
    apply sum_congr rfl
    intro b _
    exact (Fin.sum_univ_eq_sum_range (T a b) (n-a-b+1)).symm
  · intro p
    have he : n - (p.1.1 : ℕ) - (p.1.2.1 : ℕ) - (p.1.2.2.1 : ℕ) =
        (p.1.2.2.2 : ℕ) := by have := p.2; omega
    change _ = trace ((A ^ (p.1.1 : ℕ)*B)*
      ((A ^ (p.1.2.1 : ℕ)*B)*((A ^ (p.1.2.2.1 : ℕ)*B)*
        A ^ (n - (p.1.1 : ℕ) - (p.1.2.1 : ℕ) - (p.1.2.2.1 : ℕ)))))
    rw [he]
    simp only [mul_assoc]

private theorem affine_trace_eq_sum (n : ℕ) (A B : Mat) :
    (fun z : ℂ => trace ((A + z • B) ^ (n+3))) =
      fun z => ∑ k ∈ range (n+4), trace (((C A + C B * X) ^ (n+3) : Mat[X]).coeff k) * z ^ k := by
  funext z
  let p : Mat[X] := C A + C B * X
  let e : Mat[X] →+* Mat := eval₂RingHom' (RingHom.id Mat) (algebraMap ℂ Mat z)
    fun a => (Algebra.commutes z a).symm
  have hp : p.natDegree ≤ 1 := natDegree_affine_le A B
  have hdeg : (p ^ (n+3)).natDegree < n+4 := calc
    _ ≤ (n+3) * p.natDegree := natDegree_pow_le
    _ ≤ (n+3) * 1 := Nat.mul_le_mul_left _ hp
    _ < n+4 := by omega
  have he : e p = A + z • B := by
    unfold p e
    rw [map_add, map_mul]
    simp only [eval₂RingHom', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      eval₂_C, RingHom.id_apply, eval₂_X]
    rw [← Algebra.commutes z B, ← Algebra.smul_def]
  change trace ((A + z • B) ^ (n+3)) =
    ∑ k ∈ range (n+4), trace ((p ^ (n+3)).coeff k) * z ^ k
  rw [← he, ← map_pow]
  change trace (eval₂ (RingHom.id Mat) (algebraMap ℂ Mat z) (p ^ (n+3))) = _
  rw [eval₂_eq_sum_range' _ hdeg, trace_sum]
  apply sum_congr rfl
  intro k _
  rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes (z^k), ← Algebra.smul_def,
    trace_smul, smul_eq_mul, mul_comm]

/-- The third derivative at zero of the trace polynomial is exactly the
normalized average of the words with three copies of the perturbation. -/
theorem affine_trace_third_derivative (n : ℕ) (A B : Mat) :
    iteratedDeriv 3 (fun z : ℂ => trace ((A + z • B) ^ (n+3))) 0 =
      (6 * ((↑((n+3).choose 3) : ℂ))) * wordAverage n A B := by
  rw [affine_trace_eq_sum]
  rw [iteratedDeriv_fun_sum (fun i _ => by fun_prop)]
  simp_rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  rw [sum_eq_single 3]
  · rw [affine_coeff A B 3 n, trace_gapCoefficient]
    norm_num
    ring
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact False.elim (h (mem_range.mpr (by omega)))

end

end RefinedBMV
