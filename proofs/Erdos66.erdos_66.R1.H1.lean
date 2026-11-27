import OMAReductions.R_Erdos66_erdos_66_R1
import Mathlib.Topology.Order.MonotoneConvergence

/-!
Credit: @Iraeeee

For the normalized central binomial coefficients b, elementary recurrences
give b*b = 1. A second recurrence evaluates (b*L)*b, where b*L here means
pointwise multiplication by a harmonic weight L. These identities bound
the self-convolution of i ↦ b i * sqrt (L i) within a constant of log n.
The squared scale (n+1)*(b n)^2 decreases to a positive limit. A finite
boundary estimate then transfers the logarithmic asymptotic to the
fractional weights specified by H1.
-/

open AdditiveCombinatorics Filter Finset
open scoped Topology

namespace OMA.E66Calibration

/-- Coefficients of the inverse square root of one minus the variable. -/
noncomputable def kernel : ℕ → ℝ
  | 0 => 1
  | n + 1 => (((n : ℝ) + 1/2) / (n + 1)) * kernel n

noncomputable def level : ℕ → ℝ
  | 0 => 1
  | n + 1 => level n + 1 / ((n : ℝ) + 1/2)

noncomputable def moment (n : ℕ) : ℝ := kernel n * level n

lemma kernel_pos (n : ℕ) : 0 < kernel n := by
  induction n with
  | zero => norm_num [kernel]
  | succ n ih =>
    rw [kernel]
    exact mul_pos (div_pos (by positivity) (by positivity)) ih

lemma level_mono : Monotone level := by
  apply monotone_nat_of_le_succ
  intro n
  rw [level]
  exact le_add_of_nonneg_right (by positivity)

lemma level_one (n : ℕ) : 1 ≤ level n := level_mono (Nat.zero_le n)

lemma level_pos (n : ℕ) : 0 < level n := zero_lt_one.trans_le (level_one n)

/-- Weighting a convolution by its index differentiates each factor once. -/
lemma conv_recurrence (f g u v : ℕ → ℝ)
    (hf : ∀ k : ℕ, ((k : ℝ) + 1) * f (k+1) = (k+1/2) * f k + u k)
    (hg : ∀ k : ℕ, ((k : ℝ) + 1) * g (k+1) = (k+1/2) * g k + v k)
    (n : ℕ) :
    ((n : ℝ) + 1) * sumConv f g (n+1) =
      ((n : ℝ) + 1) * sumConv f g n + sumConv u g n + sumConv f v n := by
  have split (m : ℕ) : (m : ℝ) * sumConv f g m =
      sumConv (fun k ↦ (k : ℝ) * f k) g m + sumConv f (fun k ↦ (k : ℝ) * g k) m := by
    simp only [sumConv, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro ij hij
    have hh : (ij.1 : ℝ) + ij.2 = m := by
      exact_mod_cast Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [← hh]
    ring
  have left : sumConv (fun k ↦ (k : ℝ) * f k) g (n+1) =
      sumConv (fun k ↦ ((k : ℝ)+1) * f (k+1)) g n := by
    unfold sumConv
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_mul, zero_add]
  have right : sumConv f (fun k ↦ (k : ℝ) * g k) (n+1) =
      sumConv f (fun k ↦ ((k : ℝ)+1) * g (k+1)) n := by
    unfold sumConv
    rw [Finset.Nat.sum_antidiagonal_succ']
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_mul, mul_zero, zero_add]
  rw [← Nat.cast_one (R := ℝ), ← Nat.cast_add, split, left, right]
  simp only [sumConv, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro ij hij
  have hh : (n : ℝ) = (ij.1 : ℝ) + ij.2 := by
    exact_mod_cast (Finset.HasAntidiagonal.mem_antidiagonal.mp hij).symm
  rw [hf, hg]
  push_cast
  rw [hh]
  ring

lemma kernel_step (n : ℕ) :
    ((n : ℝ) + 1) * kernel (n+1) = (n+1/2) * kernel n := by
  rw [kernel]
  field_simp

lemma moment_step (n : ℕ) :
    ((n : ℝ) + 1) * moment (n+1) = (n+1/2) * moment n + kernel n := by
  unfold moment
  rw [← mul_assoc, kernel_step, level]
  have hn : (n : ℝ) + 1/2 ≠ 0 := by positivity
  field_simp

lemma kernel_self (n : ℕ) : sumConv kernel kernel n = 1 := by
  induction n with
  | zero => simp [sumConv, kernel]
  | succ n ih =>
    have hs := conv_recurrence kernel kernel (fun _ ↦ 0) (fun _ ↦ 0)
      (fun k ↦ by simpa using kernel_step k) (fun k ↦ by simpa using kernel_step k) n
    rw [ih] at hs
    simp only [sumConv, zero_mul, mul_zero, sum_const_zero, add_zero] at hs
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    exact mul_left_cancel₀ hn hs

lemma moment_self_step (n : ℕ) : sumConv moment kernel (n+1) =
    sumConv moment kernel n + 1 / ((n : ℝ)+1) := by
  have h := conv_recurrence moment kernel kernel (fun _ ↦ 0) moment_step
    (fun k ↦ by simpa using kernel_step k) n
  rw [kernel_self] at h
  have hz : sumConv moment (fun _ ↦ 0) n = 0 := by simp [sumConv]
  rw [hz, add_zero] at h
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  apply mul_left_cancel₀ hn
  rw [mul_add, h]
  field_simp

end OMA.E66Calibration

open AdditiveCombinatorics Filter Finset
open scoped Topology

namespace OMA.E66Calibration

noncomputable def logWeight (n : ℕ) : ℝ := 1 + Real.log ((n : ℝ)+1)
noncomputable def model (i : ℕ) : ℝ := kernel i * Real.sqrt (level i)

lemma log_increment (x : ℝ) (hx : 0 < x) :
    1 / (x+1) ≤ Real.log (x+1) - Real.log x ∧
    Real.log (x+1) - Real.log x ≤ 1/x := by
  have hx' : 0 < x+1 := by linarith
  rw [← Real.log_div hx'.ne' hx.ne']
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hx' hx)
    rw [inv_div] at h
    calc
      _ = 1 - x/(x+1) := by field_simp; ring
      _ ≤ _ := h
  · apply (Real.log_le_sub_one_of_pos (div_pos hx' hx)).trans
    apply le_of_eq
    field_simp
    ring

lemma logWeight_one (n : ℕ) : 1 ≤ logWeight n := by
  have h := Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+1 by linarith [Nat.cast_nonneg (α := ℝ) n])
  dsimp [logWeight]
  linarith

lemma logWeight_pos (n : ℕ) : 0 < logWeight n := zero_lt_one.trans_le (logWeight_one n)

lemma logWeight_increment (n : ℕ) :
    1 / ((n : ℝ)+2) ≤ logWeight (n+1) - logWeight n ∧
    logWeight (n+1) - logWeight n ≤ 1/((n : ℝ)+1) := by
  have h := log_increment ((n:ℝ)+1) (by positivity)
  simpa only [logWeight, Nat.cast_add, Nat.cast_one, add_sub_add_left_eq_sub,
    add_assoc, one_add_one_eq_two] using h

lemma logWeight_le_level (n : ℕ) : logWeight n ≤ level n := by
  induction n with
  | zero => simp [logWeight, level]
  | succ n ih =>
    have hp : 0 < (n:ℝ)+1/2 := by positivity
    have h := one_div_le_one_div_of_le hp (by linarith : (n:ℝ)+1/2 ≤ n+1)
    rw [level]
    linarith [(logWeight_increment n).2]

lemma level_upper_shift (n : ℕ) : level (n+2) ≤ logWeight n + 3 := by
  induction n with
  | zero => norm_num [level, logWeight]
  | succ n ih =>
    have h : 1/(((n:ℝ)+2)+1/2) ≤ 1/((n:ℝ)+2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    rw [show n+1+2 = (n+2)+1 by omega, level]
    push_cast
    linarith [(logWeight_increment n).1]

lemma level_upper (n : ℕ) : level n ≤ logWeight n + 3 :=
  (level_mono (show n ≤ n+2 by omega)).trans (level_upper_shift n)

lemma moment_lower (n : ℕ) : logWeight n ≤ sumConv moment kernel n := by
  induction n with
  | zero => simp [logWeight, sumConv, moment, kernel, level]
  | succ n ih =>
    rw [moment_self_step]
    linarith [(logWeight_increment n).2]

lemma conv_symmetric (f g : ℕ → ℝ) (n : ℕ) : sumConv f g n = sumConv g f n := by
  unfold sumConv
  simpa only [Prod.swap, mul_comm] using
    (Finset.Nat.sum_antidiagonal_swap (n := n) (f := fun q ↦ g q.1 * f q.2))

lemma model_bounds (n : ℕ) :
    logWeight n - 3 ≤ sumConv model model n ∧ sumConv model model n ≤ logWeight n + 3 := by
  have hpoint (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
      level i + level j - level n ≤ Real.sqrt (level i) * Real.sqrt (level j) ∧
      Real.sqrt (level i) * Real.sqrt (level j) ≤ level n := by
    have hi' := level_mono hi
    have hj' := level_mono hj
    have lemin : min (level i) (level j) ≤ Real.sqrt (level i) * Real.sqrt (level j) := by
      rw [← Real.sqrt_mul (level_pos i).le]
      apply Real.le_sqrt_of_sq_le
      rw [sq]
      apply mul_le_mul (min_le_left _ _) (min_le_right _ _)
        (le_min (level_pos i).le (level_pos j).le) (level_pos i).le
    refine ⟨(le_min (by linarith) (by linarith)).trans lemin, ?_⟩
    calc
      _ ≤ Real.sqrt (level n) * Real.sqrt (level n) :=
        mul_le_mul (Real.sqrt_le_sqrt hi') (Real.sqrt_le_sqrt hj')
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (level_pos n).le
  have upper : sumConv model model n ≤ level n * sumConv kernel kernel n := by
    simp only [sumConv, Finset.mul_sum]
    refine Finset.sum_le_sum fun ij hij ↦ ?_
    have hh := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have h := mul_le_mul_of_nonneg_left (hpoint ij.1 ij.2 (by omega) (by omega)).2
      (mul_nonneg (kernel_pos ij.1).le (kernel_pos ij.2).le)
    dsimp [model]
    linarith only [h]
  have lower : sumConv moment kernel n + sumConv kernel moment n - level n * sumConv kernel kernel n ≤
      sumConv model model n := by
    simp only [sumConv, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun ij hij ↦ ?_
    have hh := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have h := mul_le_mul_of_nonneg_left (hpoint ij.1 ij.2 (by omega) (by omega)).1
      (mul_nonneg (kernel_pos ij.1).le (kernel_pos ij.2).le)
    dsimp [model, moment]
    linarith only [h]
  rw [kernel_self, mul_one] at upper lower
  rw [conv_symmetric kernel moment] at lower
  exact ⟨by linarith [level_upper n, moment_lower n], upper.trans (level_upper n)⟩

lemma logN_tendsto : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma logWeight_near (n : ℕ) (hn : 1 ≤ n) :
    Real.log n ≤ logWeight n ∧ logWeight n ≤ Real.log n + 2 := by
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h2 := log_increment (n:ℝ) (by linarith)
  have hi : 1/(n:ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le zero_lt_one h1
  dsimp [logWeight]
  constructor
  · have := Real.log_le_log (by linarith : 0 < (n:ℝ)) (by linarith : (n:ℝ) ≤ n+1)
    linarith
  · linarith

lemma model_limit : Tendsto (fun n : ℕ ↦ sumConv model model n / Real.log n) atTop (𝓝 1) := by
  have small (v : ℝ) : Tendsto (fun n : ℕ ↦ v / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop logN_tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun n : ℕ ↦ 1 - 3 / Real.log n)
    (h := fun n : ℕ ↦ 1 + 5 / Real.log n)
  · simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (small 3)
  · simpa using (tendsto_const_nhds (x := (1:ℝ))).add (small 5)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hpos : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    rw [le_div_iff₀ hpos, sub_mul, div_mul_cancel₀ _ hpos.ne']
    linarith [(model_bounds n).1, (logWeight_near n (by omega)).1]
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hpos : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    rw [div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne']
    linarith [(model_bounds n).2, (logWeight_near n (by omega)).2]

end OMA.E66Calibration

open AdditiveCombinatorics Filter Finset
open scoped Topology

namespace OMA.E66Calibration

noncomputable def scaleSq (n : ℕ) : ℝ := ((n:ℝ)+1) * (kernel n)^2

lemma scaleSq_anti : Antitone scaleSq := by
  apply antitone_nat_of_succ_le
  intro n
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hd : 0 < ((n:ℝ)+1)^2 := by positivity
  have hc : ((n:ℝ)+2) * (((n:ℝ)+1/2) / (n+1))^2 ≤ n+1 := by
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ hd]
    nlinarith
  dsimp only [scaleSq]
  rw [kernel, mul_pow, ← mul_assoc]
  push_cast
  convert mul_le_mul_of_nonneg_right hc (sq_nonneg (kernel n)) using 1 <;> ring

lemma scaleSq_lower (n : ℕ) : 1/4 ≤ scaleSq n := by
  let t := fun k : ℕ ↦ (k:ℝ) * (kernel k)^2
  have ht : Monotone t := by
    apply monotone_nat_of_le_succ
    intro k
    have hd : 0 < ((k:ℝ)+1)^2 := by positivity
    have hc : (k:ℝ) ≤ ((k:ℝ)+1) * (((k:ℝ)+1/2) / (k+1))^2 := by
      rw [div_pow, ← mul_div_assoc, le_div_iff₀ hd]
      nlinarith
    dsimp only [t]
    rw [kernel, mul_pow, ← mul_assoc]
    push_cast
    exact mul_le_mul_of_nonneg_right hc (sq_nonneg (kernel k))
  cases n with
  | zero => norm_num [scaleSq, kernel]
  | succ k =>
    have hone : t 1 = 1/4 := by norm_num [t, kernel]
    calc
      _ = t 1 := hone.symm
      _ ≤ t (k+1) := ht (by omega)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

lemma scaleSq_limit : ∃ s : ℝ, 0 < s ∧ (∀ n, s ≤ scaleSq n) ∧
    Tendsto scaleSq atTop (𝓝 s) := by
  have hb : BddBelow (Set.range scaleSq) := ⟨1/4, by rintro _ ⟨n, rfl⟩; exact scaleSq_lower n⟩
  refine ⟨⨅ n, scaleSq n, ?_, fun n ↦ ciInf_le hb n, tendsto_atTop_ciInf scaleSq_anti hb⟩
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/4) (le_ciInf scaleSq_lower)

lemma model_pos (n : ℕ) : 0 < model n :=
  mul_pos (kernel_pos _) (Real.sqrt_pos.mpr (level_pos _))

lemma model_bdd (n : ℕ) : model n ≤ 2 := by
  have hgrow : ∀ k : ℕ, level k ≤ 2 * ((k : ℝ)+1) := by
    intro k
    induction k with
    | zero => norm_num [level]
    | succ k ih =>
      have hd : 0 < (k:ℝ)+1/2 := by positivity
      have hi : 1 / ((k:ℝ)+1/2) ≤ 2 := (div_le_iff₀ hd).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
      rw [level]
      push_cast
      linarith
  have hs : scaleSq n ≤ 1 := by
    calc
      _ ≤ scaleSq 0 := scaleSq_anti (Nat.zero_le n)
      _ = _ := by norm_num [scaleSq, kernel]
  have hsq : (model n)^2 ≤ 2 := by
    rw [model, mul_pow, Real.sq_sqrt (level_pos n).le]
    have := mul_le_mul_of_nonneg_left (hgrow n) (sq_nonneg (kernel n))
    dsimp only [scaleSq] at hs
    linarith
  nlinarith [sq_nonneg (model n - 1)]

lemma logWeight_tendsto : Tendsto logWeight atTop atTop := by
  apply tendsto_atTop_mono' _ _ logN_tendsto
  filter_upwards [eventually_ge_atTop 1] with n hn using (logWeight_near n hn).1

lemma level_ratio : Tendsto (fun n ↦ logWeight n / level n) atTop (𝓝 1) := by
  have hlevel : Tendsto level atTop atTop := tendsto_atTop_mono logWeight_le_level logWeight_tendsto
  have hsmall : Tendsto (fun n : ℕ ↦ 3 / level n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlevel
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ ↦ 1 - 3 / level n)
    (h := fun _ : ℕ ↦ (1:ℝ))
  · simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hsmall
  · exact tendsto_const_nhds
  · intro n
    rw [le_div_iff₀ (level_pos n), sub_mul, div_mul_cancel₀ _ (level_pos n).ne']
    linarith [level_upper n]
  · intro n
    exact (div_le_one (level_pos n)).mpr (logWeight_le_level n)

lemma fractional_anti (a : ℝ) (ha : 0 ≤ a) :
    Antitone (fun n : ℕ ↦ a * Real.sqrt (logWeight n / ((n:ℝ)+1))) := by
  apply antitone_nat_of_succ_le
  intro n
  apply mul_le_mul_of_nonneg_left _ ha
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h := (logWeight_increment n).2
  have hd : 0 < (n:ℝ)+1 := by positivity
  have hh := (le_div_iff₀ hd).mp h
  push_cast
  nlinarith [logWeight_one n]

end OMA.E66Calibration

open AdditiveCombinatorics Filter Finset
open scoped Topology

namespace OMA.E66Calibration

lemma boundary_count (K n : ℕ) :
    (∑ ij ∈ _root_.Finset.HasAntidiagonal.antidiagonal n,
      ((if ij.1 < K then (1:ℝ) else 0) + (if ij.2 < K then (1:ℝ) else 0))) ≤ 2 * K := by
  let b := fun i : ℕ ↦ if i < K then (1:ℝ) else 0
  have hf : (∑ ij ∈ _root_.Finset.HasAntidiagonal.antidiagonal n, b ij.1) ≤ K := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    dsimp only [b]
    rw [Finset.sum_boole]
    exact_mod_cast (show ((range (n+1)).filter (fun i ↦ i<K)).card ≤ K by
      calc
        _ ≤ (range K).card := card_le_card (fun i hi ↦ mem_range.mpr (mem_filter.mp hi).2)
        _ = K := Finset.card_range K)
  have he : (∑ ij ∈ _root_.Finset.HasAntidiagonal.antidiagonal n, b ij.2) = ∑ ij ∈ _root_.Finset.HasAntidiagonal.antidiagonal n, b ij.1 :=
    Finset.Nat.sum_antidiagonal_swap (f := fun ij ↦ b ij.1)
  change (∑ ij ∈ _root_.Finset.HasAntidiagonal.antidiagonal n, (b ij.1 + b ij.2)) ≤ 2 * K
  rw [Finset.sum_add_distrib, he]
  linarith

lemma conv_upper (w : ℕ → ℝ) (B : ℝ) (hw : ∀ i, 0 ≤ w i) (hmax : ∀ i, w i ≤ B) (n : ℕ) :
    sumConv (fun i ↦ w i * model i) (fun i ↦ w i * model i) n ≤ B^2 * sumConv model model n := by
  have hB : 0 ≤ B := (hw 0).trans (hmax 0)
  simp only [sumConv, Finset.mul_sum]
  refine Finset.sum_le_sum fun ij hij ↦ ?_
  have hh := mul_le_mul (hmax ij.1) (hmax ij.2) (hw ij.2) hB
  have h := mul_le_mul_of_nonneg_right hh (mul_nonneg (model_pos ij.1).le (model_pos ij.2).le)
  linarith only [h]

lemma conv_lower (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (d : ℝ) (hd : 0 ≤ d)
    (K : ℕ) (hK : ∀ i ≥ K, d ≤ w i) (n : ℕ) :
    d^2 * sumConv model model n - 8 * d^2 * K ≤
      sumConv (fun i ↦ w i * model i) (fun i ↦ w i * model i) n := by
  let b := fun i : ℕ ↦ if i < K then (1:ℝ) else 0
  have hb (i : ℕ) : 0 ≤ b i := by dsimp [b]; split <;> norm_num
  let f := fun i ↦ w i * model i
  have hf (i : ℕ) : 0 ≤ f i := mul_nonneg (hw i) (model_pos i).le
  have hpt (i j : ℕ) :
      d^2 * (model i * model j) ≤ f i * f j + (4 * d^2) * (b i + b j) := by
    by_cases hk : K ≤ i ∧ K ≤ j
    · have h := mul_le_mul (hK i hk.1) (hK j hk.2) hd (hw i)
      have hh := mul_le_mul_of_nonneg_right h (mul_nonneg (model_pos i).le (model_pos j).le)
      dsimp [f, b]
      simp only [not_lt.mpr hk.1, not_lt.mpr hk.2, if_false, add_zero, mul_zero]
      linarith only [hh]
    · have hb' : 1 ≤ b i + b j := by
        by_cases hi : i < K
        · simp [b,hi]; split <;> norm_num
        · have hj : j<K := by omega
          simp [b,hi,hj]
      have hm := mul_le_mul (model_bdd i) (model_bdd j) (model_pos j).le (by norm_num)
      have h := mul_le_mul_of_nonneg_left hm (sq_nonneg d)
      have h' := mul_le_mul_of_nonneg_left hb' (show 0 ≤ 4*d^2 by positivity)
      linarith [mul_nonneg (hf i) (hf j)]
  have hh : d^2 * sumConv model model n ≤ sumConv f f n +
      (4*d^2) * ∑ ij ∈ _root_.Finset.HasAntidiagonal.antidiagonal n, (b ij.1 + b ij.2) := by
    simp only [sumConv, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun ij _ ↦ hpt ij.1 ij.2
  have hbnd := mul_le_mul_of_nonneg_left (boundary_count K n) (by positivity : 0 ≤ 4*d^2)
  change 4*d^2 * (∑ ij ∈ _root_.Finset.HasAntidiagonal.antidiagonal n, (b ij.1 + b ij.2)) ≤ _ at hbnd
  change _ ≤ sumConv f f n
  linarith only [hh,hbnd]

/-- A bounded coefficient multiplier with a positive limit scales the leading
logarithmic convolution coefficient by the square of that limit. -/
lemma transfer (w : ℕ → ℝ) (B : ℝ) (hB : 0 < B) (hw : ∀ i, 0 ≤ w i)
    (hmax : ∀ i, w i ≤ B) (hlim : Tendsto w atTop (𝓝 B)) :
    Tendsto (fun n : ℕ ↦ sumConv (fun i ↦ w i * model i) (fun i ↦ w i * model i) n /
      Real.log n) atTop (𝓝 (B^2)) := by
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n:ℝ) := logN_tendsto.eventually_gt_atTop 0
  apply tendsto_order.mpr
  constructor
  · intro z hz
    let d := (Real.sqrt z + B)/2
    have hs : Real.sqrt z < B := (Real.sqrt_lt' hB).mpr hz
    have hd : 0 < d := by dsimp [d]; linarith [Real.sqrt_nonneg z]
    have hdB : d < B := by dsimp [d]; linarith
    have hsd : Real.sqrt z < d := by dsimp [d]; linarith
    have hzd : z < d^2 := (Real.sqrt_lt' hd).mp hsd
    obtain ⟨K,hK⟩ := eventually_atTop.mp (hlim.eventually (lt_mem_nhds hdB))
    have small : Tendsto (fun n : ℕ ↦ (8*d^2*K) / Real.log (n:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop logN_tendsto
    have hbound : Tendsto (fun n : ℕ ↦ d^2*(sumConv model model n / Real.log n) -
        (8*d^2*K) / Real.log n) atTop (𝓝 (d^2)) := by
      simpa using ((tendsto_const_nhds (x := d^2)).mul model_limit).sub small
    filter_upwards [hbound.eventually (lt_mem_nhds hzd), hlog] with n hn hl
    apply hn.trans_le
    have h := div_le_div_of_nonneg_right (conv_lower w hw d hd.le K (fun i hi ↦ (hK i hi).le) n) hl.le
    simpa only [sub_div, mul_div_assoc] using h
  · intro z hz
    have hb : Tendsto (fun n : ℕ ↦ B^2 * (sumConv model model n / Real.log n)) atTop (𝓝 (B^2)) := by
      simpa using (tendsto_const_nhds (x := B^2)).mul model_limit
    filter_upwards [hb.eventually (gt_mem_nhds hz), hlog] with n hn hl
    apply lt_of_le_of_lt _ hn
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right (conv_upper w B hw hmax n) hl.le

end OMA.E66Calibration

open AdditiveCombinatorics Filter
open scoped Topology
open OMA.E66Calibration

theorem OMA.solution : OMA.R_Erdos66_erdos_66_R1.H1 := by
  intro a ha
  refine ⟨fractional_anti a ha.le, fun i ↦ mul_nonneg ha.le (Real.sqrt_nonneg _), ?_⟩
  obtain ⟨s, hs, hsle, hslim⟩ := scaleSq_limit
  let B := a * Real.sqrt (1/s)
  let w := fun i ↦ a * Real.sqrt ((logWeight i / level i) / scaleSq i)
  have hB : 0 < B := mul_pos ha (Real.sqrt_pos.mpr (one_div_pos.mpr hs))
  have hw (i : ℕ) : 0 ≤ w i := mul_nonneg ha.le (Real.sqrt_nonneg _)
  have hmax (i : ℕ) : w i ≤ B := by
    apply mul_le_mul_of_nonneg_left _ ha.le
    apply Real.sqrt_le_sqrt
    have hi := (div_le_one (level_pos i)).mpr (logWeight_le_level i)
    exact (div_le_div_of_nonneg_right hi (hs.trans_le (hsle i)).le).trans
      (one_div_le_one_div_of_le hs (hsle i))
  have hwlim : Tendsto w atTop (𝓝 B) :=
    tendsto_const_nhds.mul (level_ratio.div hslim hs.ne').sqrt
  have hf (i : ℕ) : w i * model i = a * Real.sqrt (logWeight i / ((i:ℝ)+1)) := by
    dsimp only [w]
    rw [mul_assoc]
    congr 1
    apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (model_pos i).le) (Real.sqrt_nonneg _)).mp
    have hi : 0 ≤ (logWeight i / level i) / scaleSq i :=
      div_nonneg (div_nonneg (logWeight_pos i).le (level_pos i).le) (hs.trans_le (hsle i)).le
    rw [mul_pow, Real.sq_sqrt hi, model, mul_pow, Real.sq_sqrt (level_pos i).le,
      Real.sq_sqrt (div_nonneg (logWeight_pos i).le (by positivity))]
    dsimp only [scaleSq]
    field_simp [(level_pos i).ne', (kernel_pos i).ne']
  refine ⟨B^2, (sq_pos_of_pos hB), ?_⟩
  simpa only [hf, logWeight] using transfer w B hB hw hmax hwlim
