import OMAReductions.R_Erdos535_erdos_535_R1

/-!
Numerical cutoff estimate for the main Erdős 535 reduction.
For x = log N, choose y = ceil(sqrt x), L = ceil(x/log 2)+1,
and K = ceil(2*x/log x). The resulting counting cost is bounded by
N^((6+3*log C)/log(log N)) for all sufficiently large N.
-/


open Real Filter

namespace OMA535Growth

lemma cutoff_estimate {x C : ℝ}
    (hx : 4 ≤ x) (ht : 4 ≤ log x)
    (hscale : 1 / log 2 + 3 ≤ x)
    (hsmall : (log x) ^ 2 ≤ sqrt x) (hC : 1 ≤ C) :
    ∃ (y L K : ℕ), 2 ≤ y ∧
      exp x < (2 : ℝ) ^ L ∧ exp x < (y : ℝ) ^ (K + 1) ∧
      ((((L + 1) ^ y * (K + 1) : ℕ) : ℝ) * C ^ K) ≤
        exp ((6 + 3 * log C) * x / log x) := by
  let y : ℕ := ⌈sqrt x⌉₊
  let L : ℕ := ⌈x / log 2⌉₊ + 1
  let K : ℕ := ⌈2 * x / log x⌉₊
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < log x := by linarith
  have htwo : 0 < log 2 := log_pos (by norm_num)
  have hs0 : 0 ≤ sqrt x := sqrt_nonneg _
  have hsq : sqrt x ^ 2 = x := sq_sqrt hx0.le
  have hs2 : 2 ≤ sqrt x := by nlinarith
  have hsx : sqrt x ≤ x := by nlinarith
  have hylo : sqrt x ≤ (y : ℝ) := Nat.le_ceil _
  have hyhi : (y : ℝ) ≤ 2 * sqrt x := by
    have := Nat.ceil_lt_add_one hs0
    change (y : ℝ) < sqrt x + 1 at this
    linarith
  have hy : 2 ≤ y := by exact_mod_cast hs2.trans hylo
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hy)
  have hlogy : log x / 2 ≤ log (y : ℝ) := by
    rw [← log_sqrt hx0.le]
    exact log_le_log (by linarith) hylo
  have hLlo : x / log 2 < (L : ℝ) := by
    have := Nat.le_ceil (x / log 2)
    dsimp [L]
    push_cast
    linarith
  have hL : exp x < (2 : ℝ) ^ L := by
    apply (log_lt_log_iff (exp_pos _) (pow_pos (by norm_num) _)).mp
    rw [log_exp, log_pow]
    exact (div_lt_iff₀ htwo).mp hLlo
  have hLhi : (L : ℝ) + 1 ≤ x ^ 2 := by
    have hceil := Nat.ceil_lt_add_one (div_nonneg hx0.le htwo.le)
    have haux : x / log 2 + 3 ≤ x ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hscale hx0.le
      have hthree : (3 : ℝ) ≤ 3 * x := by linarith
      have hid : (1 / log 2 + 3) * x = x / log 2 + 3 * x := by ring
      rw [hid] at hmul
      nlinarith only [hmul, hthree]
    dsimp [L]
    push_cast
    linarith
  have hlogL : log ((L : ℝ) + 1) ≤ 2 * log x := by
    calc
      log ((L : ℝ) + 1) ≤ log (x ^ 2) := log_le_log (by positivity) hLhi
      _ = 2 * log x := by rw [log_pow]; norm_num
  have hklo : 2 * x / log x ≤ (K : ℝ) := Nat.le_ceil _
  have hkhi0 : (K : ℝ) < 2 * x / log x + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hratio : 1 ≤ x / log x := by
    apply (le_div_iff₀ ht0).mpr
    have := log_le_sub_one_of_pos hx0
    linarith
  have hkhi : (K : ℝ) ≤ 3 * x / log x := by
    calc
      (K : ℝ) ≤ 2 * x / log x + 1 := hkhi0.le
      _ ≤ 2 * x / log x + x / log x := add_le_add le_rfl hratio
      _ = 3 * x / log x := by ring
  have hklog : log ((K : ℝ) + 1) ≤ x / log x := by
    have hquot : 2 * x / log x ≤ x / 2 := by
      apply (div_le_iff₀ ht0).mpr
      have := mul_nonneg hx0.le (sub_nonneg.mpr ht)
      nlinarith
    have hkx : (K : ℝ) + 1 ≤ x := by linarith
    have htbound : log x ≤ x / log x := by
      apply (le_div_iff₀ ht0).mpr
      nlinarith
    exact (log_le_log (by positivity) hkx).trans htbound
  have hK : exp x < (y : ℝ) ^ (K + 1) := by
    apply (log_lt_log_iff (exp_pos _) (pow_pos hy0 _)).mp
    rw [log_exp, log_pow]
    have hkprod : 2 * x ≤ (K : ℝ) * log x :=
      (div_le_iff₀ ht0).mp hklo
    have hmul := mul_le_mul_of_nonneg_left hlogy (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1)
    push_cast
    nlinarith
  have hfirst : (y : ℝ) * log ((L : ℝ) + 1) ≤ 4 * x / log x := by
    have hp : (y : ℝ) * log ((L : ℝ) + 1) ≤ (2 * sqrt x) * (2 * log x) :=
      mul_le_mul hyhi hlogL
        (log_nonneg (by have := Nat.cast_nonneg (α := ℝ) L; linarith)) (by positivity)
    have hsmall' := mul_le_mul_of_nonneg_left hsmall hs0
    have hp' := mul_le_mul_of_nonneg_right hp ht0.le
    apply (le_div_iff₀ ht0).mpr
    nlinarith
  have hc0 : 0 < C := by linarith
  have hlogC : 0 ≤ log C := log_nonneg hC
  have hlast : (K : ℝ) * log C ≤ (3 * x / log x) * log C :=
    mul_le_mul_of_nonneg_right hkhi hlogC
  refine ⟨y, L, K, hy, hL, hK, ?_⟩
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  apply (log_le_log_iff (by positivity) (exp_pos _)).mp
  rw [log_exp, log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_pow, log_pow]
  have hsum := add_le_add (add_le_add hfirst hklog) hlast
  calc
    (y : ℝ) * log ((L : ℝ) + 1) + log ((K : ℝ) + 1) + (K : ℝ) * log C
        ≤ 4 * x / log x + x / log x + (3 * x / log x) * log C := hsum
    _ ≤ (6 + 3 * log C) * x / log x := by
      calc
        _ = (5 + 3 * log C) * (x / log x) := by ring
        _ ≤ (6 + 3 * log C) * (x / log x) :=
          mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hx0.le ht0.le)
        _ = (6 + 3 * log C) * x / log x := by ring

end OMA535Growth

namespace OMA535Growth

lemma eventually_log_sq_le_sqrt :
    ∀ᶠ (x : ℝ) in atTop, (log x) ^ 2 ≤ sqrt x := by
  have h := (isLittleO_log_rpow_rpow_atTop
    (s := (1 : ℝ) / 2) 2 (by norm_num)).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h] with x hx
  rw [Real.rpow_two, ← Real.sqrt_eq_rpow] at hx
  simpa only [one_mul, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (sqrt_nonneg _)] using hx

theorem numerical_cutoffs :
    ∀ C : ℝ, 1 ≤ C → ∃ c > (0 : ℝ),
      ∀ᶠ (N : ℕ) in atTop,
        ∃ (y L K : ℕ), 2 ≤ y ∧ N < 2 ^ L ∧ N < y ^ (K + 1) ∧
          ((((L + 1) ^ y * (K + 1) : ℕ) : ℝ) * C ^ K) ≤
            (N : ℝ) ^ (c / log (log (N : ℝ))) := by
  intro C hC
  have hlogC : 0 ≤ log C := Real.log_nonneg hC
  refine ⟨6 + 3 * log C, by linarith, ?_⟩
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun N : ℕ => log (log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hsmall : ∀ᶠ (N : ℕ) in atTop,
      (log (log (N : ℝ))) ^ 2 ≤ sqrt (log (N : ℝ)) :=
    hlog.eventually eventually_log_sq_le_sqrt
  filter_upwards [hlog.eventually_ge_atTop 4, hloglog.eventually_ge_atTop 4,
    hlog.eventually_ge_atTop (1 / log 2 + 3), hsmall,
    eventually_ge_atTop (1 : ℕ)] with N hx ht hscale hsmall hN
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  obtain ⟨y, L, K, hy, hL, hK, hbound⟩ := cutoff_estimate hx ht hscale hsmall hC
  refine ⟨y, L, K, hy, ?_, ?_, ?_⟩
  · have h : (N : ℝ) < (2 : ℝ) ^ L := by
      simpa only [exp_log hNpos] using hL
    exact_mod_cast h
  · have h : (N : ℝ) < (y : ℝ) ^ (K + 1) := by
      simpa only [exp_log hNpos] using hK
    exact_mod_cast h
  · calc
      _ ≤ exp ((6 + 3 * log C) * log (N : ℝ) / log (log (N : ℝ))) := hbound
      _ = (N : ℝ) ^ ((6 + 3 * log C) / log (log (N : ℝ))) := by
        rw [Real.rpow_def_of_pos hNpos]
        congr 1
        ring

end OMA535Growth


theorem OMA.solution : OMA.R_Erdos535_erdos_535_R1.H3 := by
  exact OMA535Growth.numerical_cutoffs
