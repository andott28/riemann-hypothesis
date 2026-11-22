import RHLeanFullShard20


set_option maxHeartbeats 2000000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 2000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option maxRecDepth 1000000
set_option maxRecDepth 1000000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000

section Inline_GateII_AWGC






















open Finset

namespace RHLean.GateII.AWGC

open RHLean.GateII.Chain






theorem tsum_Jm_lt : ∑' m : ℕ, Jm (m + 1) < 0.100317302 := by
  rw [tsum_Jm]
  have hγ : ((577215664901531953 / 10 ^ 18 : ℚ) : ℝ) ≤ Real.eulerMascheroniConstant :=
    Y7Chain.gamma_box.lo_le
  norm_num at hγ
  have hπ : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hπ2 : (3.14159265358979323846 : ℝ) ^ 2 < Real.pi ^ 2 := by
    nlinarith [Real.pi_pos]
  nlinarith [hγ, hπ2]





noncomputable def TkHi (k : ℕ) (hi : ℕ → ℚ) : ℚ :=
  ∑ n ∈ (Finset.range (k + 1)).filter (fun n => Lambda n ≠ 0), hi n / (n : ℚ)





theorem MertensActive_of_boxes {k : ℕ} {hi : ℕ → ℚ} {logkLo : ℚ}
    (hhi : ∀ n, IsPrimePow n → Lambda n ≤ (hi n : ℝ))
    (hlo : (logkLo : ℝ) ≤ Real.log (k : ℝ))
    (hcheck : TkHi k hi < logkLo) :
    MertensActive k := by
  have hT_mono :
      (∑ n ∈ (Finset.range (k + 1)).filter (fun n => Lambda n ≠ 0),
          Lambda n / (n : ℝ))
        ≤ ∑ n ∈ (Finset.range (k + 1)).filter (fun n => Lambda n ≠ 0),
            (hi n : ℝ) / (n : ℝ) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn'
    have hpp : IsPrimePow n :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (by simpa [Lambda] using hn'.2)
    exact div_le_div_of_nonneg_right (hhi n hpp) (Nat.cast_nonneg n)
  have hS_le_T :
      (∑ n ∈ activeN k, Lambda n / (n : ℝ))
        ≤ ∑ n ∈ (Finset.range (k + 1)).filter (fun n => Lambda n ≠ 0),
            Lambda n / (n : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro n hn
      rw [activeN, Finset.mem_filter] at hn
      exact Finset.mem_filter.mpr ⟨hn.1, hn.2.1⟩
    · intro n _ _
      exact div_nonneg (by simpa [Lambda] using ArithmeticFunction.vonMangoldt_nonneg (n := n))
        (Nat.cast_nonneg n)
  have hcast : ((TkHi k hi : ℚ) : ℝ)
      = ∑ n ∈ (Finset.range (k + 1)).filter (fun n => Lambda n ≠ 0),
          (hi n : ℝ) / (n : ℝ) := by
    unfold TkHi
    push_cast
    ring
  have hcheckR : (∑ n ∈ (Finset.range (k + 1)).filter (fun n => Lambda n ≠ 0),
        (hi n : ℝ) / (n : ℝ)) < (logkLo : ℝ) := by
    rw [← hcast]
    exact_mod_cast hcheck
  unfold MertensActive
  calc (∑ n ∈ activeN k, Lambda n / (n : ℝ))
      ≤ (∑ n ∈ (Finset.range (k + 1)).filter (fun n => Lambda n ≠ 0),
          Lambda n / (n : ℝ)) := hS_le_T
    _ ≤ (∑ n ∈ (Finset.range (k + 1)).filter (fun n => Lambda n ≠ 0),
          (hi n : ℝ) / (n : ℝ)) := hT_mono
    _ ≤ (logkLo : ℝ) := le_of_lt hcheckR
    _ ≤ Real.log (k : ℝ) := hlo



def MertensSweep : Prop :=
  ∀ k : ℕ, 7 ≤ k → k ≤ 3594641 → MertensActive k



def MertensTail : Prop :=
  ∀ k : ℕ, 3594642 ≤ k → MertensActive k


theorem MertensActive_of_sweep_tail (hs : MertensSweep) (ht : MertensTail) :
    ∀ k : ℕ, 7 ≤ k → MertensActive k := by
  intro k hk
  by_cases h : k ≤ 3594641
  · exact hs k hk h
  · exact ht k (by omega)


noncomputable def La (k m : ℕ) : ℝ := Real.log ((k : ℝ) / ((m : ℝ) + 1))


noncomputable def Lb (k m : ℕ) : ℝ := Real.log ((k : ℝ) / (m : ℝ))




theorem Lb_sub_one_sq_div_La_le {k m : ℕ} (hm : 1 ≤ m)
    (ha : 2.9 < (k : ℝ) / ((m : ℝ) + 1)) (hk : 15 ≤ Real.log (k : ℝ)) :
    (Lb k m - 1) ^ 2 / La k m ≤ Real.log (k : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmp0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    by_contra h
    have hle : (k : ℝ) / ((m : ℝ) + 1) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hmp0.le
    linarith
  have hLa1 : Real.log 2.9 < La k m := by
    unfold La
    exact Real.log_lt_log (by norm_num) ha
  have hLaL : La k m ≤ Real.log (k : ℝ) := by
    unfold La
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hmp0]
    nlinarith [hk0.le, hm0.le]
  have hlog29 : (1 : ℝ) < Real.log 2.9 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h := Real.exp_one_lt_d9
    norm_num at h ⊢
    linarith
  have hLb_eq : Lb k m = La k m + Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
    have harg : (k : ℝ) / (m : ℝ)
        = ((k : ℝ) / ((m : ℝ) + 1)) * (((m : ℝ) + 1) / (m : ℝ)) := by
      field_simp <;> positivity
    unfold Lb La
    rw [harg]
    exact Real.log_mul (div_ne_zero hk0.ne' hmp0.ne') (div_ne_zero hmp0.ne' hm0.ne')
  have hlog_inc : Real.log (((m : ℝ) + 1) / (m : ℝ)) ≤ 1 / (m : ℝ) := by
    have hpos : 0 < ((m : ℝ) + 1) / (m : ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    have heq : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by
      field_simp
      ring
    linarith
  have hlog_delta_nonneg : 0 ≤ Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hm0]
    linarith
  by_cases hm1 : m = 1
  · subst hm1
    have hLa : La k 1 = Real.log (k : ℝ) - Real.log 2 := by
      unfold La
      norm_num
      exact Real.log_div hk0.ne' (by norm_num : (2 : ℝ) ≠ 0)
    have hLb : Lb k 1 = Real.log (k : ℝ) := by
      simp [Lb]
    rw [hLa, hLb]
    have hlog2lt1 : Real.log 2 < 1 := by
      have h := Real.log_two_lt_d9
      norm_num at h ⊢
      linarith
    have hden : 0 < Real.log (k : ℝ) - Real.log 2 := by linarith
    rw [div_le_iff₀ hden]
    nlinarith [hk, hlog2lt1]
  · have hm2 : 2 ≤ m := by omega
    have hhalf : 1 / (m : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hm2)
    have hLb1_nonneg : 0 ≤ Lb k m - 1 := by
      rw [hLb_eq]
      linarith [hLa1, hlog29, hlog_delta_nonneg]
    by_cases hLa2 : 2 ≤ La k m
    · have h1 : Lb k m - 1 ≤ La k m := by
        linarith [hLb_eq, hlog_inc, hhalf]
      have hsq : (Lb k m - 1) ^ 2 ≤ (La k m) ^ 2 :=
        pow_le_pow_left₀ hLb1_nonneg h1 2
      have hden : 0 < La k m := by linarith
      calc (Lb k m - 1) ^ 2 / La k m
          ≤ (La k m) ^ 2 / La k m := div_le_div_of_nonneg_right hsq hden.le
        _ = La k m := by field_simp
        _ ≤ Real.log (k : ℝ) := hLaL
    · have hLa2' : La k m < 2 := not_le.mp hLa2
      have h1 : Lb k m - 1 ≤ 3 / 2 := by
        linarith [hLb_eq, hlog_inc, hhalf, hLa2']
      have hsq : (Lb k m - 1) ^ 2 ≤ (9 / 4 : ℝ) := by
        have h := pow_le_pow_left₀ hLb1_nonneg h1 2
        norm_num at h ⊢
        exact h
      have hden : 0 < La k m := by linarith
      have hbound : (Lb k m - 1) ^ 2 / La k m ≤ (9 / 4) / Real.log 2.9 := by
        have h1' : (Lb k m - 1) ^ 2 / La k m ≤ (9 / 4) / La k m :=
          div_le_div_of_nonneg_right hsq hden.le
        have h2' : (9 / 4) / La k m ≤ (9 / 4) / Real.log 2.9 :=
          div_le_div_of_nonneg_left (by norm_num) (by linarith [hlog29]) hLa1.le
        linarith
      have h29 : (9 / 4) / Real.log 2.9 ≤ Real.log (k : ℝ) := by
        have hlt : (9 / 4) / Real.log 2.9 < 9 / 4 :=
          div_lt_self (by norm_num) hlog29
        linarith
      linarith





noncomputable def Dm (m : ℕ) : ℝ := if m ≤ 2 then 3 / 10 else 5



noncomputable def Em (L : ℝ) (m : ℕ) : ℝ :=
  2 * Dm m * (L - Real.log (m : ℝ) - 1) ^ 2
    / ((m : ℝ) * ((m : ℝ) + 1) * (L - Real.log ((m : ℝ) + 1)) ^ 3)




theorem sq_div_cube_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) :
    x ^ 2 / (x + c) ^ 3 ≤ 4 / (27 * c) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hfac : 4 * (x + c) ^ 3 - 27 * c * x ^ 2
      = (x - 2 * c) ^ 2 * (4 * x + c) := by ring
  nlinarith [sq_nonneg (x - 2 * c),
    mul_nonneg (sq_nonneg (x - 2 * c)) (by linarith : (0 : ℝ) ≤ 4 * x + c), hfac]





theorem Em_tail_term_le {L : ℝ} {m : ℕ} (hm : 101 ≤ m)
    (ha : Real.log 2.9 < L - Real.log ((m : ℝ) + 1)) :
    Em L m ≤ (4040 / 2700) / ((m : ℝ) * ((m : ℝ) + 1)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmp0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hDm : Dm m = 5 := by
    unfold Dm
    rw [if_neg (by omega : ¬m ≤ 2)]
  set c : ℝ := 1 - Real.log (((m : ℝ) + 1) / (m : ℝ)) with hcdef
  have hratio_gt_one : 1 < ((m : ℝ) + 1) / (m : ℝ) := by
    rw [lt_div_iff₀ hm0]
    linarith
  have hlog_pos : 0 < Real.log (((m : ℝ) + 1) / (m : ℝ)) := Real.log_pos hratio_gt_one
  have hlog_le : Real.log (((m : ℝ) + 1) / (m : ℝ)) ≤ 1 / (m : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < ((m : ℝ) + 1) / (m : ℝ))
    have heq : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by
      field_simp
      ring
    linarith
  have hm_gt_one : 1 / (m : ℝ) < 1 := by
    rw [div_lt_one hm0]
    exact_mod_cast (by omega : 1 < m)
  have hc_pos : 0 < c := by
    rw [hcdef]
    linarith
  have hc_ge : 100 / 101 ≤ c := by
    rw [hcdef]
    have hm101 : (101 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have : 1 / (m : ℝ) ≤ 1 / 101 := one_div_le_one_div_of_le (by norm_num) hm101
    linarith
  have hLa_eq : L - Real.log ((m : ℝ) + 1) = (L - Real.log (m : ℝ) - 1) + c := by
    have hlog : Real.log ((m : ℝ) + 1)
        = Real.log (m : ℝ) + Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
      have hmul : (m : ℝ) * (((m : ℝ) + 1) / (m : ℝ)) = (m : ℝ) + 1 := by
        field_simp
      conv_lhs => rw [← hmul]
      exact Real.log_mul hm0.ne' (by positivity : ((m : ℝ) + 1) / (m : ℝ) ≠ 0)
    rw [hcdef, hlog]
    ring
  have hlog29_gt_one : (1 : ℝ) < Real.log 2.9 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h := Real.exp_one_lt_d9
    norm_num at h ⊢
    linarith
  have hc_le_one : c ≤ 1 := by
    rw [hcdef]
    linarith [Real.log_nonneg hratio_gt_one.le]
  have hx_nonneg : 0 ≤ L - Real.log (m : ℝ) - 1 := by
    linarith [hLa_eq, ha, hc_le_one, hlog29_gt_one]
  have hden : 0 < (m : ℝ) * ((m : ℝ) + 1) := mul_pos hm0 hmp0
  have hshape : (L - Real.log (m : ℝ) - 1) ^ 2
      / (L - Real.log ((m : ℝ) + 1)) ^ 3 ≤ 404 / 2700 := by
    have h := sq_div_cube_le hx_nonneg hc_pos
    have hcb : 4 / (27 * c) ≤ 404 / 2700 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hc_ge]
    rw [hLa_eq]
    linarith
  unfold Em
  rw [hDm]
  have hLa_pos : 0 < L - Real.log ((m : ℝ) + 1) := by
    linarith [hLa_eq, hx_nonneg, hc_pos]
  have hshape' : (L - Real.log (m : ℝ) - 1) ^ 2
      ≤ (404 / 2700) * (L - Real.log ((m : ℝ) + 1)) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hshape
      (by positivity : (0 : ℝ) ≤ (L - Real.log ((m : ℝ) + 1)) ^ 3)
    rwa [div_mul_cancel₀ _ (pow_ne_zero 3 hLa_pos.ne')] at h
  rw [div_le_div_iff₀
    (by positivity : 0 < (m : ℝ) * ((m : ℝ) + 1) * (L - Real.log ((m : ℝ) + 1)) ^ 3) hden]
  nlinarith [hshape', hden]



theorem tsum_shifted_inv_mul_le {a : ℕ} (ha : 1 ≤ a) :
    ∑' m : ℕ, 1 / (((m : ℝ) + a) * ((m : ℝ) + a + 1)) ≤ 1 / a := by
  have hpartial : ∀ N : ℕ,
      ∑ m ∈ Finset.range N, 1 / (((m : ℝ) + a) * ((m : ℝ) + a + 1))
        = 1 / (a : ℝ) - 1 / ((N : ℝ) + a) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : ((N : ℝ) + a) ≠ 0 := by positivity
      have h2 : ((N : ℝ) + a + 1) ≠ 0 := by positivity
      have h3 : (a : ℝ) ≠ 0 := by positivity
      field_simp [h1, h2, h3]
      push_cast
      ring
  refine Real.tsum_le_of_sum_range_le (fun m => by positivity) (fun N => ?_)
  rw [hpartial N]
  have : 0 ≤ 1 / ((N : ℝ) + a) := by positivity
  linarith



theorem sum_Icc_101_inv_mul_le (M : ℕ) :
    ∑ m ∈ Finset.Icc 101 M, 1 / ((m : ℝ) * ((m : ℝ) + 1)) ≤ 1 / 101 := by
  by_cases hM : M < 101
  · rw [Finset.Icc_eq_empty_of_lt hM]
    simp
  · have hM'
    have htel : ∀ M : ℕ, 101 ≤ M →
        ∑ m ∈ Finset.Icc 101 M, 1 / ((m : ℝ) * ((m : ℝ) + 1))
          = 1 / 101 - 1 / ((M : ℝ) + 1) := by
      intro M hM
      refine Nat.le_induction ?_ ?_ M hM
      · rw [Finset.Icc_self, Finset.sum_singleton]
        norm_num
      · intro n hn ih
        rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hn), ih]
        push_cast
        have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
        have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
        field_simp [h1, h2]
        ring
    rw [htel M hM']
    have : 0 ≤ 1 / ((M : ℝ) + 1) := by positivity
    linarith




theorem Em_Icc_tail_le {L : ℝ} (M : ℕ)
    (hact : ∀ m ∈ Finset.Icc 101 M, Real.log 2.9 < L - Real.log ((m : ℝ) + 1)) :
    ∑ m ∈ Finset.Icc 101 M, Em L m ≤ (4040 / 2700) / 101 := by
  have hterm : ∀ m ∈ Finset.Icc 101 M,
      Em L m ≤ (4040 / 2700) * (1 / ((m : ℝ) * ((m : ℝ) + 1))) := by
    intro m hm
    have hm101 : 101 ≤ m := (Finset.mem_Icc.mp hm).1
    have h := Em_tail_term_le (L := L) hm101 (hact m hm)
    rwa [div_eq_mul_one_div] at h
  calc ∑ m ∈ Finset.Icc 101 M, Em L m
      ≤ ∑ m ∈ Finset.Icc 101 M,
          (4040 / 2700) * (1 / ((m : ℝ) * ((m : ℝ) + 1))) :=
        Finset.sum_le_sum hterm
    _ = (4040 / 2700)
          * ∑ m ∈ Finset.Icc 101 M, 1 / ((m : ℝ) * ((m : ℝ) + 1)) := by
        rw [Finset.mul_sum]
    _ ≤ (4040 / 2700) * (1 / 101) :=
        mul_le_mul_of_nonneg_left (sum_Icc_101_inv_mul_le M) (by norm_num)
    _ = (4040 / 2700) / 101 := by ring






theorem sum_Em_lt_of_finite {L : ℝ} (M : ℕ) (S100 : ℝ) (hM : 101 ≤ M)
    (hfinite : ∑ m ∈ Finset.Icc 1 100, Em L m ≤ S100)
    (hS : S100 + (4040 / 2700) / 101 < 0.259330618)
    (hact : ∀ m ∈ Finset.Icc 101 M,
      Real.log 2.9 < L - Real.log ((m : ℝ) + 1)) :
    ∑ m ∈ Finset.Icc 1 M, Em L m < 0.259330618 := by
  have hunion : Finset.Icc 1 M = Finset.Icc 1 100 ∪ Finset.Icc 101 M := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 100) (Finset.Icc 101 M) := by
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    simp only [Finset.mem_Icc] at hm1 hm2
    omega
  rw [hunion, Finset.sum_union hdisj]
  have htail := Em_Icc_tail_le (L := L) M hact
  linarith




def DmQ (m : ℕ) : ℚ := if m ≤ 2 then 3 / 10 else 5

theorem Dm_eq_DmQ (m : ℕ) : Dm m = (DmQ m : ℝ) := by
  unfold Dm DmQ
  split <;> norm_num


noncomputable def cm (m : ℕ) : ℝ := 1 - Real.log (((m : ℝ) + 1) / (m : ℝ))


private theorem log_succ_le_six__GateII_AWGC {m : ℕ} (hm200 : m ≤ 200) :
    Real.log ((m : ℝ) + 1) ≤ 6 := by
  have h201 : ((m : ℝ) + 1) ≤ 201 := by exact_mod_cast (by omega : m + 1 ≤ 201)
  have h1 : Real.log ((m : ℝ) + 1) ≤ Real.log 201 := Real.log_le_log (by positivity) h201
  have h2 : Real.log (201 : ℝ) ≤ Real.log 256 := Real.log_le_log (by norm_num) (by norm_num)
  have h3 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  have h4 : Real.log 2 < 7 / 10 := by nlinarith [Real.log_two_lt_d9]
  linarith



private theorem Em_eq_cm__GateII_AWGC (L : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Em L m = 2 * Dm m * ((L - Real.log ((m : ℝ) + 1)) - cm m) ^ 2
      / ((m : ℝ) * ((m : ℝ) + 1) * (L - Real.log ((m : ℝ) + 1)) ^ 3) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmul : (m : ℝ) * (((m : ℝ) + 1) / (m : ℝ)) = (m : ℝ) + 1 := by
    field_simp
  have hlog : Real.log ((m : ℝ) + 1)
      = Real.log (m : ℝ) + Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
    conv_lhs => rw [← hmul]
    exact Real.log_mul hmR.ne' (by positivity : ((m : ℝ) + 1) / (m : ℝ) ≠ 0)
  unfold Em cm
  rw [hlog]
  ring


private theorem antitoneOn_sq_div_cube__GateII_AWGC {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    AntitoneOn (fun u : ℝ => (u - c) ^ 2 / u ^ 3) (Set.Ici 3) := by
  intro u₁ hu₁ u₂ hu₂ hle
  simp only [Set.mem_Ici] at hu₁ hu₂
  have hu₁0 : (0 : ℝ) < u₁ := by linarith
  have hu₂0 : (0 : ℝ) < u₂ := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hdiff : (u₁ - c) ^ 2 * u₂ ^ 3 - (u₂ - c) ^ 2 * u₁ ^ 3
      = (u₂ - u₁) * (u₁ ^ 2 * u₂ ^ 2 - 2 * c * (u₁ + u₂) * u₁ * u₂
          + c ^ 2 * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2)) := by ring
  have hbracket : 0 ≤ u₁ ^ 2 * u₂ ^ 2 - 2 * c * (u₁ + u₂) * u₁ * u₂
      + c ^ 2 * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) := by
    have hkey : 0 ≤ (u₁ * u₂ - (u₁ + u₂)) ^ 2 - u₁ * u₂ := by
      have h33 : 0 ≤ (u₁ - 3) * (u₂ - 3) := mul_nonneg (by linarith) (by linarith)
      nlinarith [h33]
    have hprod : (u₁ + u₂) * u₁ * u₂ ≥ u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2 := by nlinarith
    have hsplit : u₁ ^ 2 * u₂ ^ 2 - 2 * c * (u₁ + u₂) * u₁ * u₂
        + c ^ 2 * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2)
        = ((u₁ * u₂ - (u₁ + u₂)) ^ 2 - u₁ * u₂)
          + (1 - c) * (2 * (u₁ + u₂) * u₁ * u₂
              - (1 + c) * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2)) := by ring
    rw [hsplit]
    have hnn : 0 ≤ (1 - c) * (2 * (u₁ + u₂) * u₁ * u₂
        - (1 + c) * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2)) := by
      apply mul_nonneg (by linarith)
      nlinarith [hprod, hc1]
    linarith
  nlinarith [hdiff, hbracket, sub_nonneg.mpr hle]




theorem Em_antitone_Ici {m : ℕ} (hm : 1 ≤ m) (hm200 : m ≤ 200) :
    AntitoneOn (fun L : ℝ => Em L m) (Set.Ici 15) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hc0 : 0 ≤ cm m := by
    unfold cm
    have hle2 : ((m : ℝ) + 1) / (m : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hmR]
      have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hlog_le : Real.log (((m : ℝ) + 1) / (m : ℝ)) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) hle2
    have hlog2 : Real.log 2 < 1 := by nlinarith [Real.log_two_lt_d9]
    linarith
  have hc1 : cm m ≤ 1 := by
    unfold cm
    have hnn : 0 ≤ Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hmR]
      linarith
    linarith
  have hlog_mp6 : Real.log ((m : ℝ) + 1) ≤ 6 := log_succ_le_six__GateII_AWGC hm200
  intro L₁ hL₁ L₂ hL₂ hL
  simp only [Set.mem_Ici] at hL₁ hL₂
  change Em L₂ m ≤ Em L₁ m
  rw [Em_eq_cm__GateII_AWGC L₁ hm, Em_eq_cm__GateII_AWGC L₂ hm]
  have hu₁3 : 3 ≤ L₁ - Real.log ((m : ℝ) + 1) := by linarith
  have hu₂3 : 3 ≤ L₂ - Real.log ((m : ℝ) + 1) := by linarith
  have hbase := antitoneOn_sq_div_cube__GateII_AWGC (c := cm m) hc0 hc1 hu₁3 hu₂3
    (by linarith : L₁ - Real.log ((m : ℝ) + 1) ≤ L₂ - Real.log ((m : ℝ) + 1))
  have hK : 0 ≤ 2 * Dm m / ((m : ℝ) * ((m : ℝ) + 1)) := by
    have : 0 ≤ Dm m := by unfold Dm; split <;> norm_num
    positivity
  calc 2 * Dm m * ((L₂ - Real.log ((m : ℝ) + 1)) - cm m) ^ 2
        / ((m : ℝ) * ((m : ℝ) + 1) * (L₂ - Real.log ((m : ℝ) + 1)) ^ 3)
      = (2 * Dm m / ((m : ℝ) * ((m : ℝ) + 1)))
          * (((L₂ - Real.log ((m : ℝ) + 1)) - cm m) ^ 2
              / (L₂ - Real.log ((m : ℝ) + 1)) ^ 3) := by
        have hu : L₂ - Real.log ((m : ℝ) + 1) ≠ 0 := by linarith
        field_simp [hmR.ne', hu]
    _ ≤ (2 * Dm m / ((m : ℝ) * ((m : ℝ) + 1)))
          * (((L₁ - Real.log ((m : ℝ) + 1)) - cm m) ^ 2
              / (L₁ - Real.log ((m : ℝ) + 1)) ^ 3) :=
        mul_le_mul_of_nonneg_left hbase hK
    _ = 2 * Dm m * ((L₁ - Real.log ((m : ℝ) + 1)) - cm m) ^ 2
        / ((m : ℝ) * ((m : ℝ) + 1) * (L₁ - Real.log ((m : ℝ) + 1)) ^ 3) := by
        have hu : L₁ - Real.log ((m : ℝ) + 1) ≠ 0 := by linarith
        field_simp [hmR.ne', hu]



theorem Em_le_of_log_bounds {m : ℕ} (hm : 1 ≤ m) (hm200 : m ≤ 200)
    {lo hi : ℝ} (hlo : lo ≤ Real.log (m : ℝ))
    (hhi : Real.log ((m : ℝ) + 1) ≤ hi) (hlo14 : lo ≤ 14) (hhi15 : hi < 15) :
    Em 15 m ≤ 2 * Dm m * (14 - lo) ^ 2
      / ((m : ℝ) * ((m : ℝ) + 1) * (15 - hi) ^ 3) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlog_m6 : Real.log (m : ℝ) ≤ 6 := by
    have hle : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith [log_succ_le_six__GateII_AWGC hm200]
  unfold Em
  have hnum : (15 - Real.log (m : ℝ) - 1) ^ 2 ≤ (14 - lo) ^ 2 := by
    have h1 : 15 - Real.log (m : ℝ) - 1 ≤ 14 - lo := by linarith
    have h2 : 0 ≤ 15 - Real.log (m : ℝ) - 1 := by linarith
    nlinarith
  have hden : (15 - hi) ^ 3 ≤ (15 - Real.log ((m : ℝ) + 1)) ^ 3 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  have hpos1 : 0 < (m : ℝ) * ((m : ℝ) + 1) * (15 - Real.log ((m : ℝ) + 1)) ^ 3 := by
    have h15 : 0 < 15 - Real.log ((m : ℝ) + 1) := by linarith
    exact mul_pos (mul_pos hmR (by linarith)) (pow_pos h15 3)
  have hpos2 : 0 < (m : ℝ) * ((m : ℝ) + 1) * (15 - hi) ^ 3 := by
    have h15 : 0 < 15 - hi := by linarith
    exact mul_pos (mul_pos hmR (by linarith)) (pow_pos h15 3)
  rw [div_le_div_iff₀ hpos1 hpos2]
  have hprod : (15 - Real.log (m : ℝ) - 1) ^ 2 * (15 - hi) ^ 3
      ≤ (14 - lo) ^ 2 * (15 - Real.log ((m : ℝ) + 1)) ^ 3 :=
    mul_le_mul hnum hden (by positivity) (sq_nonneg _)
  have hprod2 := mul_le_mul_of_nonneg_left hprod
    (by positivity : (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) + 1))
  have hDm0 : 0 ≤ Dm m := by unfold Dm; split <;> norm_num
  have hprod3 := mul_le_mul_of_nonneg_left hprod2 (by linarith : (0 : ℝ) ≤ 2 * Dm m)
  nlinarith [hprod3]





theorem sum_Em_le_of_data (LO HI : ℕ → ℚ) (S : ℚ)
    (hLO : ∀ m : ℕ, m ∈ Finset.Icc 1 200 → ((LO m : ℚ) : ℝ) ≤ Real.log (m : ℝ))
    (hHI : ∀ m : ℕ, m ∈ Finset.Icc 1 200 → Real.log ((m : ℝ) + 1) ≤ ((HI m : ℚ) : ℝ))
    (hLO14 : ∀ m : ℕ, m ∈ Finset.Icc 1 200 → LO m ≤ 14)
    (hHI15 : ∀ m : ℕ, m ∈ Finset.Icc 1 200 → HI m < 15)
    (hsum : (∑ m ∈ Finset.Icc 1 200,
        2 * DmQ m * (14 - LO m) ^ 2
          / ((m : ℚ) * ((m : ℚ) + 1) * (15 - HI m) ^ 3)) ≤ S) :
    ∀ L : ℝ, 15 ≤ L → ∑ m ∈ Finset.Icc 1 200, Em L m ≤ (S : ℝ) := by
  intro L hL
  have hstep : ∀ m ∈ Finset.Icc 1 200,
      Em L m ≤ 2 * Dm m * (14 - ((LO m : ℚ) : ℝ)) ^ 2
        / ((m : ℝ) * ((m : ℝ) + 1) * (15 - ((HI m : ℚ) : ℝ)) ^ 3) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm200 : m ≤ 200 := (Finset.mem_Icc.mp hm).2
    exact le_trans (Em_antitone_Ici hm1 hm200 (by simp) hL hL)
      (Em_le_of_log_bounds hm1 hm200 (hLO m hm) (hHI m hm)
        (by exact_mod_cast hLO14 m hm) (by exact_mod_cast hHI15 m hm))
  calc ∑ m ∈ Finset.Icc 1 200, Em L m
      ≤ ∑ m ∈ Finset.Icc 1 200, 2 * Dm m * (14 - ((LO m : ℚ) : ℝ)) ^ 2
          / ((m : ℝ) * ((m : ℝ) + 1) * (15 - ((HI m : ℚ) : ℝ)) ^ 3) :=
        Finset.sum_le_sum hstep
    _ = ((∑ m ∈ Finset.Icc 1 200, 2 * DmQ m * (14 - LO m) ^ 2
          / ((m : ℚ) * ((m : ℚ) + 1) * (15 - HI m) ^ 3) : ℚ) : ℝ) := by
        push_cast
        apply Finset.sum_congr rfl
        intro m _
        rw [Dm_eq_DmQ]
    _ ≤ (S : ℝ) := by exact_mod_cast hsum

end RHLean.GateII.AWGC



end Inline_GateII_AWGC

section Inline_GateII_SweepBase



























open Finset
open scoped BigOperators

namespace RHLean.GateII.Sweep

open RHLean.GateII.Chain







structure LogBox where
  p : ℕ
  lo : ℚ
  hi : ℚ
  hp : 0 < p
  hlo : (lo : ℝ) ≤ Real.log p
  hhi : Real.log p ≤ (hi : ℝ)

theorem LogBox.sound (b : LogBox) :
    (b.lo : ℝ) ≤ Real.log b.p ∧ Real.log b.p ≤ (b.hi : ℝ) :=
  ⟨b.hlo, b.hhi⟩


theorem isPrimePow_of_vonMangoldt_ne_zero {n : ℕ} (h : Lambda n ≠ 0) :
    IsPrimePow n :=
  ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (by simpa [Lambda] using h)






noncomputable def Vhi (k m : ℕ) (lo hi : ℕ → ℚ) : ℚ :=
  (∑ n ∈ Nset k m, (hi n) ^ 2 / (n : ℚ))
    - (∑ n ∈ Nset k m, lo n) ^ 2 / (∑ n ∈ Nset k m, (n : ℚ))

theorem Vhi_cast (k m : ℕ) (lo hi : ℕ → ℚ) :
    ((Vhi k m lo hi : ℚ) : ℝ)
      = (∑ n ∈ Nset k m, (hi n : ℝ) ^ 2 / (n : ℝ))
        - (∑ n ∈ Nset k m, (lo n : ℝ)) ^ 2 / (∑ n ∈ Nset k m, (n : ℝ)) := by
  unfold Vhi
  push_cast
  ring





theorem V_le_Vhi (k m : ℕ) {lo hi : ℕ → ℚ}
    (hlo0 : ∀ n, 0 ≤ lo n)
    (hlo : ∀ n, IsPrimePow n → (lo n : ℝ) ≤ Lambda n)
    (hhi : ∀ n, IsPrimePow n → Lambda n ≤ (hi n : ℝ)) :
    V k m ≤ ((Vhi k m lo hi : ℚ) : ℝ) := by
  by_cases hne : (Nset k m).Nonempty
  · have hpp : ∀ n ∈ Nset k m, IsPrimePow n := fun n hn =>
      isPrimePow_of_vonMangoldt_ne_zero (mem_Nset.mp hn).2.1
    have hΛ0 : ∀ n ∈ Nset k m, 0 ≤ Lambda n := fun n _ =>
      by simpa [Lambda] using ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hA : (∑ n ∈ Nset k m, (Lambda n) ^ 2 / (n : ℝ))
        ≤ ∑ n ∈ Nset k m, (hi n : ℝ) ^ 2 / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := Nset_pos hn
      have hsq : (Lambda n) ^ 2 ≤ (hi n : ℝ) ^ 2 :=
        pow_le_pow_left₀ (hΛ0 n hn) (hhi n (hpp n hn)) 2
      exact div_le_div_of_nonneg_right hsq hn0.le
    have hB : (∑ n ∈ Nset k m, (lo n : ℝ)) ≤ ∑ n ∈ Nset k m, Lambda n := by
      apply Finset.sum_le_sum
      intro n hn
      exact hlo n (hpp n hn)
    have hB0 : 0 ≤ ∑ n ∈ Nset k m, Lambda n :=
      Finset.sum_nonneg (fun n hn => hΛ0 n hn)
    have hB0' : 0 ≤ ∑ n ∈ Nset k m, (lo n : ℝ) :=
      Finset.sum_nonneg (fun n _ => by exact_mod_cast hlo0 n)
    have hBsq : (∑ n ∈ Nset k m, (lo n : ℝ)) ^ 2
        ≤ (∑ n ∈ Nset k m, Lambda n) ^ 2 :=
      pow_le_pow_left₀ hB0' hB 2
    have hC : 0 < ∑ n ∈ Nset k m, (n : ℝ) := by
      obtain ⟨n, hn⟩ := hne
      exact Finset.sum_pos (fun n hn => Nset_pos hn) ⟨n, hn⟩
    have hdiv : (∑ n ∈ Nset k m, (lo n : ℝ)) ^ 2 / (∑ n ∈ Nset k m, (n : ℝ))
        ≤ (∑ n ∈ Nset k m, Lambda n) ^ 2 / (∑ n ∈ Nset k m, (n : ℝ)) :=
      div_le_div_of_nonneg_right hBsq hC.le
    rw [Vhi_cast]
    unfold V
    linarith
  · have hemp : Nset k m = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [V, Vhi, hemp]


theorem Vsum_le_VhiSum (k : ℕ) {lo hi : ℕ → ℚ}
    (hlo0 : ∀ n, 0 ≤ lo n)
    (hlo : ∀ n, IsPrimePow n → (lo n : ℝ) ≤ Lambda n)
    (hhi : ∀ n, IsPrimePow n → Lambda n ≤ (hi n : ℝ)) :
    Vsum k ≤ ((∑ m ∈ Finset.range (k + 1), Vhi k m lo hi : ℚ) : ℝ) := by
  unfold Vsum
  push_cast
  exact Finset.sum_le_sum (fun m _ => V_le_Vhi k m hlo0 hlo hhi)

theorem Vsum_nonneg (k : ℕ) : 0 ≤ Vsum k :=
  Finset.sum_nonneg (fun m _ => V_nonneg k m)








noncomputable def Slow (k : ℕ) (lo hiLog : ℕ → ℚ) (beta0hi : ℚ) : ℚ :=
  ∑ n ∈ activeN k, (lo n) ^ 2 / ((n : ℚ) * (hiLog n + beta0hi))

theorem Slow_cast (k : ℕ) (lo hiLog : ℕ → ℚ) (beta0hi : ℚ) :
    ((Slow k lo hiLog beta0hi : ℚ) : ℝ)
      = ∑ n ∈ activeN k, (lo n : ℝ) ^ 2
          / ((n : ℝ) * ((hiLog n : ℝ) + beta0hi)) := by
  unfold Slow
  push_cast
  ring


theorem Slow_le_sigmaTilde (k : ℕ) {lo hiLog : ℕ → ℚ} {beta0hi : ℚ}
    (hlo0 : ∀ n, 0 ≤ lo n)
    (hlo : ∀ n, IsPrimePow n → (lo n : ℝ) ≤ Lambda n)
    (hlog : ∀ n : ℕ, IsPrimePow n → Real.log (n : ℝ) ≤ (hiLog n : ℝ))
    (hbeta : beta0 ≤ (beta0hi : ℝ)) :
    ((Slow k lo hiLog beta0hi : ℚ) : ℝ) ≤ sigmaTilde k := by
  rw [Slow_cast]
  unfold sigmaTilde
  apply Finset.sum_le_sum
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  have hpp : IsPrimePow n := isPrimePow_of_vonMangoldt_ne_zero hn'.2.1
  have hΛ : Lambda n ≠ 0 := hn'.2.1
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have hn0' : n ≠ 0 := by
      intro h0
      exact hΛ (by simp [Lambda, h0, ArithmeticFunction.map_zero])
    exact_mod_cast Nat.pos_of_ne_zero hn0'
  have hx0 : 0 ≤ Lambda n := by
    simpa [Lambda] using ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hl0 : 0 ≤ (lo n : ℝ) := by exact_mod_cast hlo0 n
  have hlx : (lo n : ℝ) ≤ Lambda n := hlo n hpp
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      exact hΛ (by simp [Lambda, h0, ArithmeticFunction.map_zero]))))
  have hbeta0 : 0 < beta0 := beta0_pos
  have hb0 : 0 ≤ (beta0hi : ℝ) := le_trans hbeta0.le hbeta
  have hden1 : 0 < (n : ℝ) * ((hiLog n : ℝ) + beta0hi) :=
    mul_pos hn0 (by linarith [hlog n hpp, hbeta0, hlogn])
  have hden2 : 0 < (n : ℝ) * (Real.log (n : ℝ) + beta0) :=
    mul_pos hn0 (by linarith)
  rw [div_le_div_iff₀ hden1 hden2]
  have hx2 : ((lo n : ℝ)) ^ 2 ≤ (Lambda n) ^ 2 := pow_le_pow_left₀ hl0 hlx 2
  have hdenle : Real.log (n : ℝ) + beta0 ≤ (hiLog n : ℝ) + beta0hi := by
    linarith [hlog n hpp, hbeta]
  have hgoal : (lo n : ℝ) ^ 2 * (Real.log (n : ℝ) + beta0)
      ≤ (Lambda n) ^ 2 * ((hiLog n : ℝ) + beta0hi) :=
    mul_le_mul hx2 hdenle (by linarith) (sq_nonneg _)
  calc (lo n : ℝ) ^ 2 * ((n : ℝ) * (Real.log (n : ℝ) + beta0))
      = (n : ℝ) * ((lo n : ℝ) ^ 2 * (Real.log (n : ℝ) + beta0)) := by ring
    _ ≤ (n : ℝ) * ((Lambda n) ^ 2 * ((hiLog n : ℝ) + beta0hi)) :=
        mul_le_mul_of_nonneg_left hgoal hn0.le
    _ = (Lambda n) ^ 2 * ((n : ℝ) * ((hiLog n : ℝ) + beta0hi)) := by ring










theorem FiniteSweep_of_boxes {lo hi hiLog : ℕ → ℚ} {log2lo log2hi : ℚ}
    (hlog2lo_pos : 0 < log2lo)
    (hlog2lo : (log2lo : ℝ) ≤ Real.log 2)
    (hlog2hi : Real.log 2 ≤ (log2hi : ℝ))
    (hlo0 : ∀ n, 0 ≤ lo n)
    (hlo : ∀ n, IsPrimePow n → (lo n : ℝ) ≤ Lambda n)
    (hhi : ∀ n, IsPrimePow n → Lambda n ≤ (hi n : ℝ))
    (hlog : ∀ n : ℕ, IsPrimePow n → Real.log (n : ℝ) ≤ (hiLog n : ℝ))
    (hcheck : ∀ k : ℕ, 2 ≤ k → k ≤ 3594641 →
      (1 / (log2lo : ℝ))
          * ((∑ m ∈ Finset.range (k + 1), Vhi k m lo hi : ℚ) : ℝ)
        ≤ ((Slow k lo hiLog (log2hi + 1 / 2) : ℚ) : ℝ)) :
    FiniteSweep := by
  intro k hk hkX
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbeta : beta0 ≤ ((log2hi + 1 / 2 : ℚ) : ℝ) := by
    unfold beta0
    push_cast
    linarith
  have hV : Vsum k ≤ ((∑ m ∈ Finset.range (k + 1), Vhi k m lo hi : ℚ) : ℝ) :=
    Vsum_le_VhiSum k hlo0 hlo hhi
  have hV0 : 0 ≤ Vsum k := Vsum_nonneg k
  have hcoef : (1 : ℝ) / Real.log 2 ≤ 1 / (log2lo : ℝ) := by
    have hlog2loR : 0 < (log2lo : ℝ) := by exact_mod_cast hlog2lo_pos
    exact one_div_le_one_div_of_le hlog2loR hlog2lo
  have h1 : (1 / Real.log 2) * Vsum k
      ≤ (1 / (log2lo : ℝ)) * Vsum k :=
    mul_le_mul_of_nonneg_right hcoef hV0
  have h2 : (1 / (log2lo : ℝ)) * Vsum k
      ≤ (1 / (log2lo : ℝ))
          * ((∑ m ∈ Finset.range (k + 1), Vhi k m lo hi : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hV (by positivity)
  exact le_trans (le_trans h1 h2)
    (le_trans (hcheck k hk hkX) (Slow_le_sigmaTilde k hlo0 hlo hlog hbeta))





noncomputable def logLo (log2lo : ℚ) (e n : ℕ) (x : ℚ) : ℚ :=
  (e : ℚ) * log2lo + 2 * ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1)



noncomputable def logHi (log2hi : ℚ) (e n : ℕ) (x : ℚ) : ℚ :=
  (e : ℚ) * log2hi
    + 2 * ((∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1))
        + x ^ (2 * n + 1) / (1 - x ^ 2))




theorem logLo_sound {p e n : ℕ} {x log2lo : ℚ}
    (hp : 0 < p) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hxp : (1 + x) / (1 - x) = (p : ℚ) / (2 : ℚ) ^ e)
    (hlog2lo : (log2lo : ℝ) ≤ Real.log 2) :
    (logLo log2lo e n x : ℝ) ≤ Real.log (p : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h2R : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hlogp : Real.log (p : ℝ) = (e : ℝ) * Real.log 2
      + Real.log ((p : ℝ) / (2 : ℝ) ^ e) := by
    rw [← Real.log_pow, ← Real.log_mul h2R.ne' (div_ne_zero hpR.ne' h2R.ne')]
    congr 1
    field_simp
  have hcast : ((logLo log2lo e n x : ℚ) : ℝ)
      = (e : ℝ) * (log2lo : ℝ)
        + 2 * ∑ i ∈ Finset.range n, (x : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
    unfold logLo
    push_cast
    ring
  have hxeq : ((1 + (x : ℝ)) / (1 - (x : ℝ))) = (p : ℝ) / (2 : ℝ) ^ e := by
    have hcast' := congrArg (fun q : ℚ => (q : ℝ)) hxp
    simpa using hcast'
  have hlow := Real.sum_range_le_log_div (x := (x : ℝ))
    (by exact_mod_cast hx0) (by exact_mod_cast hx1) n
  rw [hxeq] at hlow
  have hcoef : (e : ℝ) * (log2lo : ℝ) ≤ (e : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2lo (Nat.cast_nonneg e)
  rw [hcast, hlogp]
  linarith



theorem logHi_sound {p e n : ℕ} {x log2hi : ℚ}
    (hp : 0 < p) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hxp : (1 + x) / (1 - x) = (p : ℚ) / (2 : ℚ) ^ e)
    (hlog2hi : Real.log 2 ≤ (log2hi : ℝ)) :
    Real.log (p : ℝ) ≤ (logHi log2hi e n x : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h2R : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hlogp : Real.log (p : ℝ) = (e : ℝ) * Real.log 2
      + Real.log ((p : ℝ) / (2 : ℝ) ^ e) := by
    rw [← Real.log_pow, ← Real.log_mul h2R.ne' (div_ne_zero hpR.ne' h2R.ne')]
    congr 1
    field_simp
  have hcast : ((logHi log2hi e n x : ℚ) : ℝ)
      = (e : ℝ) * (log2hi : ℝ)
        + 2 * ((∑ i ∈ Finset.range n, (x : ℝ) ^ (2 * i + 1) / (2 * i + 1))
          + (x : ℝ) ^ (2 * n + 1) / (1 - (x : ℝ) ^ 2)) := by
    unfold logHi
    push_cast
    ring
  have hxeq : ((1 + (x : ℝ)) / (1 - (x : ℝ))) = (p : ℝ) / (2 : ℝ) ^ e := by
    have hcast' := congrArg (fun q : ℚ => (q : ℝ)) hxp
    simpa using hcast'
  have hhi := Real.log_div_le_sum_range_add (x := (x : ℝ))
    (by exact_mod_cast hx0) (by exact_mod_cast hx1) n
  rw [hxeq] at hhi
  have hcoef : (e : ℝ) * Real.log 2 ≤ (e : ℝ) * (log2hi : ℝ) :=
    mul_le_mul_of_nonneg_left hlog2hi (Nat.cast_nonneg e)
  rw [hcast, hlogp]
  linarith



structure LogLowerCert where
  p : ℕ
  e : ℕ
  n : ℕ
  x : ℚ
  log2lo : ℚ
  hp : 0 < p
  hx0 : 0 ≤ x
  hx1 : x < 1
  hxp : (1 + x) / (1 - x) = (p : ℚ) / (2 : ℚ) ^ e
  hlog2lo : (log2lo : ℝ) ≤ Real.log 2

theorem LogLowerCert.sound (b : LogLowerCert) :
    (logLo b.log2lo b.e b.n b.x : ℝ) ≤ Real.log b.p :=
  logLo_sound b.hp b.hx0 b.hx1 b.hxp b.hlog2lo


structure LogUpperCert where
  p : ℕ
  e : ℕ
  n : ℕ
  x : ℚ
  log2hi : ℚ
  hp : 0 < p
  hx0 : 0 ≤ x
  hx1 : x < 1
  hxp : (1 + x) / (1 - x) = (p : ℚ) / (2 : ℚ) ^ e
  hlog2hi : Real.log 2 ≤ (log2hi : ℝ)

theorem LogUpperCert.sound (b : LogUpperCert) :
    Real.log b.p ≤ (logHi b.log2hi b.e b.n b.x : ℝ) :=
  logHi_sound b.hp b.hx0 b.hx1 b.hxp b.hlog2hi



noncomputable def LogBox.ofCerts (lo : LogLowerCert) (hi : LogUpperCert)
    (hp : lo.p = hi.p) : LogBox where
  p := lo.p
  lo := logLo lo.log2lo lo.e lo.n lo.x
  hi := logHi hi.log2hi hi.e hi.n hi.x
  hp := lo.hp
  hlo := lo.sound
  hhi := by
    rw [hp]
    exact hi.sound

end RHLean.GateII.Sweep



end Inline_GateII_SweepBase

section Inline_GateII_PrimePart

























open Set
open MeasureTheory

namespace RHLean.GateII.PrimePart

open RHLean.GateII.Chain
open RHLean.GateII.AWGC



theorem La_eq {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    La k m = Real.log (k : ℝ) - Real.log ((m : ℝ) + 1) := by
  unfold La
  rw [Real.log_div (by positivity) (by positivity)]

theorem Lb_eq {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    Lb k m = Real.log (k : ℝ) - Real.log (m : ℝ) := by
  unfold Lb
  rw [Real.log_div (by positivity) (by positivity)]



theorem Em_eq_La_Lb {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    Em (Real.log (k : ℝ)) m
      = 2 * Dm m * (Lb k m - 1) ^ 2
        / ((m : ℝ) * ((m : ℝ) + 1) * (La k m) ^ 3) := by
  unfold Em
  rw [La_eq hk hm, Lb_eq hk hm]

theorem Dm_nonneg (m : ℕ) : 0 ≤ Dm m := by
  unfold Dm
  split <;> norm_num












theorem Em_error_term_le {k m : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (ha : 2.9 < (k : ℝ) / ((m : ℝ) + 1)) :
    2 * Dm m * ((k : ℝ) / (m : ℝ)) / (La k m) ^ 2
        * gpar (Lb k m / ((k : ℝ) / (m : ℝ))) ((k : ℝ) / ((m : ℝ) + 1))
      ≤ Em (Real.log (k : ℝ)) m := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hmp0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set A : ℝ := (k : ℝ) / ((m : ℝ) + 1) with hA
  set B : ℝ := (k : ℝ) / (m : ℝ) with hB
  have hApos : 0 < A := lt_trans (by norm_num) ha
  have hAexp : Real.exp 1 ≤ A := by
    have h := Real.exp_one_lt_d9
    norm_num at h
    linarith
  have hAleB : A ≤ B := by
    rw [hA, hB]
    exact div_le_div_of_nonneg_left hk0.le hm0 (by linarith)
  have hBexp : Real.exp 1 ≤ B := by
    have hmul : 2.9 * ((m : ℝ) + 1) < (k : ℝ) := by
      rw [lt_div_iff₀ hmp0] at ha
      exact ha
    have h29B : (2.9 : ℝ) < B := by
      rw [hB, lt_div_iff₀ hm0]
      nlinarith [hmul]
    have h := Real.exp_one_lt_d9
    norm_num at h
    linarith
  have hLbB : Lb k m = Real.log B := by
    unfold Lb
    rw [hB]
  have hLaA : La k m = Real.log A := by
    unfold La
    rw [hA]
  have hlapos : 0 < La k m := by
    rw [hLaA]
    exact Real.log_pos (lt_of_lt_of_le (by norm_num) hAexp)
  have hBpos : 0 < B := lt_of_lt_of_le (Real.exp_pos 1) hBexp
  have hLbpos : 0 < Lb k m := by
    rw [hLbB]
    exact Real.log_pos (lt_of_lt_of_le (by norm_num) hBexp)

  have hAB : A / B = (m : ℝ) / ((m : ℝ) + 1) := by
    rw [hA, hB]
    field_simp
    try ring

  have hlog_lb : 1 / ((m : ℝ) + 1) ≤ Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
    have h := Real.one_sub_inv_le_log_of_pos (x := ((m : ℝ) + 1) / (m : ℝ)) (by positivity)
    have heq : 1 - (((m : ℝ) + 1) / (m : ℝ))⁻¹ = 1 / ((m : ℝ) + 1) := by
      field_simp
      try ring
    rwa [heq] at h

  have hAub : Apar (Lb k m / B) A ≤ (Lb k m - 1) / ((m : ℝ) + 1) := by
    have hlogA : Real.log A = Lb k m + Real.log ((m : ℝ) / ((m : ℝ) + 1)) := by
      have hAeq : A = B * ((m : ℝ) / ((m : ℝ) + 1)) := by
        rw [← hAB]
        field_simp
      rw [hAeq, Real.log_mul hBpos.ne' (by positivity), hLbB]
    have hlogm : Real.log ((m : ℝ) / ((m : ℝ) + 1))
        = -Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_div (by positivity) (by positivity)]
      ring
    have hApar : Apar (Lb k m / B) A
        = (Lb k m - ((m : ℝ) + 1) * Real.log (((m : ℝ) + 1) / (m : ℝ)))
            / ((m : ℝ) + 1) := by
      unfold Apar
      rw [hlogA, hlogm]
      have hca : Lb k m / B * A = Lb k m * ((m : ℝ) / ((m : ℝ) + 1)) := by
        calc Lb k m / B * A = Lb k m * (A / B) := by ring
          _ = Lb k m * ((m : ℝ) / ((m : ℝ) + 1)) := by rw [hAB]
      rw [hca]
      field_simp
      try ring
    rw [hApar, div_le_div_iff₀ hmp0 hmp0]
    have hmul := mul_le_mul_of_nonneg_left hlog_lb hmp0.le
    have h1 : ((m : ℝ) + 1) * (1 / ((m : ℝ) + 1)) = 1 := by
      field_simp
    have hge : (1 : ℝ) ≤ ((m : ℝ) + 1) * Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
      linarith [hmul, h1]
    have hmul2 := mul_le_mul_of_nonneg_left hge hmp0.le
    nlinarith [hmul2]

  have hA0 : 0 ≤ Apar (Lb k m / B) A := by
    have h := Apar_nonneg (b := B) (t := A) hBexp hAexp hAleB
    have hc : Lb k m / B = Real.log B / B := by rw [hLbB]
    simpa [hc] using h

  have hgub : gpar (Lb k m / B) A
      ≤ (Lb k m - 1) ^ 2 / (((m : ℝ) + 1) * (k : ℝ) * La k m) := by
    have hAparseq : gpar (Lb k m / B) A
        = (Apar (Lb k m / B) A) ^ 2 / (A * La k m) := by
      unfold gpar
      rw [hLaA]
    rw [hAparseq]
    have hnum : (Apar (Lb k m / B) A) ^ 2 ≤ ((Lb k m - 1) / ((m : ℝ) + 1)) ^ 2 :=
      pow_le_pow_left₀ hA0 hAub 2
    have hfac : 0 < ((m : ℝ) + 1) / ((k : ℝ) * La k m) := by positivity
    calc (Apar (Lb k m / B) A) ^ 2 / (A * La k m)
        = (Apar (Lb k m / B) A) ^ 2
            * (((m : ℝ) + 1) / ((k : ℝ) * La k m)) := by
          rw [hA]
          field_simp
          try ring
      _ ≤ ((Lb k m - 1) / ((m : ℝ) + 1)) ^ 2
            * (((m : ℝ) + 1) / ((k : ℝ) * La k m)) :=
          mul_le_mul_of_nonneg_right hnum hfac.le
      _ = (Lb k m - 1) ^ 2 / (((m : ℝ) + 1) * (k : ℝ) * La k m) := by
          field_simp
          try ring

  have hconst : 0 ≤ 2 * Dm m * B / (La k m) ^ 2 := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) (Dm_nonneg m)) hBpos.le
    · positivity
  have hstep : 2 * Dm m * B / (La k m) ^ 2 * gpar (Lb k m / B) A
      ≤ 2 * Dm m * B / (La k m) ^ 2
          * ((Lb k m - 1) ^ 2 / (((m : ℝ) + 1) * (k : ℝ) * La k m)) :=
    mul_le_mul_of_nonneg_left hgub hconst
  have hmid : 2 * Dm m * B / (La k m) ^ 2
        * ((Lb k m - 1) ^ 2 / (((m : ℝ) + 1) * (k : ℝ) * La k m))
      = 2 * Dm m * (Lb k m - 1) ^ 2
          / ((m : ℝ) * ((m : ℝ) + 1) * (La k m) ^ 3) := by
    rw [hB]
    field_simp
    try ring
  rw [Em_eq_La_Lb (by omega : 0 < k) (by omega : 0 < m)]
  exact le_trans hstep (le_of_eq hmid)









theorem integral_gpar_le {k m : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (ha : 2.9 < (k : ℝ) / ((m : ℝ) + 1)) :
    ∫ t in (k : ℝ) / ((m : ℝ) + 1)..(k : ℝ) / (m : ℝ),
        gpar (Lb k m / ((k : ℝ) / (m : ℝ))) t
      ≤ ((Lb k m - 1) ^ 2 / La k m) * Jm m := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hmp0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set A : ℝ := (k : ℝ) / ((m : ℝ) + 1) with hA
  set B : ℝ := (k : ℝ) / (m : ℝ) with hB
  have hApos : 0 < A := lt_trans (by norm_num) ha
  have hAexp_lt : Real.exp 1 < A := by
    have h := Real.exp_one_lt_d9
    norm_num at h
    linarith
  have hAexp : Real.exp 1 ≤ A := hAexp_lt.le
  have hBexp_lt : Real.exp 1 < B := by
    have hmul : 2.9 * ((m : ℝ) + 1) < (k : ℝ) := by
      rw [lt_div_iff₀ hmp0] at ha
      exact ha
    have h29B : (2.9 : ℝ) < B := by
      rw [hB, lt_div_iff₀ hm0]
      nlinarith [hmul]
    have h := Real.exp_one_lt_d9
    norm_num at h
    linarith
  have hBexp : Real.exp 1 ≤ B := hBexp_lt.le
  have hBpos : 0 < B := lt_of_lt_of_le (Real.exp_pos 1) hBexp
  have hLbB : Lb k m = Real.log B := by
    unfold Lb
    rw [hB]
  have hLaA : La k m = Real.log A := by
    unfold La
    rw [hA]
  have hlapos : 0 < La k m := by
    rw [hLaA]
    exact Real.log_pos (lt_of_lt_of_le (by norm_num) hAexp)
  have hLb_gt_one : 1 < Lb k m := by
    rw [hLbB, Real.lt_log_iff_exp_lt (lt_of_lt_of_le (Real.exp_pos 1) hBexp)]
    exact hBexp_lt
  have hBAm : B * ((m : ℝ) / ((m : ℝ) + 1)) = A := by
    rw [hA, hB]
    field_simp
    try ring

  have hsub : ∫ t in A..B, gpar (Lb k m / B) t
      = B * ∫ u in (m : ℝ) / ((m : ℝ) + 1)..1, gpar (Lb k m / B) (B * u) := by
    have h := intervalIntegral.integral_comp_mul_left
      (f := gpar (Lb k m / B)) (a := (m : ℝ) / ((m : ℝ) + 1)) (b := 1) hBpos.ne'
    rw [smul_eq_mul] at h
    have hB1 : B * 1 = B := by ring
    rw [hBAm, hB1] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ hBpos.ne', one_mul]
  rw [hsub]

  have hfrac_le : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hmp0]
    linarith
  have hmem : ∀ u ∈ Set.uIcc ((m : ℝ) / ((m : ℝ) + 1)) 1, 0 < B * u := by
    intro u hu
    rw [Set.uIcc_of_le hfrac_le] at hu
    exact mul_pos hBpos (lt_of_lt_of_le (by positivity) hu.1)
  have hABu : ∀ u ∈ Set.uIcc ((m : ℝ) / ((m : ℝ) + 1)) 1, A ≤ B * u := by
    intro u hu
    rw [Set.uIcc_of_le hfrac_le] at hu
    rw [← hBAm]
    exact mul_le_mul_of_nonneg_left hu.1 hBpos.le
  have hlogBu_gt : ∀ u ∈ Set.uIcc ((m : ℝ) / ((m : ℝ) + 1)) 1,
      1 < Real.log (B * u) := by
    intro u hu
    have h1 : Real.log A ≤ Real.log (B * u) := Real.log_le_log hApos (hABu u hu)
    have h2 : 1 < Real.log A := by
      rw [Real.lt_log_iff_exp_lt hApos]
      exact hAexp_lt
    linarith
  have hpt : ∀ u ∈ Set.Icc ((m : ℝ) / ((m : ℝ) + 1)) 1,
      B * gpar (Lb k m / B) (B * u) ≤ ((Lb k m - 1) ^ 2 / La k m) * ((1 - u) ^ 2 / u) := by
    intro u hu
    have hu_ge : (m : ℝ) / ((m : ℝ) + 1) ≤ u := hu.1
    have hu_le_one : u ≤ 1 := hu.2
    have hu_pos : 0 < u := lt_of_lt_of_le (by positivity) hu_ge
    have hBu_pos : 0 < B * u := mul_pos hBpos hu_pos
    have hABu' : A ≤ B * u := by
      rw [← hBAm]
      exact mul_le_mul_of_nonneg_left hu_ge hBpos.le
    have hBu_exp : Real.exp 1 ≤ B * u := le_trans hAexp hABu'
    have hlogBu : La k m ≤ Real.log (B * u) := by
      rw [hLaA]
      exact Real.log_le_log hApos hABu'
    have hAub : Apar (Lb k m / B) (B * u) ≤ (1 - u) * (Lb k m - 1) := by
      have hlog : Real.log (B * u) = Real.log B + Real.log u :=
        Real.log_mul hBpos.ne' hu_pos.ne'
      have hcBu : Lb k m / B * (B * u) = u * Lb k m := by
        rw [hLbB]
        field_simp
      unfold Apar
      rw [hlog, hcBu, hLbB]
      have hlogu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu_pos
      nlinarith
    have hA0 : 0 ≤ Apar (Lb k m / B) (B * u) := by
      have h := Apar_nonneg (b := B) (t := B * u) hBexp hBu_exp
        (by nlinarith [hBpos.le, hu_le_one])
      have hc : Lb k m / B = Real.log B / B := by rw [hLbB]
      simpa [hc] using h
    have hnum : (Apar (Lb k m / B) (B * u)) ^ 2 ≤ ((1 - u) * (Lb k m - 1)) ^ 2 :=
      pow_le_pow_left₀ hA0 hAub 2
    have hden_le : (B * u) * La k m ≤ (B * u) * Real.log (B * u) :=
      mul_le_mul_of_nonneg_left hlogBu hBu_pos.le
    have hg : gpar (Lb k m / B) (B * u)
        ≤ ((1 - u) * (Lb k m - 1)) ^ 2 / ((B * u) * La k m) := by
      unfold gpar
      exact div_le_div₀ (sq_nonneg _) hnum (mul_pos hBu_pos hlapos) hden_le
    calc B * gpar (Lb k m / B) (B * u)
        ≤ B * (((1 - u) * (Lb k m - 1)) ^ 2 / ((B * u) * La k m)) :=
          mul_le_mul_of_nonneg_left hg hBpos.le
      _ = ((Lb k m - 1) ^ 2 / La k m) * ((1 - u) ^ 2 / u) := by
          field_simp
          try ring

  have hint1 : IntervalIntegrable (fun u : ℝ => gpar (Lb k m / B) (B * u)) volume
      ((m : ℝ) / ((m : ℝ) + 1)) 1 := by
    apply ContinuousOn.intervalIntegrable
    unfold gpar Apar
    apply ContinuousOn.div
    · apply ContinuousOn.pow
      apply ContinuousOn.sub
      · exact Real.continuousOn_log.comp (continuousOn_const.mul continuousOn_id)
          (fun u hu => (hmem u hu).ne')
      · exact continuousOn_const.mul (continuousOn_const.mul continuousOn_id)
    · apply ContinuousOn.mul
      · exact continuousOn_const.mul continuousOn_id
      · exact Real.continuousOn_log.comp (continuousOn_const.mul continuousOn_id)
          (fun u hu => (hmem u hu).ne')
    · intro u hu
      exact mul_ne_zero (hmem u hu).ne' (zero_lt_one.trans (hlogBu_gt u hu)).ne'
  have hint2 : IntervalIntegrable
      (fun u : ℝ => ((Lb k m - 1) ^ 2 / La k m) * ((1 - u) ^ 2 / u)) volume
      ((m : ℝ) / ((m : ℝ) + 1)) 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · exact continuousOn_const
    · apply ContinuousOn.div
      · fun_prop
      · exact continuousOn_id
      · intro u hu
        rw [Set.uIcc_of_le hfrac_le] at hu
        exact (lt_of_lt_of_le (by positivity) hu.1).ne'
  have hint1b : IntervalIntegrable (fun u : ℝ => B * gpar (Lb k m / B) (B * u))
      volume ((m : ℝ) / ((m : ℝ) + 1)) 1 := hint1.const_mul B
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) (a := (m : ℝ) / ((m : ℝ) + 1)) (b := 1) hfrac_le hint1b hint2
    (fun u hu => hpt u hu)
  calc B * ∫ u in (m : ℝ) / ((m : ℝ) + 1)..1, gpar (Lb k m / B) (B * u)
      = ∫ u in (m : ℝ) / ((m : ℝ) + 1)..1, B * gpar (Lb k m / B) (B * u) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ u in (m : ℝ) / ((m : ℝ) + 1)..1,
          ((Lb k m - 1) ^ 2 / La k m) * ((1 - u) ^ 2 / u) := hmono
    _ = ((Lb k m - 1) ^ 2 / La k m)
          * ∫ u in (m : ℝ) / ((m : ℝ) + 1)..1, (1 - u) ^ 2 / u := by
        rw [intervalIntegral.integral_const_mul]
    _ = ((Lb k m - 1) ^ 2 / La k m) * Jm m := by
        rw [Jm]

end RHLean.GateII.PrimePart



end Inline_GateII_PrimePart

section Inline_GateII_Stieltjes













open scoped BigOperators
open MeasureTheory
open Finset

namespace RHLean.GateII.Stieltjes



noncomputable def thetaJump (m : ℕ) : ℝ := if m.Prime then Real.log m else 0

theorem thetaJump_nonneg (m : ℕ) : 0 ≤ thetaJump m := by
  unfold thetaJump
  split
  · exact Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_lt ‹_›).le)
  · exact le_rfl


theorem sum_range_succ_thetaJump (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), thetaJump i = Chebyshev.theta ((n : ℕ) : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log n, Nat.primesLE_eq_filter_range,
    Finset.sum_filter]
  exact Finset.sum_congr rfl (fun i _ => by unfold thetaJump; rfl)


theorem sum_range_thetaJump {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range n, thetaJump i = Chebyshev.theta (((n - 1 : ℕ)) : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_comm, Nat.add_sub_cancel_left] using sum_range_succ_thetaJump k




theorem sum_Ico_thetaJump_mul (f : ℕ → ℝ) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ m ∈ Finset.Ico N (M + 1), f m * thetaJump m
      = f M * Chebyshev.theta ((M : ℕ) : ℝ)
        - f N * Chebyshev.theta (((N - 1 : ℕ)) : ℝ)
        - ∑ m ∈ Finset.Ico N M,
            (f (m + 1) - f m) * Chebyshev.theta ((m : ℕ) : ℝ) := by
  have hlt : N < M + 1 := Nat.lt_succ_of_le hNM
  have h := Finset.sum_Ico_by_parts (f := f) (g := thetaJump) hlt
  simp only [smul_eq_mul, Nat.add_sub_cancel] at h
  rw [h]
  have hG1 : ∑ i ∈ Finset.range (M + 1), thetaJump i
      = Chebyshev.theta ((M : ℕ) : ℝ) := sum_range_succ_thetaJump M
  have hG2 : ∑ i ∈ Finset.range N, thetaJump i
      = Chebyshev.theta (((N - 1 : ℕ)) : ℝ) := sum_range_thetaJump hN
  have hG3 : ∀ i : ℕ, ∑ j ∈ Finset.range (i + 1), thetaJump j
      = Chebyshev.theta ((i : ℕ) : ℝ) := fun i => sum_range_succ_thetaJump i
  simp only [hG1, hG2, hG3]




theorem sum_Ico_sub_mul_eq (f : ℕ → ℝ) {N M : ℕ} (hNM : N ≤ M) :
    ∑ m ∈ Finset.Ico N M, (f (m + 1) - f m) * (m : ℝ)
      = f M * ((M : ℝ) - 1) - f N * ((N : ℝ) - 1)
        - ∑ m ∈ Finset.Ico N M, f m := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [Nat.Ico_succ_right_eq_insert_Ico hNM, Finset.sum_insert, Finset.sum_insert, ih]
    · push_cast
      ring
    · simp [Finset.mem_Ico]
    · simp [Finset.mem_Ico]




theorem main_eq_sum_Icc (f : ℕ → ℝ) {N M : ℕ} (hNM : N ≤ M) :
    f M * (M : ℝ) - f N * ((N : ℝ) - 1)
        - ∑ m ∈ Finset.Ico N M, (f (m + 1) - f m) * (m : ℝ)
      = ∑ m ∈ Finset.Icc N M, f m := by
  rw [sum_Ico_sub_mul_eq f hNM, Finset.Icc_eq_cons_Ico hNM, Finset.sum_cons]
  ring


theorem sum_Ico_sub_eq (f : ℕ → ℝ) {N M : ℕ} (hNM : N ≤ M) :
    ∑ m ∈ Finset.Ico N M, (f (m + 1) - f m) = f M - f N := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [Nat.Ico_succ_right_eq_insert_Ico hNM, Finset.sum_insert, ih]
    · ring
    · simp [Finset.mem_Ico]




theorem sum_Icc_le_integral_add {g : ℝ → ℝ} {a b : ℝ} {N M : ℕ}
    (hN : N = ⌊a⌋₊ + 1) (hM : M = ⌊b⌋₊) (ha0 : 0 ≤ a) (hab : a ≤ b) (hNM : N ≤ M)
    (hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t)
    (hganti : AntitoneOn g (Set.Icc a b)) :
    ∑ m ∈ Finset.Icc N M, g (m : ℝ)
      ≤ (∫ t in a..b, g t) + (a - (N : ℝ) + 1) * g (N : ℝ) := by
  have haN : a ≤ (N : ℝ) := by
    rw [hN, Nat.cast_add, Nat.cast_one]
    exact (Nat.lt_floor_add_one a).le
  have hMb : (M : ℝ) ≤ b := by
    rw [hM]
    exact Nat.floor_le (by linarith)
  have hNM' : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  have hsubM : (N : ℝ) ≤ b := le_trans hNM' hMb

  have hint : ∀ x y : ℝ, x ∈ Set.Icc a b → y ∈ Set.Icc a b → IntervalIntegrable g volume x y := by
    intro x y hx hy
    refine (hganti.mono ?_).intervalIntegrable
    intro t ht
    rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans hx.1 h1, le_trans h2 hy.2⟩
    · exact ⟨le_trans hy.1 h1, le_trans h2 hx.2⟩

  have hIco1 : ((N : ℝ) - a) * g (N : ℝ) ≤ ∫ t in a..(N : ℝ), g t := by
    have huni : ∀ t ∈ Set.Icc a (N : ℝ), g (N : ℝ) ≤ g t := by
      intro t ht
      exact hganti ⟨ht.1, le_trans ht.2 hsubM⟩ ⟨haN, hsubM⟩ ht.2
    have h := intervalIntegral.integral_mono_on haN intervalIntegrable_const
      (hint a (N : ℝ) ⟨le_rfl, hab⟩ ⟨haN, hsubM⟩) huni
    rwa [intervalIntegral.integral_const, smul_eq_mul] at h

  have hsubIcc : ∀ k : ℕ, N ≤ k → k + 1 ≤ M →
      Set.uIcc (k : ℝ) (((k + 1 : ℕ)) : ℝ) ⊆ Set.Icc a b := by
    intro k hk1 hk2 t ht
    have hkN : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkM : ((k + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk2
    rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans haN (le_trans hkN h1), le_trans h2 (le_trans hkM hMb)⟩
    · exfalso
      have hcontra : (((k + 1 : ℕ)) : ℝ) ≤ (k : ℝ) := le_trans h1 h2
      have : ((k : ℝ) + 1) ≤ (k : ℝ) := by
        simpa [Nat.cast_add, Nat.cast_one] using hcontra
      linarith
  have hintK : ∀ k ∈ Set.Ico N M,
      IntervalIntegrable g volume (k : ℝ) (((k + 1 : ℕ)) : ℝ) :=
    fun k hk => (hganti.mono (hsubIcc k hk.1 (Nat.succ_le_of_lt hk.2))).intervalIntegrable
  have hIco2 : ∑ k ∈ Finset.Ico N M, g (((k + 1 : ℕ)) : ℝ)
      ≤ ∫ t in (N : ℝ)..(M : ℝ), g t := by
    have hterm : ∀ k ∈ Finset.Ico N M,
        g (((k + 1 : ℕ)) : ℝ) ≤ ∫ t in (k : ℝ)..(((k + 1 : ℕ)) : ℝ), g t := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
      have hk2' : k + 1 ≤ M := Nat.succ_le_of_lt hk2
      have hle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
      have ht' : ∀ t ∈ Set.Icc (k : ℝ) (((k + 1 : ℕ)) : ℝ),
          t ∈ Set.uIcc (k : ℝ) (((k + 1 : ℕ)) : ℝ) := by
        intro t ht
        rwa [Set.uIcc_of_le hle]
      have hk' : (((k + 1 : ℕ)) : ℝ) ∈ Set.uIcc (k : ℝ) (((k + 1 : ℕ)) : ℝ) := by
        rw [Set.uIcc_of_le hle]
        exact ⟨hle, le_rfl⟩
      have huni : ∀ t ∈ Set.Icc (k : ℝ) (((k + 1 : ℕ)) : ℝ),
          g (((k + 1 : ℕ)) : ℝ) ≤ g t := by
        intro t ht
        exact hganti (hsubIcc k hk1 hk2' (ht' t ht)) (hsubIcc k hk1 hk2' hk') ht.2
      have h := intervalIntegral.integral_mono_on hle intervalIntegrable_const
        (hintK k ⟨hk1, hk2⟩) huni
      simp only [intervalIntegral.integral_const, smul_eq_mul] at h
      have hsub1 : (((k + 1 : ℕ) : ℝ) - (k : ℝ)) * g (((k + 1 : ℕ)) : ℝ)
          = g (((k + 1 : ℕ)) : ℝ) := by
        have h1 : (((k + 1 : ℕ) : ℝ) - (k : ℝ)) = 1 := by push_cast; ring
        rw [h1, one_mul]
      rwa [hsub1] at h
    calc ∑ k ∈ Finset.Ico N M, g (((k + 1 : ℕ)) : ℝ)
        ≤ ∑ k ∈ Finset.Ico N M, ∫ t in (k : ℝ)..(((k + 1 : ℕ)) : ℝ), g t :=
          Finset.sum_le_sum hterm
      _ = ∫ t in (N : ℝ)..(M : ℝ), g t :=
          intervalIntegral.sum_integral_adjacent_intervals_Ico hNM hintK

  have h3 : 0 ≤ ∫ t in (M : ℝ)..b, g t :=
    intervalIntegral.integral_nonneg hMb
      (fun t ht => hg0 t ⟨le_trans haN (le_trans hNM' ht.1), ht.2⟩)

  have hs1 : (∫ t in a..(N : ℝ), g t) + (∫ t in (N : ℝ)..(M : ℝ), g t)
      = ∫ t in a..(M : ℝ), g t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint a (N : ℝ) ⟨le_rfl, hab⟩ ⟨haN, hsubM⟩)
      (hint (N : ℝ) (M : ℝ) ⟨haN, hsubM⟩ ⟨le_trans haN hNM', hMb⟩)
  have hs2 : (∫ t in a..(M : ℝ), g t) + (∫ t in (M : ℝ)..b, g t)
      = ∫ t in a..b, g t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint a (M : ℝ) ⟨le_rfl, hab⟩ ⟨le_trans haN hNM', hMb⟩)
      (hint (M : ℝ) b ⟨le_trans haN hNM', hMb⟩
        ⟨le_trans haN (le_trans hNM' hMb), le_rfl⟩)

  have hsum : ∑ m ∈ Finset.Icc N M, g (m : ℝ)
      = (∑ m ∈ Finset.Ico N M, g (((m + 1 : ℕ)) : ℝ)) + g (N : ℝ) := by
    have hsum1 : ∑ m ∈ Finset.Icc N M, g (m : ℝ)
        = g (M : ℝ) + ∑ m ∈ Finset.Ico N M, g (m : ℝ) := by
      rw [Finset.Icc_eq_cons_Ico hNM, Finset.sum_cons]
    have htel2 : (∑ m ∈ Finset.Ico N M, g (((m + 1 : ℕ)) : ℝ))
        - (∑ m ∈ Finset.Ico N M, g (m : ℝ)) = g (M : ℝ) - g (N : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      exact sum_Ico_sub_eq (fun m => g (m : ℝ)) hNM
    rw [hsum1]
    linarith
  rw [hsum]
  nlinarith [hIco1, hIco2, h3, hs1, hs2]







theorem sum_thetaJump_mul_identity (g : ℝ → ℝ) {a b : ℝ} {N M : ℕ}
    (hN : N = ⌊a⌋₊ + 1) (hM : M = ⌊b⌋₊) (hNM : N ≤ M) :
    ∑ m ∈ Finset.Ico N (M + 1), g (m : ℝ) * thetaJump m
      = (∑ m ∈ Finset.Icc N M, g (m : ℝ))
        + g (M : ℝ) * (Chebyshev.theta (M : ℝ) - (M : ℝ))
        - g (N : ℝ) * (Chebyshev.theta a - ((N : ℝ) - 1))
        - ∑ m ∈ Finset.Ico N M,
            (g (((m + 1 : ℕ)) : ℝ) - g (m : ℝ))
              * (Chebyshev.theta (m : ℝ) - (m : ℝ)) := by
  have hN1 : 1 ≤ N := by rw [hN]; omega
  have hNm1 : N - 1 = ⌊a⌋₊ := by omega
  have htN : Chebyshev.theta (((N - 1 : ℕ)) : ℝ) = Chebyshev.theta a := by
    rw [hNm1]
    exact (Chebyshev.theta_eq_theta_coe_floor a).symm
  rw [sum_Ico_thetaJump_mul (f := fun m : ℕ => g (m : ℝ)) hN1 hNM, htN]
  have hmain := main_eq_sum_Icc (fun m : ℕ => g (m : ℝ)) hNM
  have hsumE : ∑ m ∈ Finset.Ico N M,
        (g (((m + 1 : ℕ)) : ℝ) - g (m : ℝ)) * Chebyshev.theta (m : ℝ)
      = (∑ m ∈ Finset.Ico N M, (g (((m + 1 : ℕ)) : ℝ) - g (m : ℝ)) * (m : ℝ))
        + ∑ m ∈ Finset.Ico N M, (g (((m + 1 : ℕ)) : ℝ) - g (m : ℝ))
            * (Chebyshev.theta (m : ℝ) - (m : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  rw [hsumE]
  have hMexp : Chebyshev.theta (M : ℝ)
      = (M : ℝ) + (Chebyshev.theta (M : ℝ) - (M : ℝ)) := by ring
  have hNexp : Chebyshev.theta a
      = ((N : ℝ) - 1) + (Chebyshev.theta a - ((N : ℝ) - 1)) := by ring
  rw [hMexp, hNexp]
  linear_combination (norm := ring) hmain



theorem sum_primes_eq_sum_thetaJump (g : ℝ → ℝ) {a b : ℝ} (ha0 : 0 ≤ a) :
    ∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ => a < (p : ℝ)), g (p : ℝ) * Real.log (p : ℝ)
      = ∑ m ∈ Finset.Ico (⌊a⌋₊ + 1) (⌊b⌋₊ + 1), g (m : ℝ) * thetaJump m := by
  have ha_iff : ∀ p : ℕ, a < (p : ℝ) ↔ ⌊a⌋₊ < p := by
    intro p
    constructor
    · intro h
      by_contra hc
      have h1 : p ≤ ⌊a⌋₊ := Nat.le_of_not_lt hc
      have h2 : (p : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast h1
      have h3 : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha0
      linarith
    · intro h
      have h1 : ⌊a⌋₊ + 1 ≤ p := Nat.succ_le_of_lt h
      have h2 : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
      have h3 : ((⌊a⌋₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast h1
      have h4 : ((⌊a⌋₊ + 1 : ℕ) : ℝ) = (⌊a⌋₊ : ℝ) + 1 := by push_cast; ring
      linarith
  have hset : (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ => a < (p : ℝ))
      = (Finset.Ico (⌊a⌋₊ + 1) (⌊b⌋₊ + 1)).filter Nat.Prime := by
    ext p
    rw [Nat.primesLE_eq_filter_range]
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    have ha1 : ⌊a⌋₊ < p → ⌊a⌋₊ + 1 ≤ p := fun h => by omega
    have ha2 : ⌊a⌋₊ + 1 ≤ p → ⌊a⌋₊ < p := fun h => by omega
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨ha1 ((ha_iff p).mp h3), h1⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h2, h3⟩, (ha_iff p).mpr (ha2 h1)⟩
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases h : Nat.Prime m
  · simp [thetaJump, h]
  · simp [thetaJump, h]




theorem sum_thetaJump_mul_le {g : ℝ → ℝ} {a b Mq : ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t)
    (hganti : AntitoneOn g (Set.Icc a b))
    (hE : ∀ t ∈ Set.Icc a b, |Chebyshev.theta t - t| ≤ Mq) :
    ∑ m ∈ Finset.Ico (⌊a⌋₊ + 1) (⌊b⌋₊ + 1), g (m : ℝ) * thetaJump m
      ≤ (∫ t in a..b, g t) + 2 * Mq * g a := by
  by_cases hNM : ⌊a⌋₊ + 1 ≤ ⌊b⌋₊
  · set N : ℕ := ⌊a⌋₊ + 1 with hN
    set M : ℕ := ⌊b⌋₊ with hM
    have hNMc : N ≤ M := by rw [hN, hM]; exact hNM
    have haN : a ≤ (N : ℝ) := by
      rw [hN, Nat.cast_add, Nat.cast_one]
      exact (Nat.lt_floor_add_one a).le
    have hMb : (M : ℝ) ≤ b := by
      rw [hM]
      exact Nat.floor_le (by linarith)
    have hNM' : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNMc
    have hsubM : (N : ℝ) ≤ b := le_trans hNM' hMb
    have hEa : |Chebyshev.theta a - a| ≤ Mq := hE a ⟨le_rfl, hab⟩
    have hEM : |Chebyshev.theta (M : ℝ) - (M : ℝ)| ≤ Mq :=
      hE (M : ℝ) ⟨le_trans haN hNM', hMb⟩
    have hEm : ∀ m ∈ Finset.Ico N M,
        |Chebyshev.theta (m : ℝ) - (m : ℝ)| ≤ Mq := by
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
      refine hE (m : ℝ) ⟨le_trans haN (by exact_mod_cast hm1), ?_⟩
      exact le_trans (by exact_mod_cast (Nat.le_of_lt hm2) : (m : ℝ) ≤ (M : ℝ)) hMb
    have hg0N : 0 ≤ g (N : ℝ) := hg0 _ ⟨haN, hsubM⟩
    have hg0M : 0 ≤ g (M : ℝ) := hg0 _ ⟨le_trans haN hNM', hMb⟩
    have hga : 0 ≤ g a := hg0 a ⟨le_rfl, hab⟩
    have hMq0 : 0 ≤ Mq := le_trans (abs_nonneg _) hEa
    have hb1 : g (M : ℝ) * (Chebyshev.theta (M : ℝ) - (M : ℝ)) ≤ Mq * g (M : ℝ) := by
      have h := (abs_le.mp hEM).2
      nlinarith [hg0M]
    have hb2 : -(g (N : ℝ) * (Chebyshev.theta a - ((N : ℝ) - 1)))
        ≤ Mq * g (N : ℝ) - (a - (N : ℝ) + 1) * g (N : ℝ) := by
      have h1 : -(Mq) ≤ Chebyshev.theta a - a := (abs_le.mp hEa).1
      have h2 : -(Chebyshev.theta a - ((N : ℝ) - 1))
          ≤ Mq - (a - (N : ℝ) + 1) := by
        have h3 : a - (N : ℝ) + 1 = a - ((N : ℝ) - 1) := by ring
        linarith
      have h4 : -(g (N : ℝ) * (Chebyshev.theta a - ((N : ℝ) - 1)))
          = g (N : ℝ) * (-(Chebyshev.theta a - ((N : ℝ) - 1))) := by ring
      rw [h4]
      calc g (N : ℝ) * (-(Chebyshev.theta a - ((N : ℝ) - 1)))
          ≤ g (N : ℝ) * (Mq - (a - (N : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left h2 hg0N
        _ = Mq * g (N : ℝ) - (a - (N : ℝ) + 1) * g (N : ℝ) := by ring
    have hb3 : -(∑ m ∈ Finset.Ico N M,
          (g (((m + 1 : ℕ)) : ℝ) - g (m : ℝ)) * (Chebyshev.theta (m : ℝ) - (m : ℝ)))
        ≤ Mq * (g (N : ℝ) - g (M : ℝ)) := by
      have hterm : ∀ m ∈ Finset.Ico N M,
          -((g (((m + 1 : ℕ)) : ℝ) - g (m : ℝ))
              * (Chebyshev.theta (m : ℝ) - (m : ℝ)))
          ≤ Mq * (g (m : ℝ) - g (((m + 1 : ℕ)) : ℝ)) := by
        intro m hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
        have h1 : Chebyshev.theta (m : ℝ) - (m : ℝ) ≤ Mq := (abs_le.mp (hEm m hm)).2
        have hmR : (m : ℝ) ≤ b :=
          le_trans (by exact_mod_cast (Nat.le_of_lt hm2) : (m : ℝ) ≤ (M : ℝ)) hMb
        have hm1R : m + 1 ≤ M := Nat.succ_le_of_lt hm2
        have hm1b : (((m + 1 : ℕ)) : ℝ) ≤ b :=
          le_trans (by exact_mod_cast hm1R : (((m + 1 : ℕ)) : ℝ) ≤ (M : ℝ)) hMb
        have hgm : 0 ≤ g (m : ℝ) := hg0 _ ⟨le_trans haN (by exact_mod_cast hm1), hmR⟩
        have hm1N : (N : ℝ) ≤ (((m + 1 : ℕ)) : ℝ) := by
          exact_mod_cast (Nat.le_trans hm1 (Nat.le_succ m))
        have hgm1 : 0 ≤ g (((m + 1 : ℕ)) : ℝ) := hg0 _ ⟨le_trans haN hm1N, hm1b⟩
        have hmono : g (((m + 1 : ℕ)) : ℝ) ≤ g (m : ℝ) :=
          hganti ⟨le_trans haN (by exact_mod_cast hm1), hmR⟩
            ⟨le_trans haN hm1N, hm1b⟩ (by exact_mod_cast Nat.le_succ m)
        have hδ : 0 ≤ g (m : ℝ) - g (((m + 1 : ℕ)) : ℝ) := by linarith
        have h4 : -((g (((m + 1 : ℕ)) : ℝ) - g (m : ℝ))
            * (Chebyshev.theta (m : ℝ) - (m : ℝ)))
            = (g (m : ℝ) - g (((m + 1 : ℕ)) : ℝ))
              * (Chebyshev.theta (m : ℝ) - (m : ℝ)) := by ring
        rw [h4]
        calc (g (m : ℝ) - g (((m + 1 : ℕ)) : ℝ))
              * (Chebyshev.theta (m : ℝ) - (m : ℝ))
            ≤ (g (m : ℝ) - g (((m + 1 : ℕ)) : ℝ)) * Mq :=
              mul_le_mul_of_nonneg_left h1 hδ
          _ = Mq * (g (m : ℝ) - g (((m + 1 : ℕ)) : ℝ)) := by ring
      calc -(∑ m ∈ Finset.Ico N M, (g (((m + 1 : ℕ)) : ℝ) - g (m : ℝ))
              * (Chebyshev.theta (m : ℝ) - (m : ℝ)))
          = ∑ m ∈ Finset.Ico N M, -((g (((m + 1 : ℕ)) : ℝ) - g (m : ℝ))
              * (Chebyshev.theta (m : ℝ) - (m : ℝ))) := by rw [Finset.sum_neg_distrib]
        _ ≤ ∑ m ∈ Finset.Ico N M, Mq * (g (m : ℝ) - g (((m + 1 : ℕ)) : ℝ)) :=
            Finset.sum_le_sum hterm
        _ = Mq * (∑ m ∈ Finset.Ico N M, (g (m : ℝ) - g (((m + 1 : ℕ)) : ℝ))) := by
            rw [Finset.mul_sum]
        _ = Mq * (g (N : ℝ) - g (M : ℝ)) := by
            have hsub := sum_Ico_sub_eq (fun m : ℕ => g (m : ℝ)) hNMc
            have hsub' : (∑ m ∈ Finset.Ico N M, g (((m + 1 : ℕ)) : ℝ))
                - (∑ m ∈ Finset.Ico N M, g (m : ℝ)) = g (M : ℝ) - g (N : ℝ) := by
              rw [← Finset.sum_sub_distrib]
              exact hsub
            congr 1
            rw [Finset.sum_sub_distrib]
            linarith
    have hmulN : 2 * Mq * g (N : ℝ) ≤ 2 * Mq * g a := by
      have hgN : g (N : ℝ) ≤ g a := hganti ⟨le_rfl, hab⟩ ⟨haN, hsubM⟩ haN
      have h2 := mul_le_mul_of_nonneg_left hgN (by linarith : (0 : ℝ) ≤ 2 * Mq)
      linarith
    have hident := sum_thetaJump_mul_identity (g := g) hN hM hNMc
    rw [hident]
    have hInt := sum_Icc_le_integral_add (g := g) hN hM ha0 hab hNMc hg0 hganti
    linarith [hInt, hb1, hb2, hb3, hmulN]
  · have hempty : Finset.Ico (⌊a⌋₊ + 1) (⌊b⌋₊ + 1) = ∅ := by
      ext m
      simp only [Finset.mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩
        omega
      · intro h
        simp at h
    rw [hempty, Finset.sum_empty]
    have hEa : |Chebyshev.theta a - a| ≤ Mq := hE a ⟨le_rfl, hab⟩
    have hMq0 : 0 ≤ Mq := le_trans (abs_nonneg _) hEa
    have hga : 0 ≤ g a := hg0 a ⟨le_rfl, hab⟩
    have hi : 0 ≤ ∫ t in a..b, g t := intervalIntegral.integral_nonneg hab (fun t ht => hg0 t ht)
    have hprod : 0 ≤ 2 * Mq * g a := mul_nonneg (by linarith) hga
    linarith

end RHLean.GateII.Stieltjes



end Inline_GateII_Stieltjes

section Inline_GateII_EmData


















open Finset
open scoped BigOperators

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RHLean.GateII.EmData

open RHLean.GateII.AWGC
open RHLean.GateII.Sweep





theorem sum_Icc_inv_mul_le (a M : ℕ) (ha : 1 ≤ a) :
    ∑ m ∈ Finset.Icc a M, 1 / ((m : ℝ) * ((m : ℝ) + 1)) ≤ 1 / a := by
  by_cases hM : M < a
  · rw [Finset.Icc_eq_empty_of_lt hM]
    simp
  · have hM' : a ≤ M := not_lt.mp hM
    have htel : ∀ M : ℕ, a ≤ M →
        ∑ m ∈ Finset.Icc a M, 1 / ((m : ℝ) * ((m : ℝ) + 1))
          = 1 / (a : ℝ) - 1 / ((M : ℝ) + 1) := by
      intro M hM
      refine Nat.le_induction ?_ ?_ M hM
      · rw [Finset.Icc_self, Finset.sum_singleton]
        have ha0 : (a : ℝ) ≠ 0 := by positivity
        have ha1 : (a : ℝ) + 1 ≠ 0 := by positivity
        field_simp [ha0, ha1]
        ring
      · intro n hn ih
        rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hn), ih]
        push_cast
        have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
        have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
        have h3 : (a : ℝ) ≠ 0 := by positivity
        field_simp [h1, h2, h3]
        ring
    rw [htel M hM']
    have : 0 ≤ 1 / ((M : ℝ) + 1) := by positivity
    linarith



theorem Em_tail_term_le_of {L : ℝ} {a m : ℕ} (ha3 : 3 ≤ a) (hm : a ≤ m)
    (ha : Real.log 2.9 < L - Real.log ((m : ℝ) + 1)) :
    Em L m ≤ (40 / (27 * (1 - 1 / (a : ℝ)))) / ((m : ℝ) * ((m : ℝ) + 1)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmp0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hDm : Dm m = 5 := by
    unfold Dm
    rw [if_neg (by omega : ¬m ≤ 2)]
  set c : ℝ := 1 - Real.log (((m : ℝ) + 1) / (m : ℝ)) with hcdef
  have hratio_gt_one : 1 < ((m : ℝ) + 1) / (m : ℝ) := by
    rw [lt_div_iff₀ hm0]
    linarith
  have hlog_pos : 0 < Real.log (((m : ℝ) + 1) / (m : ℝ)) := Real.log_pos hratio_gt_one
  have hlog_le : Real.log (((m : ℝ) + 1) / (m : ℝ)) ≤ 1 / (m : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < ((m : ℝ) + 1) / (m : ℝ))
    have heq : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by
      field_simp
      ring
    linarith
  have hm_gt_one : 1 / (m : ℝ) < 1 := by
    rw [div_lt_one hm0]
    exact_mod_cast (by omega : 1 < m)
  have hc_pos : 0 < c := by
    rw [hcdef]
    linarith
  have hc_ge : 1 - 1 / (a : ℝ) ≤ c := by
    rw [hcdef]
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    have ham : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hle : 1 / (m : ℝ) ≤ 1 / (a : ℝ) := one_div_le_one_div_of_le haR ham
    linarith
  have hLa_eq : L - Real.log ((m : ℝ) + 1) = (L - Real.log (m : ℝ) - 1) + c := by
    have hlog : Real.log ((m : ℝ) + 1)
        = Real.log (m : ℝ) + Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
      have hmul : (m : ℝ) * (((m : ℝ) + 1) / (m : ℝ)) = (m : ℝ) + 1 := by
        field_simp
      conv_lhs => rw [← hmul]
      exact Real.log_mul hm0.ne' (by positivity : ((m : ℝ) + 1) / (m : ℝ) ≠ 0)
    rw [hcdef, hlog]
    ring
  have hlog29_gt_one : (1 : ℝ) < Real.log 2.9 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h := Real.exp_one_lt_d9
    norm_num at h ⊢
    linarith
  have hc_le_one : c ≤ 1 := by
    rw [hcdef]
    linarith [Real.log_nonneg hratio_gt_one.le]
  have hx_nonneg : 0 ≤ L - Real.log (m : ℝ) - 1 := by
    linarith [hLa_eq, ha, hc_le_one, hlog29_gt_one]
  have hden : 0 < (m : ℝ) * ((m : ℝ) + 1) := mul_pos hm0 hmp0
  have hconst_pos : 0 < 1 - 1 / (a : ℝ) := by
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    have : 1 / (a : ℝ) < 1 := by
      rw [div_lt_one haR]
      exact_mod_cast (by omega : 1 < a)
    linarith
  have hshape : (L - Real.log (m : ℝ) - 1) ^ 2
      / (L - Real.log ((m : ℝ) + 1)) ^ 3 ≤ 4 / (27 * (1 - 1 / (a : ℝ))) := by
    have h := sq_div_cube_le hx_nonneg hc_pos
    have hcb : 4 / (27 * c) ≤ 4 / (27 * (1 - 1 / (a : ℝ))) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hc_ge]
    rw [hLa_eq]
    linarith
  unfold Em
  rw [hDm]
  have hLa_pos : 0 < L - Real.log ((m : ℝ) + 1) := by
    linarith [hLa_eq, hx_nonneg, hc_pos]
  have hshape' : (L - Real.log (m : ℝ) - 1) ^ 2
      ≤ (4 / (27 * (1 - 1 / (a : ℝ)))) * (L - Real.log ((m : ℝ) + 1)) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hshape
      (by positivity : (0 : ℝ) ≤ (L - Real.log ((m : ℝ) + 1)) ^ 3)
    rwa [div_mul_cancel₀ _ (pow_ne_zero 3 hLa_pos.ne')] at h
  rw [div_le_div_iff₀
    (by positivity : 0 < (m : ℝ) * ((m : ℝ) + 1) * (L - Real.log ((m : ℝ) + 1)) ^ 3) hden]
  have hgoal : 2 * 5 * (L - Real.log (m : ℝ) - 1) ^ 2 * ((m : ℝ) * ((m : ℝ) + 1))
      ≤ (40 / (27 * (1 - 1 / (a : ℝ))))
          * ((m : ℝ) * ((m : ℝ) + 1) * (L - Real.log ((m : ℝ) + 1)) ^ 3) := by
    have hc0 : 0 ≤ 10 * ((m : ℝ) * ((m : ℝ) + 1)) := by positivity
    calc 2 * 5 * (L - Real.log (m : ℝ) - 1) ^ 2 * ((m : ℝ) * ((m : ℝ) + 1))
        = (10 * ((m : ℝ) * ((m : ℝ) + 1))) * (L - Real.log (m : ℝ) - 1) ^ 2 := by ring
      _ ≤ (10 * ((m : ℝ) * ((m : ℝ) + 1)))
            * ((4 / (27 * (1 - 1 / (a : ℝ)))) * (L - Real.log ((m : ℝ) + 1)) ^ 3) :=
          mul_le_mul_of_nonneg_left hshape' hc0
      _ = (40 / (27 * (1 - 1 / (a : ℝ))))
            * ((m : ℝ) * ((m : ℝ) + 1) * (L - Real.log ((m : ℝ) + 1)) ^ 3) := by ring
  exact hgoal


theorem Em_Icc_tail_le_of {L : ℝ} (a M : ℕ) (ha3 : 3 ≤ a)
    (hact : ∀ m ∈ Finset.Icc a M, Real.log 2.9 < L - Real.log ((m : ℝ) + 1)) :
    ∑ m ∈ Finset.Icc a M, Em L m ≤ 40 / (27 * ((a : ℝ) - 1)) := by
  have hterm : ∀ m ∈ Finset.Icc a M,
      Em L m ≤ (40 / (27 * (1 - 1 / (a : ℝ)))) * (1 / ((m : ℝ) * ((m : ℝ) + 1))) := by
    intro m hm
    have ham : a ≤ m := (Finset.mem_Icc.mp hm).1
    have h := Em_tail_term_le_of ha3 ham (hact m hm)
    rwa [div_eq_mul_one_div] at h
  have hconst : 0 ≤ 40 / (27 * (1 - 1 / (a : ℝ))) := by
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    have hlt : 1 / (a : ℝ) < 1 := by
      rw [div_lt_one haR]
      exact_mod_cast (by omega : 1 < a)
    exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) (by linarith))
  calc ∑ m ∈ Finset.Icc a M, Em L m
      ≤ ∑ m ∈ Finset.Icc a M,
          (40 / (27 * (1 - 1 / (a : ℝ)))) * (1 / ((m : ℝ) * ((m : ℝ) + 1))) :=
        Finset.sum_le_sum hterm
    _ = (40 / (27 * (1 - 1 / (a : ℝ))))
          * ∑ m ∈ Finset.Icc a M, 1 / ((m : ℝ) * ((m : ℝ) + 1)) := by
        rw [Finset.mul_sum]
    _ ≤ (40 / (27 * (1 - 1 / (a : ℝ)))) * (1 / a) :=
        mul_le_mul_of_nonneg_left (sum_Icc_inv_mul_le a M (by omega)) hconst
    _ = 40 / (27 * ((a : ℝ) - 1)) := by
        have ha0 : (a : ℝ) ≠ 0 := by positivity
        have ha1 : (a : ℝ) - 1 ≠ 0 := by
          have : (1 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 1 < a)
          linarith
        field_simp [ha0, ha1]




def log2lo : ℚ := 693147 / 10 ^ 6


def log2hi : ℚ := 693148 / 10 ^ 6

theorem log2lo_le : (log2lo : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num [log2lo] at h ⊢
  linarith

theorem log2hi_ge : Real.log 2 ≤ (log2hi : ℝ) := by
  have h := Real.log_two_lt_d9
  norm_num [log2hi] at h ⊢
  linarith


noncomputable def loOf : ℕ → ℚ
  | 2 => logLo log2lo 1 5 (0 : ℚ)
  | 3 => logLo log2lo 1 5 ((1 : ℚ) / 5)
  | 4 => logLo log2lo 2 5 (0 : ℚ)
  | 5 => logLo log2lo 2 5 ((1 : ℚ) / 9)
  | 6 => logLo log2lo 2 5 ((1 : ℚ) / 5)
  | 7 => logLo log2lo 2 5 ((3 : ℚ) / 11)
  | 8 => logLo log2lo 3 5 (0 : ℚ)
  | 9 => logLo log2lo 3 5 ((1 : ℚ) / 17)
  | 10 => logLo log2lo 3 5 ((1 : ℚ) / 9)
  | 11 => logLo log2lo 3 5 ((3 : ℚ) / 19)
  | 12 => logLo log2lo 3 5 ((1 : ℚ) / 5)
  | 13 => logLo log2lo 3 5 ((5 : ℚ) / 21)
  | 14 => logLo log2lo 3 5 ((3 : ℚ) / 11)
  | 15 => logLo log2lo 3 5 ((7 : ℚ) / 23)
  | 16 => logLo log2lo 4 5 (0 : ℚ)
  | 17 => logLo log2lo 4 5 ((1 : ℚ) / 33)
  | 18 => logLo log2lo 4 5 ((1 : ℚ) / 17)
  | 19 => logLo log2lo 4 5 ((3 : ℚ) / 35)
  | 20 => logLo log2lo 4 5 ((1 : ℚ) / 9)
  | 21 => logLo log2lo 4 5 ((5 : ℚ) / 37)
  | 22 => logLo log2lo 4 5 ((3 : ℚ) / 19)
  | 23 => logLo log2lo 4 5 ((7 : ℚ) / 39)
  | 24 => logLo log2lo 4 5 ((1 : ℚ) / 5)
  | 25 => logLo log2lo 4 5 ((9 : ℚ) / 41)
  | 26 => logLo log2lo 4 5 ((5 : ℚ) / 21)
  | 27 => logLo log2lo 4 5 ((11 : ℚ) / 43)
  | 28 => logLo log2lo 4 5 ((3 : ℚ) / 11)
  | 29 => logLo log2lo 4 5 ((13 : ℚ) / 45)
  | 30 => logLo log2lo 4 5 ((7 : ℚ) / 23)
  | 31 => logLo log2lo 4 5 ((15 : ℚ) / 47)
  | 32 => logLo log2lo 5 5 (0 : ℚ)
  | 33 => logLo log2lo 5 5 ((1 : ℚ) / 65)
  | 34 => logLo log2lo 5 5 ((1 : ℚ) / 33)
  | 35 => logLo log2lo 5 5 ((3 : ℚ) / 67)
  | 36 => logLo log2lo 5 5 ((1 : ℚ) / 17)
  | 37 => logLo log2lo 5 5 ((5 : ℚ) / 69)
  | 38 => logLo log2lo 5 5 ((3 : ℚ) / 35)
  | 39 => logLo log2lo 5 5 ((7 : ℚ) / 71)
  | 40 => logLo log2lo 5 5 ((1 : ℚ) / 9)
  | 41 => logLo log2lo 5 5 ((9 : ℚ) / 73)
  | 42 => logLo log2lo 5 5 ((5 : ℚ) / 37)
  | 43 => logLo log2lo 5 5 ((11 : ℚ) / 75)
  | 44 => logLo log2lo 5 5 ((3 : ℚ) / 19)
  | 45 => logLo log2lo 5 5 ((13 : ℚ) / 77)
  | 46 => logLo log2lo 5 5 ((7 : ℚ) / 39)
  | 47 => logLo log2lo 5 5 ((15 : ℚ) / 79)
  | 48 => logLo log2lo 5 5 ((1 : ℚ) / 5)
  | 49 => logLo log2lo 5 5 ((17 : ℚ) / 81)
  | 50 => logLo log2lo 5 5 ((9 : ℚ) / 41)
  | 51 => logLo log2lo 5 5 ((19 : ℚ) / 83)
  | 52 => logLo log2lo 5 5 ((5 : ℚ) / 21)
  | 53 => logLo log2lo 5 5 ((21 : ℚ) / 85)
  | 54 => logLo log2lo 5 5 ((11 : ℚ) / 43)
  | 55 => logLo log2lo 5 5 ((23 : ℚ) / 87)
  | 56 => logLo log2lo 5 5 ((3 : ℚ) / 11)
  | 57 => logLo log2lo 5 5 ((25 : ℚ) / 89)
  | 58 => logLo log2lo 5 5 ((13 : ℚ) / 45)
  | 59 => logLo log2lo 5 5 ((27 : ℚ) / 91)
  | 60 => logLo log2lo 5 5 ((7 : ℚ) / 23)
  | 61 => logLo log2lo 5 5 ((29 : ℚ) / 93)
  | 62 => logLo log2lo 5 5 ((15 : ℚ) / 47)
  | 63 => logLo log2lo 5 5 ((31 : ℚ) / 95)
  | 64 => logLo log2lo 6 5 (0 : ℚ)
  | 65 => logLo log2lo 6 5 ((1 : ℚ) / 129)
  | 66 => logLo log2lo 6 5 ((1 : ℚ) / 65)
  | 67 => logLo log2lo 6 5 ((3 : ℚ) / 131)
  | 68 => logLo log2lo 6 5 ((1 : ℚ) / 33)
  | 69 => logLo log2lo 6 5 ((5 : ℚ) / 133)
  | 70 => logLo log2lo 6 5 ((3 : ℚ) / 67)
  | 71 => logLo log2lo 6 5 ((7 : ℚ) / 135)
  | 72 => logLo log2lo 6 5 ((1 : ℚ) / 17)
  | 73 => logLo log2lo 6 5 ((9 : ℚ) / 137)
  | 74 => logLo log2lo 6 5 ((5 : ℚ) / 69)
  | 75 => logLo log2lo 6 5 ((11 : ℚ) / 139)
  | 76 => logLo log2lo 6 5 ((3 : ℚ) / 35)
  | 77 => logLo log2lo 6 5 ((13 : ℚ) / 141)
  | 78 => logLo log2lo 6 5 ((7 : ℚ) / 71)
  | 79 => logLo log2lo 6 5 ((15 : ℚ) / 143)
  | 80 => logLo log2lo 6 5 ((1 : ℚ) / 9)
  | 81 => logLo log2lo 6 5 ((17 : ℚ) / 145)
  | 82 => logLo log2lo 6 5 ((9 : ℚ) / 73)
  | 83 => logLo log2lo 6 5 ((19 : ℚ) / 147)
  | 84 => logLo log2lo 6 5 ((5 : ℚ) / 37)
  | 85 => logLo log2lo 6 5 ((21 : ℚ) / 149)
  | 86 => logLo log2lo 6 5 ((11 : ℚ) / 75)
  | 87 => logLo log2lo 6 5 ((23 : ℚ) / 151)
  | 88 => logLo log2lo 6 5 ((3 : ℚ) / 19)
  | 89 => logLo log2lo 6 5 ((25 : ℚ) / 153)
  | 90 => logLo log2lo 6 5 ((13 : ℚ) / 77)
  | 91 => logLo log2lo 6 5 ((27 : ℚ) / 155)
  | 92 => logLo log2lo 6 5 ((7 : ℚ) / 39)
  | 93 => logLo log2lo 6 5 ((29 : ℚ) / 157)
  | 94 => logLo log2lo 6 5 ((15 : ℚ) / 79)
  | 95 => logLo log2lo 6 5 ((31 : ℚ) / 159)
  | 96 => logLo log2lo 6 5 ((1 : ℚ) / 5)
  | 97 => logLo log2lo 6 5 ((33 : ℚ) / 161)
  | 98 => logLo log2lo 6 5 ((17 : ℚ) / 81)
  | 99 => logLo log2lo 6 5 ((35 : ℚ) / 163)
  | 100 => logLo log2lo 6 5 ((9 : ℚ) / 41)
  | 101 => logLo log2lo 6 5 ((37 : ℚ) / 165)
  | 102 => logLo log2lo 6 5 ((19 : ℚ) / 83)
  | 103 => logLo log2lo 6 5 ((39 : ℚ) / 167)
  | 104 => logLo log2lo 6 5 ((5 : ℚ) / 21)
  | 105 => logLo log2lo 6 5 ((41 : ℚ) / 169)
  | 106 => logLo log2lo 6 5 ((21 : ℚ) / 85)
  | 107 => logLo log2lo 6 5 ((43 : ℚ) / 171)
  | 108 => logLo log2lo 6 5 ((11 : ℚ) / 43)
  | 109 => logLo log2lo 6 5 ((45 : ℚ) / 173)
  | 110 => logLo log2lo 6 5 ((23 : ℚ) / 87)
  | 111 => logLo log2lo 6 5 ((47 : ℚ) / 175)
  | 112 => logLo log2lo 6 5 ((3 : ℚ) / 11)
  | 113 => logLo log2lo 6 5 ((49 : ℚ) / 177)
  | 114 => logLo log2lo 6 5 ((25 : ℚ) / 89)
  | 115 => logLo log2lo 6 5 ((51 : ℚ) / 179)
  | 116 => logLo log2lo 6 5 ((13 : ℚ) / 45)
  | 117 => logLo log2lo 6 5 ((53 : ℚ) / 181)
  | 118 => logLo log2lo 6 5 ((27 : ℚ) / 91)
  | 119 => logLo log2lo 6 5 ((55 : ℚ) / 183)
  | 120 => logLo log2lo 6 5 ((7 : ℚ) / 23)
  | 121 => logLo log2lo 6 5 ((57 : ℚ) / 185)
  | 122 => logLo log2lo 6 5 ((29 : ℚ) / 93)
  | 123 => logLo log2lo 6 5 ((59 : ℚ) / 187)
  | 124 => logLo log2lo 6 5 ((15 : ℚ) / 47)
  | 125 => logLo log2lo 6 5 ((61 : ℚ) / 189)
  | 126 => logLo log2lo 6 5 ((31 : ℚ) / 95)
  | 127 => logLo log2lo 6 5 ((63 : ℚ) / 191)
  | 128 => logLo log2lo 7 5 (0 : ℚ)
  | 129 => logLo log2lo 7 5 ((1 : ℚ) / 257)
  | 130 => logLo log2lo 7 5 ((1 : ℚ) / 129)
  | 131 => logLo log2lo 7 5 ((3 : ℚ) / 259)
  | 132 => logLo log2lo 7 5 ((1 : ℚ) / 65)
  | 133 => logLo log2lo 7 5 ((5 : ℚ) / 261)
  | 134 => logLo log2lo 7 5 ((3 : ℚ) / 131)
  | 135 => logLo log2lo 7 5 ((7 : ℚ) / 263)
  | 136 => logLo log2lo 7 5 ((1 : ℚ) / 33)
  | 137 => logLo log2lo 7 5 ((9 : ℚ) / 265)
  | 138 => logLo log2lo 7 5 ((5 : ℚ) / 133)
  | 139 => logLo log2lo 7 5 ((11 : ℚ) / 267)
  | 140 => logLo log2lo 7 5 ((3 : ℚ) / 67)
  | 141 => logLo log2lo 7 5 ((13 : ℚ) / 269)
  | 142 => logLo log2lo 7 5 ((7 : ℚ) / 135)
  | 143 => logLo log2lo 7 5 ((15 : ℚ) / 271)
  | 144 => logLo log2lo 7 5 ((1 : ℚ) / 17)
  | 145 => logLo log2lo 7 5 ((17 : ℚ) / 273)
  | 146 => logLo log2lo 7 5 ((9 : ℚ) / 137)
  | 147 => logLo log2lo 7 5 ((19 : ℚ) / 275)
  | 148 => logLo log2lo 7 5 ((5 : ℚ) / 69)
  | 149 => logLo log2lo 7 5 ((21 : ℚ) / 277)
  | 150 => logLo log2lo 7 5 ((11 : ℚ) / 139)
  | 151 => logLo log2lo 7 5 ((23 : ℚ) / 279)
  | 152 => logLo log2lo 7 5 ((3 : ℚ) / 35)
  | 153 => logLo log2lo 7 5 ((25 : ℚ) / 281)
  | 154 => logLo log2lo 7 5 ((13 : ℚ) / 141)
  | 155 => logLo log2lo 7 5 ((27 : ℚ) / 283)
  | 156 => logLo log2lo 7 5 ((7 : ℚ) / 71)
  | 157 => logLo log2lo 7 5 ((29 : ℚ) / 285)
  | 158 => logLo log2lo 7 5 ((15 : ℚ) / 143)
  | 159 => logLo log2lo 7 5 ((31 : ℚ) / 287)
  | 160 => logLo log2lo 7 5 ((1 : ℚ) / 9)
  | 161 => logLo log2lo 7 5 ((33 : ℚ) / 289)
  | 162 => logLo log2lo 7 5 ((17 : ℚ) / 145)
  | 163 => logLo log2lo 7 5 ((35 : ℚ) / 291)
  | 164 => logLo log2lo 7 5 ((9 : ℚ) / 73)
  | 165 => logLo log2lo 7 5 ((37 : ℚ) / 293)
  | 166 => logLo log2lo 7 5 ((19 : ℚ) / 147)
  | 167 => logLo log2lo 7 5 ((39 : ℚ) / 295)
  | 168 => logLo log2lo 7 5 ((5 : ℚ) / 37)
  | 169 => logLo log2lo 7 5 ((41 : ℚ) / 297)
  | 170 => logLo log2lo 7 5 ((21 : ℚ) / 149)
  | 171 => logLo log2lo 7 5 ((43 : ℚ) / 299)
  | 172 => logLo log2lo 7 5 ((11 : ℚ) / 75)
  | 173 => logLo log2lo 7 5 ((45 : ℚ) / 301)
  | 174 => logLo log2lo 7 5 ((23 : ℚ) / 151)
  | 175 => logLo log2lo 7 5 ((47 : ℚ) / 303)
  | 176 => logLo log2lo 7 5 ((3 : ℚ) / 19)
  | 177 => logLo log2lo 7 5 ((49 : ℚ) / 305)
  | 178 => logLo log2lo 7 5 ((25 : ℚ) / 153)
  | 179 => logLo log2lo 7 5 ((51 : ℚ) / 307)
  | 180 => logLo log2lo 7 5 ((13 : ℚ) / 77)
  | 181 => logLo log2lo 7 5 ((53 : ℚ) / 309)
  | 182 => logLo log2lo 7 5 ((27 : ℚ) / 155)
  | 183 => logLo log2lo 7 5 ((55 : ℚ) / 311)
  | 184 => logLo log2lo 7 5 ((7 : ℚ) / 39)
  | 185 => logLo log2lo 7 5 ((57 : ℚ) / 313)
  | 186 => logLo log2lo 7 5 ((29 : ℚ) / 157)
  | 187 => logLo log2lo 7 5 ((59 : ℚ) / 315)
  | 188 => logLo log2lo 7 5 ((15 : ℚ) / 79)
  | 189 => logLo log2lo 7 5 ((61 : ℚ) / 317)
  | 190 => logLo log2lo 7 5 ((31 : ℚ) / 159)
  | 191 => logLo log2lo 7 5 ((63 : ℚ) / 319)
  | 192 => logLo log2lo 7 5 ((1 : ℚ) / 5)
  | 193 => logLo log2lo 7 5 ((65 : ℚ) / 321)
  | 194 => logLo log2lo 7 5 ((33 : ℚ) / 161)
  | 195 => logLo log2lo 7 5 ((67 : ℚ) / 323)
  | 196 => logLo log2lo 7 5 ((17 : ℚ) / 81)
  | 197 => logLo log2lo 7 5 ((69 : ℚ) / 325)
  | 198 => logLo log2lo 7 5 ((35 : ℚ) / 163)
  | 199 => logLo log2lo 7 5 ((71 : ℚ) / 327)
  | 200 => logLo log2lo 7 5 ((9 : ℚ) / 41)
  | 201 => logLo log2lo 7 5 ((73 : ℚ) / 329)
  | _ => 0


noncomputable def hiOf : ℕ → ℚ
  | 2 => logHi log2hi 1 5 (0 : ℚ)
  | 3 => logHi log2hi 1 5 ((1 : ℚ) / 5)
  | 4 => logHi log2hi 2 5 (0 : ℚ)
  | 5 => logHi log2hi 2 5 ((1 : ℚ) / 9)
  | 6 => logHi log2hi 2 5 ((1 : ℚ) / 5)
  | 7 => logHi log2hi 2 5 ((3 : ℚ) / 11)
  | 8 => logHi log2hi 3 5 (0 : ℚ)
  | 9 => logHi log2hi 3 5 ((1 : ℚ) / 17)
  | 10 => logHi log2hi 3 5 ((1 : ℚ) / 9)
  | 11 => logHi log2hi 3 5 ((3 : ℚ) / 19)
  | 12 => logHi log2hi 3 5 ((1 : ℚ) / 5)
  | 13 => logHi log2hi 3 5 ((5 : ℚ) / 21)
  | 14 => logHi log2hi 3 5 ((3 : ℚ) / 11)
  | 15 => logHi log2hi 3 5 ((7 : ℚ) / 23)
  | 16 => logHi log2hi 4 5 (0 : ℚ)
  | 17 => logHi log2hi 4 5 ((1 : ℚ) / 33)
  | 18 => logHi log2hi 4 5 ((1 : ℚ) / 17)
  | 19 => logHi log2hi 4 5 ((3 : ℚ) / 35)
  | 20 => logHi log2hi 4 5 ((1 : ℚ) / 9)
  | 21 => logHi log2hi 4 5 ((5 : ℚ) / 37)
  | 22 => logHi log2hi 4 5 ((3 : ℚ) / 19)
  | 23 => logHi log2hi 4 5 ((7 : ℚ) / 39)
  | 24 => logHi log2hi 4 5 ((1 : ℚ) / 5)
  | 25 => logHi log2hi 4 5 ((9 : ℚ) / 41)
  | 26 => logHi log2hi 4 5 ((5 : ℚ) / 21)
  | 27 => logHi log2hi 4 5 ((11 : ℚ) / 43)
  | 28 => logHi log2hi 4 5 ((3 : ℚ) / 11)
  | 29 => logHi log2hi 4 5 ((13 : ℚ) / 45)
  | 30 => logHi log2hi 4 5 ((7 : ℚ) / 23)
  | 31 => logHi log2hi 4 5 ((15 : ℚ) / 47)
  | 32 => logHi log2hi 5 5 (0 : ℚ)
  | 33 => logHi log2hi 5 5 ((1 : ℚ) / 65)
  | 34 => logHi log2hi 5 5 ((1 : ℚ) / 33)
  | 35 => logHi log2hi 5 5 ((3 : ℚ) / 67)
  | 36 => logHi log2hi 5 5 ((1 : ℚ) / 17)
  | 37 => logHi log2hi 5 5 ((5 : ℚ) / 69)
  | 38 => logHi log2hi 5 5 ((3 : ℚ) / 35)
  | 39 => logHi log2hi 5 5 ((7 : ℚ) / 71)
  | 40 => logHi log2hi 5 5 ((1 : ℚ) / 9)
  | 41 => logHi log2hi 5 5 ((9 : ℚ) / 73)
  | 42 => logHi log2hi 5 5 ((5 : ℚ) / 37)
  | 43 => logHi log2hi 5 5 ((11 : ℚ) / 75)
  | 44 => logHi log2hi 5 5 ((3 : ℚ) / 19)
  | 45 => logHi log2hi 5 5 ((13 : ℚ) / 77)
  | 46 => logHi log2hi 5 5 ((7 : ℚ) / 39)
  | 47 => logHi log2hi 5 5 ((15 : ℚ) / 79)
  | 48 => logHi log2hi 5 5 ((1 : ℚ) / 5)
  | 49 => logHi log2hi 5 5 ((17 : ℚ) / 81)
  | 50 => logHi log2hi 5 5 ((9 : ℚ) / 41)
  | 51 => logHi log2hi 5 5 ((19 : ℚ) / 83)
  | 52 => logHi log2hi 5 5 ((5 : ℚ) / 21)
  | 53 => logHi log2hi 5 5 ((21 : ℚ) / 85)
  | 54 => logHi log2hi 5 5 ((11 : ℚ) / 43)
  | 55 => logHi log2hi 5 5 ((23 : ℚ) / 87)
  | 56 => logHi log2hi 5 5 ((3 : ℚ) / 11)
  | 57 => logHi log2hi 5 5 ((25 : ℚ) / 89)
  | 58 => logHi log2hi 5 5 ((13 : ℚ) / 45)
  | 59 => logHi log2hi 5 5 ((27 : ℚ) / 91)
  | 60 => logHi log2hi 5 5 ((7 : ℚ) / 23)
  | 61 => logHi log2hi 5 5 ((29 : ℚ) / 93)
  | 62 => logHi log2hi 5 5 ((15 : ℚ) / 47)
  | 63 => logHi log2hi 5 5 ((31 : ℚ) / 95)
  | 64 => logHi log2hi 6 5 (0 : ℚ)
  | 65 => logHi log2hi 6 5 ((1 : ℚ) / 129)
  | 66 => logHi log2hi 6 5 ((1 : ℚ) / 65)
  | 67 => logHi log2hi 6 5 ((3 : ℚ) / 131)
  | 68 => logHi log2hi 6 5 ((1 : ℚ) / 33)
  | 69 => logHi log2hi 6 5 ((5 : ℚ) / 133)
  | 70 => logHi log2hi 6 5 ((3 : ℚ) / 67)
  | 71 => logHi log2hi 6 5 ((7 : ℚ) / 135)
  | 72 => logHi log2hi 6 5 ((1 : ℚ) / 17)
  | 73 => logHi log2hi 6 5 ((9 : ℚ) / 137)
  | 74 => logHi log2hi 6 5 ((5 : ℚ) / 69)
  | 75 => logHi log2hi 6 5 ((11 : ℚ) / 139)
  | 76 => logHi log2hi 6 5 ((3 : ℚ) / 35)
  | 77 => logHi log2hi 6 5 ((13 : ℚ) / 141)
  | 78 => logHi log2hi 6 5 ((7 : ℚ) / 71)
  | 79 => logHi log2hi 6 5 ((15 : ℚ) / 143)
  | 80 => logHi log2hi 6 5 ((1 : ℚ) / 9)
  | 81 => logHi log2hi 6 5 ((17 : ℚ) / 145)
  | 82 => logHi log2hi 6 5 ((9 : ℚ) / 73)
  | 83 => logHi log2hi 6 5 ((19 : ℚ) / 147)
  | 84 => logHi log2hi 6 5 ((5 : ℚ) / 37)
  | 85 => logHi log2hi 6 5 ((21 : ℚ) / 149)
  | 86 => logHi log2hi 6 5 ((11 : ℚ) / 75)
  | 87 => logHi log2hi 6 5 ((23 : ℚ) / 151)
  | 88 => logHi log2hi 6 5 ((3 : ℚ) / 19)
  | 89 => logHi log2hi 6 5 ((25 : ℚ) / 153)
  | 90 => logHi log2hi 6 5 ((13 : ℚ) / 77)
  | 91 => logHi log2hi 6 5 ((27 : ℚ) / 155)
  | 92 => logHi log2hi 6 5 ((7 : ℚ) / 39)
  | 93 => logHi log2hi 6 5 ((29 : ℚ) / 157)
  | 94 => logHi log2hi 6 5 ((15 : ℚ) / 79)
  | 95 => logHi log2hi 6 5 ((31 : ℚ) / 159)
  | 96 => logHi log2hi 6 5 ((1 : ℚ) / 5)
  | 97 => logHi log2hi 6 5 ((33 : ℚ) / 161)
  | 98 => logHi log2hi 6 5 ((17 : ℚ) / 81)
  | 99 => logHi log2hi 6 5 ((35 : ℚ) / 163)
  | 100 => logHi log2hi 6 5 ((9 : ℚ) / 41)
  | 101 => logHi log2hi 6 5 ((37 : ℚ) / 165)
  | 102 => logHi log2hi 6 5 ((19 : ℚ) / 83)
  | 103 => logHi log2hi 6 5 ((39 : ℚ) / 167)
  | 104 => logHi log2hi 6 5 ((5 : ℚ) / 21)
  | 105 => logHi log2hi 6 5 ((41 : ℚ) / 169)
  | 106 => logHi log2hi 6 5 ((21 : ℚ) / 85)
  | 107 => logHi log2hi 6 5 ((43 : ℚ) / 171)
  | 108 => logHi log2hi 6 5 ((11 : ℚ) / 43)
  | 109 => logHi log2hi 6 5 ((45 : ℚ) / 173)
  | 110 => logHi log2hi 6 5 ((23 : ℚ) / 87)
  | 111 => logHi log2hi 6 5 ((47 : ℚ) / 175)
  | 112 => logHi log2hi 6 5 ((3 : ℚ) / 11)
  | 113 => logHi log2hi 6 5 ((49 : ℚ) / 177)
  | 114 => logHi log2hi 6 5 ((25 : ℚ) / 89)
  | 115 => logHi log2hi 6 5 ((51 : ℚ) / 179)
  | 116 => logHi log2hi 6 5 ((13 : ℚ) / 45)
  | 117 => logHi log2hi 6 5 ((53 : ℚ) / 181)
  | 118 => logHi log2hi 6 5 ((27 : ℚ) / 91)
  | 119 => logHi log2hi 6 5 ((55 : ℚ) / 183)
  | 120 => logHi log2hi 6 5 ((7 : ℚ) / 23)
  | 121 => logHi log2hi 6 5 ((57 : ℚ) / 185)
  | 122 => logHi log2hi 6 5 ((29 : ℚ) / 93)
  | 123 => logHi log2hi 6 5 ((59 : ℚ) / 187)
  | 124 => logHi log2hi 6 5 ((15 : ℚ) / 47)
  | 125 => logHi log2hi 6 5 ((61 : ℚ) / 189)
  | 126 => logHi log2hi 6 5 ((31 : ℚ) / 95)
  | 127 => logHi log2hi 6 5 ((63 : ℚ) / 191)
  | 128 => logHi log2hi 7 5 (0 : ℚ)
  | 129 => logHi log2hi 7 5 ((1 : ℚ) / 257)
  | 130 => logHi log2hi 7 5 ((1 : ℚ) / 129)
  | 131 => logHi log2hi 7 5 ((3 : ℚ) / 259)
  | 132 => logHi log2hi 7 5 ((1 : ℚ) / 65)
  | 133 => logHi log2hi 7 5 ((5 : ℚ) / 261)
  | 134 => logHi log2hi 7 5 ((3 : ℚ) / 131)
  | 135 => logHi log2hi 7 5 ((7 : ℚ) / 263)
  | 136 => logHi log2hi 7 5 ((1 : ℚ) / 33)
  | 137 => logHi log2hi 7 5 ((9 : ℚ) / 265)
  | 138 => logHi log2hi 7 5 ((5 : ℚ) / 133)
  | 139 => logHi log2hi 7 5 ((11 : ℚ) / 267)
  | 140 => logHi log2hi 7 5 ((3 : ℚ) / 67)
  | 141 => logHi log2hi 7 5 ((13 : ℚ) / 269)
  | 142 => logHi log2hi 7 5 ((7 : ℚ) / 135)
  | 143 => logHi log2hi 7 5 ((15 : ℚ) / 271)
  | 144 => logHi log2hi 7 5 ((1 : ℚ) / 17)
  | 145 => logHi log2hi 7 5 ((17 : ℚ) / 273)
  | 146 => logHi log2hi 7 5 ((9 : ℚ) / 137)
  | 147 => logHi log2hi 7 5 ((19 : ℚ) / 275)
  | 148 => logHi log2hi 7 5 ((5 : ℚ) / 69)
  | 149 => logHi log2hi 7 5 ((21 : ℚ) / 277)
  | 150 => logHi log2hi 7 5 ((11 : ℚ) / 139)
  | 151 => logHi log2hi 7 5 ((23 : ℚ) / 279)
  | 152 => logHi log2hi 7 5 ((3 : ℚ) / 35)
  | 153 => logHi log2hi 7 5 ((25 : ℚ) / 281)
  | 154 => logHi log2hi 7 5 ((13 : ℚ) / 141)
  | 155 => logHi log2hi 7 5 ((27 : ℚ) / 283)
  | 156 => logHi log2hi 7 5 ((7 : ℚ) / 71)
  | 157 => logHi log2hi 7 5 ((29 : ℚ) / 285)
  | 158 => logHi log2hi 7 5 ((15 : ℚ) / 143)
  | 159 => logHi log2hi 7 5 ((31 : ℚ) / 287)
  | 160 => logHi log2hi 7 5 ((1 : ℚ) / 9)
  | 161 => logHi log2hi 7 5 ((33 : ℚ) / 289)
  | 162 => logHi log2hi 7 5 ((17 : ℚ) / 145)
  | 163 => logHi log2hi 7 5 ((35 : ℚ) / 291)
  | 164 => logHi log2hi 7 5 ((9 : ℚ) / 73)
  | 165 => logHi log2hi 7 5 ((37 : ℚ) / 293)
  | 166 => logHi log2hi 7 5 ((19 : ℚ) / 147)
  | 167 => logHi log2hi 7 5 ((39 : ℚ) / 295)
  | 168 => logHi log2hi 7 5 ((5 : ℚ) / 37)
  | 169 => logHi log2hi 7 5 ((41 : ℚ) / 297)
  | 170 => logHi log2hi 7 5 ((21 : ℚ) / 149)
  | 171 => logHi log2hi 7 5 ((43 : ℚ) / 299)
  | 172 => logHi log2hi 7 5 ((11 : ℚ) / 75)
  | 173 => logHi log2hi 7 5 ((45 : ℚ) / 301)
  | 174 => logHi log2hi 7 5 ((23 : ℚ) / 151)
  | 175 => logHi log2hi 7 5 ((47 : ℚ) / 303)
  | 176 => logHi log2hi 7 5 ((3 : ℚ) / 19)
  | 177 => logHi log2hi 7 5 ((49 : ℚ) / 305)
  | 178 => logHi log2hi 7 5 ((25 : ℚ) / 153)
  | 179 => logHi log2hi 7 5 ((51 : ℚ) / 307)
  | 180 => logHi log2hi 7 5 ((13 : ℚ) / 77)
  | 181 => logHi log2hi 7 5 ((53 : ℚ) / 309)
  | 182 => logHi log2hi 7 5 ((27 : ℚ) / 155)
  | 183 => logHi log2hi 7 5 ((55 : ℚ) / 311)
  | 184 => logHi log2hi 7 5 ((7 : ℚ) / 39)
  | 185 => logHi log2hi 7 5 ((57 : ℚ) / 313)
  | 186 => logHi log2hi 7 5 ((29 : ℚ) / 157)
  | 187 => logHi log2hi 7 5 ((59 : ℚ) / 315)
  | 188 => logHi log2hi 7 5 ((15 : ℚ) / 79)
  | 189 => logHi log2hi 7 5 ((61 : ℚ) / 317)
  | 190 => logHi log2hi 7 5 ((31 : ℚ) / 159)
  | 191 => logHi log2hi 7 5 ((63 : ℚ) / 319)
  | 192 => logHi log2hi 7 5 ((1 : ℚ) / 5)
  | 193 => logHi log2hi 7 5 ((65 : ℚ) / 321)
  | 194 => logHi log2hi 7 5 ((33 : ℚ) / 161)
  | 195 => logHi log2hi 7 5 ((67 : ℚ) / 323)
  | 196 => logHi log2hi 7 5 ((17 : ℚ) / 81)
  | 197 => logHi log2hi 7 5 ((69 : ℚ) / 325)
  | 198 => logHi log2hi 7 5 ((35 : ℚ) / 163)
  | 199 => logHi log2hi 7 5 ((71 : ℚ) / 327)
  | 200 => logHi log2hi 7 5 ((9 : ℚ) / 41)
  | 201 => logHi log2hi 7 5 ((73 : ℚ) / 329)
  | _ => 0


theorem log_lo (n : ℕ) (hn : n ≤ 201) : ((loOf n : ℚ) : ℝ) ≤ Real.log (n : ℝ) := by
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n <;>
    first
      | exact logLo_sound (by norm_num) (by norm_num) (by norm_num) (by norm_num) log2lo_le
      | norm_num [loOf]


theorem log_hi (n : ℕ) (hn : n ≤ 201) : Real.log (n : ℝ) ≤ ((hiOf n : ℚ) : ℝ) := by
  have hn0 : 0 ≤ n := Nat.zero_le n
  interval_cases n <;>
    first
      | exact logHi_sound (by norm_num) (by norm_num) (by norm_num) (by norm_num) log2hi_ge
      | norm_num [hiOf]


noncomputable def HI (m : ℕ) : ℚ := hiOf (m + 1)

theorem hLO : ∀ m : ℕ, m ∈ Finset.Icc 1 200 → ((loOf m : ℚ) : ℝ) ≤ Real.log (m : ℝ) :=
  fun m hm => log_lo m (by have := (Finset.mem_Icc.mp hm).2; omega)

theorem hHI : ∀ m : ℕ, m ∈ Finset.Icc 1 200 →
    Real.log ((m : ℝ) + 1) ≤ ((HI m : ℚ) : ℝ) := by
  intro m hm
  have hm2 := (Finset.mem_Icc.mp hm).2
  have h := log_hi (m + 1) (by omega)
  simpa [HI, Nat.cast_add, Nat.cast_one] using h




def D : ℕ := 10 ^ 6

theorem hLO14 : ∀ m : ℕ, m ∈ Finset.Icc 1 200 → loOf m ≤ 14 := by
  intro m hm
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  interval_cases m <;> norm_num [loOf, logLo, log2lo, Finset.sum_range_succ]

theorem hHI15 : ∀ m : ℕ, m ∈ Finset.Icc 1 200 → HI m < 15 := by
  intro m hm
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  interval_cases m <;> norm_num [HI, hiOf, logHi, log2hi, Finset.sum_range_succ]


noncomputable def termQ (m : ℕ) : ℚ :=
  2 * DmQ m * (14 - loOf m) ^ 2 / ((m : ℚ) * ((m : ℚ) + 1) * (15 - HI m) ^ 3)


def termU : ℕ → ℕ
  | 1 => 20080
  | 2 => 6592
  | 3 => 54975
  | 4 => 33133
  | 5 => 22209
  | 6 => 15953
  | 7 => 12030
  | 8 => 9405
  | 9 => 7562
  | 10 => 6216
  | 11 => 5203
  | 12 => 4421
  | 13 => 3805
  | 14 => 3310
  | 15 => 2907
  | 16 => 2574
  | 17 => 2295
  | 18 => 2060
  | 19 => 1860
  | 20 => 1688
  | 21 => 1539
  | 22 => 1409
  | 23 => 1295
  | 24 => 1194
  | 25 => 1105
  | 26 => 1026
  | 27 => 955
  | 28 => 891
  | 29 => 833
  | 30 => 781
  | 31 => 734
  | 32 => 691
  | 33 => 651
  | 34 => 615
  | 35 => 582
  | 36 => 552
  | 37 => 524
  | 38 => 498
  | 39 => 474
  | 40 => 451
  | 41 => 431
  | 42 => 411
  | 43 => 393
  | 44 => 376
  | 45 => 361
  | 46 => 346
  | 47 => 332
  | 48 => 319
  | 49 => 306
  | 50 => 295
  | 51 => 284
  | 52 => 274
  | 53 => 264
  | 54 => 255
  | 55 => 246
  | 56 => 237
  | 57 => 230
  | 58 => 222
  | 59 => 215
  | 60 => 208
  | 61 => 202
  | 62 => 196
  | 63 => 190
  | 64 => 184
  | 65 => 179
  | 66 => 173
  | 67 => 169
  | 68 => 164
  | 69 => 159
  | 70 => 155
  | 71 => 151
  | 72 => 147
  | 73 => 143
  | 74 => 139
  | 75 => 136
  | 76 => 133
  | 77 => 129
  | 78 => 126
  | 79 => 123
  | 80 => 120
  | 81 => 117
  | 82 => 115
  | 83 => 112
  | 84 => 109
  | 85 => 107
  | 86 => 105
  | 87 => 102
  | 88 => 100
  | 89 => 98
  | 90 => 96
  | 91 => 94
  | 92 => 92
  | 93 => 90
  | 94 => 88
  | 95 => 87
  | 96 => 85
  | 97 => 83
  | 98 => 82
  | 99 => 80
  | 100 => 79
  | 101 => 77
  | 102 => 76
  | 103 => 74
  | 104 => 73
  | 105 => 72
  | 106 => 70
  | 107 => 69
  | 108 => 68
  | 109 => 67
  | 110 => 65
  | 111 => 64
  | 112 => 63
  | 113 => 62
  | 114 => 61
  | 115 => 60
  | 116 => 59
  | 117 => 58
  | 118 => 57
  | 119 => 56
  | 120 => 56
  | 121 => 55
  | 122 => 54
  | 123 => 53
  | 124 => 52
  | 125 => 51
  | 126 => 51
  | 127 => 50
  | 128 => 49
  | 129 => 48
  | 130 => 48
  | 131 => 47
  | 132 => 46
  | 133 => 46
  | 134 => 45
  | 135 => 44
  | 136 => 44
  | 137 => 43
  | 138 => 43
  | 139 => 42
  | 140 => 41
  | 141 => 41
  | 142 => 40
  | 143 => 40
  | 144 => 39
  | 145 => 39
  | 146 => 38
  | 147 => 38
  | 148 => 37
  | 149 => 37
  | 150 => 36
  | 151 => 36
  | 152 => 35
  | 153 => 35
  | 154 => 35
  | 155 => 34
  | 156 => 34
  | 157 => 33
  | 158 => 33
  | 159 => 33
  | 160 => 32
  | 161 => 32
  | 162 => 31
  | 163 => 31
  | 164 => 31
  | 165 => 30
  | 166 => 30
  | 167 => 30
  | 168 => 29
  | 169 => 29
  | 170 => 29
  | 171 => 28
  | 172 => 28
  | 173 => 28
  | 174 => 27
  | 175 => 27
  | 176 => 27
  | 177 => 27
  | 178 => 26
  | 179 => 26
  | 180 => 26
  | 181 => 26
  | 182 => 25
  | 183 => 25
  | 184 => 25
  | 185 => 24
  | 186 => 24
  | 187 => 24
  | 188 => 24
  | 189 => 24
  | 190 => 23
  | 191 => 23
  | 192 => 23
  | 193 => 23
  | 194 => 22
  | 195 => 22
  | 196 => 22
  | 197 => 22
  | 198 => 22
  | 199 => 21
  | 200 => 21
  | _ => 0


def SnumLit : ℕ := 250143

theorem hsum : (∑ m ∈ Finset.Icc 1 200, termQ m) ≤ (SnumLit : ℚ) / D := by
  have h1 : ∀ m ∈ Finset.Icc 1 200, termQ m ≤ (termU m : ℚ) / D := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    interval_cases m <;>
      norm_num [termQ, loOf, HI, hiOf, DmQ, logLo, logHi, log2lo, log2hi, Finset.sum_range_succ, termU, D]
  calc ∑ m ∈ Finset.Icc 1 200, termQ m
      ≤ ∑ m ∈ Finset.Icc 1 200, (termU m : ℚ) / D := Finset.sum_le_sum h1
    _ = ((∑ m ∈ Finset.Icc 1 200, termU m : ℕ) : ℚ) / D := by
        rw [← Finset.sum_div]
        push_cast
        ring
    _ ≤ (SnumLit : ℚ) / D := by
        apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℚ) ≤ (D : ℚ))
        exact_mod_cast (by
          decide : (∑ m ∈ Finset.Icc 1 200, termU m) ≤ SnumLit)


theorem numeric_check :
    (SnumLit : ℝ) / D + 1 / 135 < (0.259330618 : ℝ) := by
  norm_num [SnumLit, D]


theorem finite_bound (L : ℝ) (hL : 15 ≤ L) :
    ∑ m ∈ Finset.Icc 1 200, Em L m ≤ (SnumLit : ℝ) / D := by
  have h := sum_Em_le_of_data loOf HI ((SnumLit : ℚ) / D) hLO hHI hLO14 hHI15 hsum L hL
  convert h using 1
  push_cast
  ring



theorem em_sum_lt (L : ℝ) (hL : 15 ≤ L) (M : ℕ) (hM : 200 ≤ M)
    (hact : ∀ m ∈ Finset.Icc 201 M, Real.log 2.9 < L - Real.log ((m : ℝ) + 1)) :
    ∑ m ∈ Finset.Icc 1 M, Em L m < (0.259330618 : ℝ) := by
  have hunion : Finset.Icc 1 M = Finset.Icc 1 200 ∪ Finset.Icc 201 M := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 200) (Finset.Icc 201 M) := by
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    simp only [Finset.mem_Icc] at hm1 hm2
    omega
  rw [hunion, Finset.sum_union hdisj]
  have htail := Em_Icc_tail_le_of (L := L) 201 M (by norm_num) hact
  have htail' : ∑ m ∈ Finset.Icc 201 M, Em L m ≤ 1 / 135 := by
    convert htail using 1
    norm_num
  have hfin := finite_bound L hL
  have hnum := numeric_check
  linarith

end RHLean.GateII.EmData




end Inline_GateII_EmData

section Inline_GateII_PrimeBound



















open Set MeasureTheory
open scoped BigOperators

namespace RHLean.GateII.Chain


theorem Jm_nonneg (m : ℕ) : 0 ≤ Jm m := by
  unfold Jm
  apply intervalIntegral.integral_nonneg
  · rw [div_le_one (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    linarith
  · intro u hu
    have hum : 0 ≤ u :=
      le_trans (by positivity : (0 : ℝ) ≤ (m : ℝ) / ((m : ℝ) + 1)) hu.1
    rcases eq_or_lt_of_le hum with h | h
    · rw [← h]
      simp
    · exact div_nonneg (sq_nonneg _) h.le


theorem Jm_summable : Summable (fun m : ℕ => Jm (m + 1)) := hasSum_Jm.summable


theorem sum_Icc_one_eq_sum_range_Jm (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, Jm m = ∑ m ∈ Finset.range M, Jm (m + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), ih, Finset.sum_range_succ]


theorem sum_Icc_Jm_le_tsum (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, Jm m ≤ ∑' m : ℕ, Jm (m + 1) := by
  rw [sum_Icc_one_eq_sum_range_Jm M]
  exact Jm_summable.sum_le_tsum (Finset.range M) (fun i _ => Jm_nonneg (i + 1))

end RHLean.GateII.Chain

namespace RHLean.GateII.PrimePart

open RHLean.GateII.Chain
open RHLean.GateII.AWGC
open RHLean.GateII.Stieltjes





theorem prime_part_bin_le {k m : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (ha : 2.9 < (k : ℝ) / ((m : ℝ) + 1))
    (hMert : ∀ t ∈ Set.Icc ((k : ℝ) / ((m : ℝ) + 1)) ((k : ℝ) / (m : ℝ)),
        |Chebyshev.theta t - t| ≤ Dm m * ((k : ℝ) / (m : ℝ)) / (La k m) ^ 2) :
    ∑ p ∈ (Nat.primesLE ⌊(k : ℝ) / (m : ℝ)⌋₊).filter
        (fun p : ℕ => (k : ℝ) / ((m : ℝ) + 1) < (p : ℝ)),
      gpar (Lb k m / ((k : ℝ) / (m : ℝ))) (p : ℝ) * Real.log (p : ℝ)
      ≤ ((Lb k m - 1) ^ 2 / La k m) * Jm m + Em (Real.log (k : ℝ)) m := by
  set A : ℝ := (k : ℝ) / ((m : ℝ) + 1) with hA
  set B : ℝ := (k : ℝ) / (m : ℝ) with hB
  set c : ℝ := Lb k m / B with hc
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have haA : 2.9 < A := ha
  have haRaw : 2.9 < (k : ℝ) / ((m : ℝ) + 1) := by rw [← hA]; exact ha
  have ha0 : 0 ≤ A := le_of_lt (lt_trans (by norm_num) haA)
  have hApos : 0 < A := lt_trans (by norm_num) haA
  have hBpos : 0 < B := by rw [hB]; exact div_pos hk0 hm0
  have hAexp : Real.exp 1 ≤ A := by
    have h := Real.exp_one_lt_d9
    norm_num at h
    linarith
  have hBexp_lt : Real.exp 1 < B := by
    have hmul : 2.9 * ((m : ℝ) + 1) < (k : ℝ) := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)] at ha
      exact ha
    have h29B : (2.9 : ℝ) < B := by
      rw [hB, lt_div_iff₀ hm0]
      nlinarith [hmul]
    have h := Real.exp_one_lt_d9
    norm_num at h
    linarith
  have hBexp : Real.exp 1 ≤ B := hBexp_lt.le
  have hAleB : A ≤ B := by
    rw [hA, hB]
    exact div_le_div_of_nonneg_left hk0.le hm0 (by linarith)
  have hLB : Lb k m = Real.log B := by
    unfold Lb
    rw [hB]
  have hc_pos : 0 < c := by
    have hlogB : 0 < Real.log B :=
      Real.log_pos (lt_trans (Real.one_lt_exp_iff.mpr one_pos) hBexp_lt)
    rw [hc, hLB]
    exact div_pos hlogB hBpos
  have hApar : ∀ t ∈ Set.Icc A B, 0 ≤ Apar c t := by
    intro t ht
    have h := Apar_nonneg (b := B) hBexp (le_trans hAexp ht.1) ht.2
    have hc'
    rw [hc']
    exact h
  have hg0 : ∀ t ∈ Set.Icc A B, 0 ≤ gpar c t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hApos ht.1
    have hlog : 0 < Real.log t :=
      Real.log_pos (lt_of_lt_of_le (by norm_num) (le_trans hAexp ht.1))
    unfold gpar
    exact div_nonneg (sq_nonneg _) (mul_pos ht0 hlog).le
  have hganti : AntitoneOn (gpar c) (Set.Icc A B) :=
    gpar_antitoneOn_Icc hc_pos hAexp hAleB hApar
  have hst := sum_thetaJump_mul_le (g := gpar c) (a := A) (b := B)
    (Mq := Dm m * B / (La k m) ^ 2) ha0 hAleB hg0 hganti hMert
  have hconv := sum_primes_eq_sum_thetaJump (g := gpar c) (a := A) (b := B) ha0
  have hint' : ∫ t in A..B, gpar c t ≤ ((Lb k m - 1) ^ 2 / La k m) * Jm m := by
    rw [hA, hc, hB]
    exact integral_gpar_le hm hk haRaw
  have hem' : 2 * (Dm m * B / (La k m) ^ 2) * gpar c A
      ≤ Em (Real.log (k : ℝ)) m := by
    rw [hA, hc, hB]
    have hem := Em_error_term_le hm hk haRaw
    have e1 : 2 * (Dm m * ((k : ℝ) / (m : ℝ)) / (La k m) ^ 2)
        = 2 * Dm m * ((k : ℝ) / (m : ℝ)) / (La k m) ^ 2 := by ring
    rw [e1]
    exact hem
  calc ∑ p ∈ (Nat.primesLE ⌊B⌋₊).filter (fun p : ℕ => A < (p : ℝ)),
        gpar c (p : ℝ) * Real.log (p : ℝ)
      = ∑ m ∈ Finset.Ico (⌊A⌋₊ + 1) (⌊B⌋₊ + 1),
          gpar c (m : ℝ) * thetaJump m := hconv
    _ ≤ (∫ t in A..B, gpar c t) + 2 * (Dm m * B / (La k m) ^ 2) * gpar c A := hst
    _ ≤ ((Lb k m - 1) ^ 2 / La k m) * Jm m + Em (Real.log (k : ℝ)) m := by
        linarith [hint', hem']



theorem Lb_sub_one_sq_div_La_mul_Jm_le {k m : ℕ} (hm : 1 ≤ m)
    (ha : 2.9 < (k : ℝ) / ((m : ℝ) + 1)) (hk : 15 ≤ Real.log (k : ℝ)) :
    ((Lb k m - 1) ^ 2 / La k m) * Jm m ≤ Real.log (k : ℝ) * Jm m :=
  mul_le_mul_of_nonneg_right (Lb_sub_one_sq_div_La_le hm ha hk)
    (RHLean.GateII.Chain.Jm_nonneg m)




theorem prime_part_arith {L SJ SE : ℝ} (hL : 0 ≤ L)
    (hJ : SJ < 0.100317302) (hE : SE < 0.259330618) :
    L * SJ + SE < 0.100317302 * L + 0.259330618 := by
  rcases eq_or_lt_of_le hL with h | h
  · subst h
    simpa using hE
  · have h1 := mul_lt_mul_of_pos_left hJ h
    linarith


theorem log_k_nonneg {k : ℕ} (hL : 15 ≤ Real.log (k : ℝ)) :
    0 ≤ Real.log (k : ℝ) := le_trans (by norm_num) hL










theorem prime_part_sum_le {k M : ℕ} (hk : 1 ≤ k) (hM : 200 ≤ M)
    (hL : 15 ≤ Real.log (k : ℝ))
    (ha : ∀ m ∈ Finset.Icc 1 M, 2.9 < (k : ℝ) / ((m : ℝ) + 1))
    (hMert : ∀ m ∈ Finset.Icc 1 M,
        ∀ t ∈ Set.Icc ((k : ℝ) / ((m : ℝ) + 1)) ((k : ℝ) / (m : ℝ)),
        |Chebyshev.theta t - t| ≤ Dm m * ((k : ℝ) / (m : ℝ)) / (La k m) ^ 2)
    (hact : ∀ m ∈ Finset.Icc 201 M,
        Real.log 2.9 < Real.log (k : ℝ) - Real.log ((m : ℝ) + 1)) :
    ∑ m ∈ Finset.Icc 1 M,
        (∑ p ∈ (Nat.primesLE ⌊(k : ℝ) / (m : ℝ)⌋₊).filter
            (fun p : ℕ => (k : ℝ) / ((m : ℝ) + 1) < (p : ℝ)),
          gpar (Lb k m / ((k : ℝ) / (m : ℝ))) (p : ℝ) * Real.log (p : ℝ))
      < 0.100317302 * Real.log (k : ℝ) + 0.259330618 := by
  have hbin : ∀ m ∈ Finset.Icc 1 M,
      (∑ p ∈ (Nat.primesLE ⌊(k : ℝ) / (m : ℝ)⌋₊).filter
          (fun p : ℕ => (k : ℝ) / ((m : ℝ) + 1) < (p : ℝ)),
        gpar (Lb k m / ((k : ℝ) / (m : ℝ))) (p : ℝ) * Real.log (p : ℝ))
      ≤ ((Lb k m - 1) ^ 2 / La k m) * Jm m + Em (Real.log (k : ℝ)) m :=
    fun m hm => prime_part_bin_le (Finset.mem_Icc.mp hm).1 hk (ha m hm) (hMert m hm)
  have hsum1 : (∑ m ∈ Finset.Icc 1 M,
        (∑ p ∈ (Nat.primesLE ⌊(k : ℝ) / (m : ℝ)⌋₊).filter
            (fun p : ℕ => (k : ℝ) / ((m : ℝ) + 1) < (p : ℝ)),
          gpar (Lb k m / ((k : ℝ) / (m : ℝ))) (p : ℝ) * Real.log (p : ℝ)))
      ≤ (∑ m ∈ Finset.Icc 1 M, ((Lb k m - 1) ^ 2 / La k m) * Jm m)
        + ∑ m ∈ Finset.Icc 1 M, Em (Real.log (k : ℝ)) m := by
    simpa [Finset.sum_add_distrib] using Finset.sum_le_sum hbin
  have hJpart : (∑ m ∈ Finset.Icc 1 M, ((Lb k m - 1) ^ 2 / La k m) * Jm m)
      ≤ Real.log (k : ℝ) * ∑ m ∈ Finset.Icc 1 M, Jm m := by
    calc (∑ m ∈ Finset.Icc 1 M, ((Lb k m - 1) ^ 2 / La k m) * Jm m)
        ≤ ∑ m ∈ Finset.Icc 1 M, Real.log (k : ℝ) * Jm m :=
          Finset.sum_le_sum fun m hm =>
            Lb_sub_one_sq_div_La_mul_Jm_le (Finset.mem_Icc.mp hm).1 (ha m hm) hL
      _ = Real.log (k : ℝ) * ∑ m ∈ Finset.Icc 1 M, Jm m :=
          (Finset.mul_sum (Finset.Icc 1 M) Jm (Real.log (k : ℝ))).symm
  have hJtot : (∑ m ∈ Finset.Icc 1 M, Jm m) < 0.100317302 :=
    lt_of_le_of_lt (RHLean.GateII.Chain.sum_Icc_Jm_le_tsum M) tsum_Jm_lt
  have hEtot := RHLean.GateII.EmData.em_sum_lt (Real.log (k : ℝ)) hL M hM hact
  have hfin : Real.log (k : ℝ) * (∑ m ∈ Finset.Icc 1 M, Jm m)
        + ∑ m ∈ Finset.Icc 1 M, Em (Real.log (k : ℝ)) m
      < 0.100317302 * Real.log (k : ℝ) + 0.259330618 :=
    prime_part_arith (log_k_nonneg hL) hJtot hEtot
  calc (∑ m ∈ Finset.Icc 1 M,
        (∑ p ∈ (Nat.primesLE ⌊(k : ℝ) / (m : ℝ)⌋₊).filter
            (fun p : ℕ => (k : ℝ) / ((m : ℝ) + 1) < (p : ℝ)),
          gpar (Lb k m / ((k : ℝ) / (m : ℝ))) (p : ℝ) * Real.log (p : ℝ)))
      ≤ (∑ m ∈ Finset.Icc 1 M, ((Lb k m - 1) ^ 2 / La k m) * Jm m)
          + ∑ m ∈ Finset.Icc 1 M, Em (Real.log (k : ℝ)) m := hsum1
    _ ≤ Real.log (k : ℝ) * (∑ m ∈ Finset.Icc 1 M, Jm m)
          + ∑ m ∈ Finset.Icc 1 M, Em (Real.log (k : ℝ)) m :=
        add_le_add_left hJpart _
    _ < 0.100317302 * Real.log (k : ℝ) + 0.259330618 := hfin






noncomputable def cBin (k m : ℕ) : ℝ := Lb k m / ((k : ℝ) / (m : ℝ))






theorem Nset_prime_sum_le_interval {k m : ℕ} (hm : 1 ≤ m) :
    (∑ n ∈ (Nset k m).filter (fun n => Nat.Prime n),
        (Lambda n - cBin k m * (n : ℝ)) ^ 2 / (n : ℝ))
      ≤ ∑ p ∈ (Nat.primesLE ⌊(k : ℝ) / (m : ℝ)⌋₊).filter
          (fun p : ℕ => (k : ℝ) / ((m : ℝ) + 1) < (p : ℝ)),
          gpar (cBin k m) (p : ℝ) * Real.log (p : ℝ) := by
  have hcongr : (∑ n ∈ (Nset k m).filter (fun n => Nat.Prime n),
        (Lambda n - cBin k m * (n : ℝ)) ^ 2 / (n : ℝ))
      = ∑ n ∈ (Nset k m).filter (fun n => Nat.Prime n),
        gpar (cBin k m) (n : ℝ) * Real.log (n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hprime : Nat.Prime n := (Finset.mem_filter.mp hn).2
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hprime.one_lt
    have hlogn : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hn1)
    have hΛ : Lambda n = Real.log (n : ℝ) :=
      ArithmeticFunction.vonMangoldt_apply_prime hprime
    rw [hΛ]
    unfold gpar Apar
    field_simp
  rw [hcongr]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hprime : Nat.Prime n := hn'.2
    have hmem := mem_Nset.mp hn'.1
    obtain ⟨hnk, _hΛnz, _hndvd, hdiv⟩ := hmem
    have hnpos : 0 < n := hprime.pos
    have hdiv' := (Nat.div_eq_iff hnpos).mp hdiv
    have hkle : m * n ≤ k := hdiv'.1
    have hklt : k < (m + 1) * n := by
      have h2 := hdiv'.2
      have hn1 : 1 ≤ n := hprime.one_lt.le
      rw [Nat.succ_mul]
      omega
    refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨?_, hprime⟩, ?_⟩
    · rw [Nat.floor_div_eq_div, Nat.le_div_iff_mul_le hm]
      simpa [Nat.mul_comm] using hkle
    · have hkltR : (k : ℝ) < ((m : ℝ) + 1) * (n : ℝ) := by exact_mod_cast hklt
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
      linarith
  · intro n hnt _
    have hprime : Nat.Prime n := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hnt).1).2
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hprime.one_lt
    have hnpos : (0 : ℝ) < n := by positivity
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hn1
    unfold gpar
    exact mul_nonneg (div_nonneg (sq_nonneg _) (mul_pos hnpos hlogn).le) hlogn.le



theorem Nset_prime_sum_le (k M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Nset k m).filter (fun n => Nat.Prime n),
        (Lambda n - cBin k m * (n : ℝ)) ^ 2 / (n : ℝ))
      ≤ ∑ m ∈ Finset.Icc 1 M,
          (∑ p ∈ (Nat.primesLE ⌊(k : ℝ) / (m : ℝ)⌋₊).filter
              (fun p : ℕ => (k : ℝ) / ((m : ℝ) + 1) < (p : ℝ)),
            gpar (cBin k m) (p : ℝ) * Real.log (p : ℝ)) :=
  Finset.sum_le_sum fun _m hm =>
    Nset_prime_sum_le_interval (Finset.mem_Icc.mp hm).1





theorem Nset_prime_sum_lt {k M : ℕ} (hk : 1 ≤ k) (hM : 200 ≤ M)
    (hL : 15 ≤ Real.log (k : ℝ))
    (ha : ∀ m ∈ Finset.Icc 1 M, 2.9 < (k : ℝ) / ((m : ℝ) + 1))
    (hMert : ∀ m ∈ Finset.Icc 1 M,
        ∀ t ∈ Set.Icc ((k : ℝ) / ((m : ℝ) + 1)) ((k : ℝ) / (m : ℝ)),
        |Chebyshev.theta t - t| ≤ Dm m * ((k : ℝ) / (m : ℝ)) / (La k m) ^ 2)
    (hact : ∀ m ∈ Finset.Icc 201 M,
        Real.log 2.9 < Real.log (k : ℝ) - Real.log ((m : ℝ) + 1)) :
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ (Nset k m).filter (fun n => Nat.Prime n),
        (Lambda n - cBin k m * (n : ℝ)) ^ 2 / (n : ℝ))
      < 0.100317302 * Real.log (k : ℝ) + 0.259330618 :=
  lt_of_le_of_lt (Nset_prime_sum_le k M)
    (prime_part_sum_le hk hM hL ha hMert hact)








theorem Vsum_le_sum_activeN_shifted (k : ℕ) :
    Vsum k ≤ ∑ n ∈ activeN k,
        (Lambda n - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ) := by
  have h1 : Vsum k ≤ ∑ m ∈ Finset.range (k + 1),
      ∑ n ∈ Nset k m, (Lambda n - cBin k m * (n : ℝ)) ^ 2 / (n : ℝ) :=
    Finset.sum_le_sum fun m _ => V_le_shifted k m (cBin k m)
  have hmap : ∀ n ∈ activeN k, k / n ∈ Finset.range (k + 1) := by
    intro n hn
    rw [Finset.mem_range]
    have hle : k / n ≤ k := Nat.div_le_self k n
    omega
  have hfiber := Finset.sum_fiberwise_of_maps_to (s := activeN k)
    (t := Finset.range (k + 1)) (g := fun n : ℕ => k / n)
    (f := fun n : ℕ => (Lambda n - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ)) hmap
  have h1' : Vsum k ≤ ∑ m ∈ Finset.range (k + 1),
      ∑ n ∈ (activeN k).filter (fun n => k / n = m),
        (Lambda n - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ) := by
    refine le_trans h1 (Finset.sum_le_sum fun m _ => ?_)
    have hset : Nset k m = (activeN k).filter (fun n => k / n = m) := by
      ext n
      simp only [mem_Nset, activeN, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
      tauto
    rw [hset]
    refine Finset.sum_le_sum fun n hn => ?_
    have hkn : k / n = m := (Finset.mem_filter.mp hn).2
    rw [← hkn]
  rwa [hfiber] at h1'




theorem Vsum_le_prime_add_hpp (k : ℕ) :
    Vsum k ≤
      (∑ n ∈ (activeN k).filter (fun n => Nat.Prime n),
          (Lambda n - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ))
        + ∑ n ∈ (activeN k).filter (fun n => ¬ Nat.Prime n),
          (Lambda n - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ) := by
  have h := Vsum_le_sum_activeN_shifted k
  rw [← Finset.sum_filter_add_sum_filter_not (s := activeN k)
    (p := fun n : ℕ => Nat.Prime n)
    (f := fun n : ℕ => (Lambda n - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ))] at h
  exact h

end RHLean.GateII.PrimePart



end Inline_GateII_PrimeBound



section Inline_GateII_CollarSplit










open MeasureTheory Set

namespace RHLean.GateII.Collar




theorem setIntegral_prod_block_split
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : ℝ × ℝ → E} {s t u : Set ℝ}
    (hOC : s = t ∪ u) (hdisj : Disjoint t u)
    (ht : MeasurableSet t) (hu : MeasurableSet u)
    (hK : IntegrableOn K (s ×ˢ s) (volume.prod volume)) :
    (∫ x in s, ∫ y in s, K (x, y))
      = (∫ x in t, ∫ y in t, K (x, y))
        + (∫ x in t, ∫ y in u, K (x, y))
        + (∫ x in u, ∫ y in t, K (x, y))
        + (∫ x in u, ∫ y in u, K (x, y)) := by
  classical
  have hsub_t : t ⊆ s := by rw [hOC]; exact subset_union_left
  have hsub_u : u ⊆ s := by rw [hOC]; exact subset_union_right
  have hK_tt : IntegrableOn K (t ×ˢ t) (volume.prod volume) :=
    hK.mono_set (Set.prod_mono hsub_t hsub_t)
  have hK_tu : IntegrableOn K (t ×ˢ u) (volume.prod volume) :=
    hK.mono_set (Set.prod_mono hsub_t hsub_u)
  have hK_ut : IntegrableOn K (u ×ˢ t) (volume.prod volume) :=
    hK.mono_set (Set.prod_mono hsub_u hsub_t)
  have hK_uu : IntegrableOn K (u ×ˢ u) (volume.prod volume) :=
    hK.mono_set (Set.prod_mono hsub_u hsub_u)

  have hd_tt_tu : Disjoint (t ×ˢ t) (t ×ˢ u) := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨-, hy'⟩
    exact (Set.disjoint_left.mp hdisj) hy hy'
  have hd_ut_uu : Disjoint (u ×ˢ t) (u ×ˢ u) := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨-, hy'⟩
    exact (Set.disjoint_left.mp hdisj) hy hy'
  have hd_left_right : Disjoint (t ×ˢ s) (u ×ˢ s) := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, -⟩ ⟨hx', -⟩
    exact (Set.disjoint_left.mp hdisj) hx hx'

  have hm_tt : MeasurableSet (t ×ˢ t) := ht.prod ht
  have hm_tu : MeasurableSet (t ×ˢ u) := ht.prod hu
  have hm_ut : MeasurableSet (u ×ˢ t) := hu.prod ht
  have hm_uu : MeasurableSet (u ×ˢ u) := hu.prod hu
  have hm_ts : MeasurableSet (t ×ˢ s) := ht.prod (by rw [hOC]; exact ht.union hu)
  have hm_us : MeasurableSet (u ×ˢ s) := hu.prod (by rw [hOC]; exact ht.union hu)

  have hts : t ×ˢ s = (t ×ˢ t) ∪ (t ×ˢ u) := by
    rw [← Set.prod_union, hOC]
  have hus : u ×ˢ s = (u ×ˢ t) ∪ (u ×ˢ u) := by
    rw [← Set.prod_union, hOC]
  have hss : s ×ˢ s = (t ×ˢ s) ∪ (u ×ˢ s) := by
    calc s ×ˢ s = (t ∪ u) ×ˢ (t ∪ u) := by rw [hOC]
      _ = (t ×ˢ (t ∪ u)) ∪ (u ×ˢ (t ∪ u)) := Set.union_prod
      _ = (t ×ˢ s) ∪ (u ×ˢ s) := by rw [← hOC]
  have hK_ts : IntegrableOn K (t ×ˢ s) (volume.prod volume) :=
    hK.mono_set (Set.prod_mono hsub_t subset_rfl)
  have hK_us : IntegrableOn K (u ×ˢ s) (volume.prod volume) :=
    hK.mono_set (Set.prod_mono hsub_u subset_rfl)

  have hsplit1 : (∫ z in s ×ˢ s, K z ∂(volume.prod volume))
      = (∫ z in t ×ˢ s, K z ∂(volume.prod volume))
        + (∫ z in u ×ˢ s, K z ∂(volume.prod volume)) := by
    rw [hss]
    exact setIntegral_union hd_left_right hm_us hK_ts hK_us
  have hsplit2 : (∫ z in t ×ˢ s, K z ∂(volume.prod volume))
      = (∫ z in t ×ˢ t, K z ∂(volume.prod volume))
        + (∫ z in t ×ˢ u, K z ∂(volume.prod volume)) := by
    rw [hts]
    exact setIntegral_union hd_tt_tu hm_tu hK_tt hK_tu
  have hsplit3 : (∫ z in u ×ˢ s, K z ∂(volume.prod volume))
      = (∫ z in u ×ˢ t, K z ∂(volume.prod volume))
        + (∫ z in u ×ˢ u, K z ∂(volume.prod volume)) := by
    rw [hus]
    exact setIntegral_union hd_ut_uu hm_uu hK_ut hK_uu

  have hL : (∫ x in s, ∫ y in s, K (x, y))
      = ∫ z in s ×ˢ s, K z ∂(volume.prod volume) :=
    (setIntegral_prod K hK).symm
  have htt : (∫ x in t, ∫ y in t, K (x, y))
      = ∫ z in t ×ˢ t, K z ∂(volume.prod volume) :=
    (setIntegral_prod K hK_tt).symm
  have htu : (∫ x in t, ∫ y in u, K (x, y))
      = ∫ z in t ×ˢ u, K z ∂(volume.prod volume) :=
    (setIntegral_prod K hK_tu).symm
  have hut : (∫ x in u, ∫ y in t, K (x, y))
      = ∫ z in u ×ˢ t, K z ∂(volume.prod volume) :=
    (setIntegral_prod K hK_ut).symm
  have huu : (∫ x in u, ∫ y in u, K (x, y))
      = ∫ z in u ×ˢ u, K z ∂(volume.prod volume) :=
    (setIntegral_prod K hK_uu).symm
  rw [hL, hsplit1, hsplit2, hsplit3, ← htt, ← htu, ← hut, ← huu]
  abel

end RHLean.GateII.Collar



end Inline_GateII_CollarSplit

section Inline_GateII_Harmonic


















































namespace RHLean.GateII.Harmonic

open Matrix
open scoped InnerProductSpace





noncomputable def oldNewBlock {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) :
    Matrix (m ⊕ n) (m ⊕ n) ℝ :=
  fromBlocks A B Bᴴ D



noncomputable def harmonicForm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) [Invertible D] :
    Matrix m m ℝ :=
  A - B * D⁻¹ * Bᴴ



noncomputable def harmonicExtension {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (B : Matrix m n ℝ) (D : Matrix n n ℝ) [Invertible D] (f : m → ℝ) :
    m ⊕ n → ℝ :=
  f ⊕ᵥ (-(D⁻¹ *ᵥ (Bᴴ *ᵥ f)))







theorem dotProduct_harmonicExtension {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) [Invertible D]
    (hD : D.IsHermitian) (f : m → ℝ) :
    harmonicExtension B D f ⬝ᵥ (oldNewBlock A B D *ᵥ harmonicExtension B D f)
      = f ⬝ᵥ (harmonicForm A B D *ᵥ f) := by
  have h := Matrix.schur_complement_eq₂₂ A B f (-(D⁻¹ *ᵥ (Bᴴ *ᵥ f))) hD
  have hy : (D⁻¹ * Bᴴ) *ᵥ f + (-(D⁻¹ *ᵥ (Bᴴ *ᵥ f))) = 0 := by
    rw [Matrix.mulVec_mulVec]
    abel
  rw [hy] at h
  simp only [star_zero, Matrix.zero_vecMul, dotProduct_zero, zero_add] at h
  simpa [harmonicExtension, harmonicForm, oldNewBlock, star_trivial,
    Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec] using h




theorem harmonicExtension_minimizes {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) [Invertible D]
    (hD : D.PosDef) (f : m → ℝ) (y : n → ℝ) :
    f ⬝ᵥ (harmonicForm A B D *ᵥ f)
      ≤ (f ⊕ᵥ y) ⬝ᵥ (oldNewBlock A B D *ᵥ (f ⊕ᵥ y)) := by
  have h := Matrix.schur_complement_eq₂₂ A B f y hD.1
  simp only [star_trivial, oldNewBlock, harmonicForm] at h
  have hnonneg : 0 ≤ ((D⁻¹ * Bᴴ) *ᵥ f + y) ᵥ* D ⬝ᵥ ((D⁻¹ * Bᴴ) *ᵥ f + y) := by
    rw [← Matrix.dotProduct_mulVec]
    exact hD.posSemidef.dotProduct_mulVec_nonneg _
  simp only [oldNewBlock, harmonicForm, Matrix.dotProduct_mulVec]
  rw [h]
  linarith






theorem oldNew_schur {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) [Invertible D]
    (hA : A.PosDef) (hD : D.PosDef) (hT : (harmonicForm A B D).PosDef) :
    (oldNewBlock A B D).PosDef := by
  have hPS : (oldNewBlock A B D).PosSemidef :=
    (Matrix.PosDef.fromBlocks₂₂ A B hD).mpr hT.posSemidef
  refine (Matrix.posDef_iff_dotProduct_mulVec).mpr ⟨hPS.isHermitian, ?_⟩
  intro x hx
  set x₁ : m → ℝ := fun i => x (Sum.inl i)
  set x₂ : n → ℝ := fun j => x (Sum.inr j)
  have hxdecomp : x = x₁ ⊕ᵥ x₂ := (Sum.elim_comp_inl_inr x).symm
  have h := Matrix.schur_complement_eq₂₂ A B x₁ x₂ hD.1
  simp only [star_trivial, oldNewBlock, harmonicForm] at h
  rw [hxdecomp]
  simp only [star_trivial, oldNewBlock, harmonicForm, Matrix.dotProduct_mulVec]
  rw [h]
  rcases eq_or_ne x₁ 0 with hx1 | hx1
  · have hx2 : x₂ ≠ 0 := by
      intro hx2
      apply hx
      rw [hxdecomp, hx1, hx2]
      simp
    have hu : (D⁻¹ * Bᴴ) *ᵥ x₁ + x₂ = x₂ := by rw [hx1, mulVec_zero, zero_add]
    rw [hu, hx1]
    simp only [Matrix.zero_vecMul, dotProduct_zero, add_zero]
    rw [← Matrix.dotProduct_mulVec]
    simpa only [star_trivial] using hD.dotProduct_mulVec_pos hx2
  · have h1 : 0 < x₁ ᵥ* (A - B * D⁻¹ * Bᴴ) ⬝ᵥ x₁ := by
      rw [← Matrix.dotProduct_mulVec]
      exact hT.dotProduct_mulVec_pos hx1
    have h2 : 0 ≤ ((D⁻¹ * Bᴴ) *ᵥ x₁ + x₂) ᵥ* D ⬝ᵥ ((D⁻¹ * Bᴴ) *ᵥ x₁ + x₂) := by
      rw [← Matrix.dotProduct_mulVec]
      exact hD.posSemidef.dotProduct_mulVec_nonneg _
    linarith






theorem harmonicForm_posDef_of_block {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) [Invertible D]
    (hD : D.PosDef) (hM : (oldNewBlock A B D).PosDef) :
    (harmonicForm A B D).PosDef := by
  refine (Matrix.posDef_iff_dotProduct_mulVec).mpr ⟨?_, ?_⟩
  · exact ((Matrix.PosDef.fromBlocks₂₂ A B hD).mp hM.posSemidef).isHermitian
  · intro f hf
    have hne : harmonicExtension B D f ≠ 0 := by
      intro hzero
      apply hf
      funext i
      have := congrFun hzero (Sum.inl i)
      simpa [harmonicExtension] using this
    have hpos := hM.dotProduct_mulVec_pos (x := harmonicExtension B D f) hne
    simp only [star_trivial] at hpos
    rw [dotProduct_harmonicExtension A B D hD.1 f] at hpos
    simpa only [star_trivial] using hpos




noncomputable def groundCoord {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e f : E) : ℝ :=
  ⟪e, f⟫_ℝ / ‖e‖ ^ 2


noncomputable def transversePart {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e f : E) : E :=
  f - groundCoord e f • e


theorem inner_transversePart {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e f : E) (he : e ≠ 0) : ⟪e, transversePart e f⟫_ℝ = 0 := by
  unfold transversePart groundCoord
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hne : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
  field_simp
  ring


theorem ground_decomposition {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (e w : E) (γ : ℝ)
    (hw : ⟪e, w⟫_ℝ = 0) :
    ⟪γ • e + w, T (γ • e + w)⟫_ℝ
      = γ ^ 2 * ⟪e, T e⟫_ℝ + 2 * γ * ⟪e, T w⟫_ℝ + ⟪w, T w⟫_ℝ := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm (T e) w, hT e w]
  ring












theorem master_bound_of_components {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsPositive) (e w : E) (γ g : ℝ)
    (hw : ⟪e, w⟫_ℝ = 0) (hg : g * ‖e‖ ^ 2 ≤ ⟪e, T e⟫_ℝ)
    (hplace : 0 ≤ γ * ⟪e, T w⟫_ℝ) :
    γ ^ 2 * (g * ‖e‖ ^ 2) + ⟪w, T w⟫_ℝ
      ≤ ⟪γ • e + w, T (γ • e + w)⟫_ℝ := by
  rw [ground_decomposition T hT.isSymmetric e w γ hw]
  have h1 : γ ^ 2 * (g * ‖e‖ ^ 2) ≤ γ ^ 2 * ⟪e, T e⟫_ℝ :=
    mul_le_mul_of_nonneg_left hg (sq_nonneg γ)
  have h2 : 0 ≤ 2 * γ * ⟪e, T w⟫_ℝ := by linarith [hplace]
  have h3 : 0 ≤ ⟪w, T w⟫_ℝ := hT.inner_nonneg_right w
  linarith




theorem master_posDef_of_components {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsPositive) (e : E) (he : e ≠ 0) (g : ℝ) (hg : 0 < g)
    (hground : g * ‖e‖ ^ 2 ≤ ⟪e, T e⟫_ℝ)
    (hplace : ∀ f : E, 0 ≤ groundCoord e f * ⟪e, T (transversePart e f)⟫_ℝ)
    (hres : ∀ w : E, ⟪e, w⟫_ℝ = 0 → w ≠ 0 → 0 < ⟪w, T w⟫_ℝ) :
    ∀ f : E, f ≠ 0 → 0 < ⟪f, T f⟫_ℝ := by
  intro f hf
  set w := transversePart e f with hwdef
  set γ := groundCoord e f with hγdef
  have hw : ⟪e, w⟫_ℝ = 0 := inner_transversePart e f he
  have hfd : f = γ • e + w := by
    simp only [hwdef, hγdef, transversePart]
    abel
  have hbound := master_bound_of_components T hT e w γ g hw hground (hplace f)
  rw [← hfd] at hbound
  rcases eq_or_ne γ 0 with hγ | hγ
  · have hwne : w ≠ 0 := by
      intro hw0
      apply hf
      rw [hfd, hγ, hw0]
      simp
    have := hres w hw hwne
    rw [hγ] at hbound
    simp at hbound
    linarith
  · have hpos : 0 < γ ^ 2 * (g * ‖e‖ ^ 2) := by
      have hγ2 : 0 < γ ^ 2 := sq_pos_of_ne_zero hγ
      have hnorm : 0 < ‖e‖ ^ 2 := pow_pos (norm_pos_iff.mpr he) 2
      positivity
    have hw0 : 0 ≤ ⟪w, T w⟫_ℝ := hT.inner_nonneg_right w
    linarith

end RHLean.GateII.Harmonic



end Inline_GateII_Harmonic

section Inline_GateII_Components































open Finset

namespace RHLean.GateII.Components

open RHLean





theorem reserve_scalar_w {k : ℕ} (hk : 1 ≤ k) :
    (8 / 1000 : ℝ) < 1 / 2 - Real.log ((k : ℝ) * GateII.w k) - 492 / 1000 := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hwpos : 0 < GateII.w k := GateII.w_pos hk
  have hlt : (k : ℝ) * GateII.w k < 1 := by
    have h := GateII.w_lt_inv hk
    have h2 := mul_lt_mul_of_pos_left h hk0
    rwa [show (k : ℝ) * (1 / (k : ℝ)) = 1 by field_simp] at h2
  have hloglt : Real.log ((k : ℝ) * GateII.w k) < 0 := by
    have h := Real.log_lt_log (mul_pos hk0 hwpos) hlt
    rwa [Real.log_one] at h
  linarith




theorem reserve_corrected_w {E leak : ℝ} (hE : (8 / 1000 : ℝ) < E)
    (hleak : leak < 9 / 10 ^ 8) :
    (79999 / 10000000 : ℝ) < E - leak := by
  norm_num at *
  linarith






theorem master_P2_splice_certified (P θ r0 : ℝ) (c : ℂ) :
    P * ‖(r0 : ℂ) * c‖ ^ 2 + (-(P * ‖((θ * r0 : ℝ) : ℂ) * c‖ ^ 2))
      = ‖c‖ ^ 2 * (P * ‖(r0 : ℂ)‖ ^ 2 - P * ‖((θ * r0 : ℝ) : ℂ)‖ ^ 2) := by
  have hnorm (x : ℝ) : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  rw [norm_mul, norm_mul, mul_pow, mul_pow, hnorm r0, hnorm (θ * r0)]
  ring




theorem master_P2_lower {Pi0 P ε C θ : ℝ} (hP : Pi0 ≤ P) (hC : 0 ≤ C)
    (hθ : 0 ≤ 1 - θ ^ 2) (c : ℂ) :
    (1 - θ ^ 2) * Pi0 * (ε ^ 2 * C * ‖c‖ ^ 2)
      ≤ ‖c‖ ^ 2 * (P * (ε * Real.sqrt C) ^ 2 - P * (θ * (ε * Real.sqrt C)) ^ 2) := by
  have hsqrt : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC
  have hdiff : P * (ε * Real.sqrt C) ^ 2 - P * (θ * (ε * Real.sqrt C)) ^ 2
      = P * (ε ^ 2 * C) * (1 - θ ^ 2) := by
    have h1 : (ε * Real.sqrt C) ^ 2 = ε ^ 2 * C := by rw [mul_pow, hsqrt]
    have h2 : (θ * (ε * Real.sqrt C)) ^ 2 = θ ^ 2 * (ε ^ 2 * C) := by rw [mul_pow, h1]
    rw [h1, h2]
    ring
  rw [hdiff]
  have h1 : (1 - θ ^ 2) * Pi0 ≤ (1 - θ ^ 2) * P :=
    mul_le_mul_of_nonneg_left hP hθ
  calc (1 - θ ^ 2) * Pi0 * (ε ^ 2 * C * ‖c‖ ^ 2)
      ≤ (1 - θ ^ 2) * P * (ε ^ 2 * C * ‖c‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h1
          (mul_nonneg (mul_nonneg (sq_nonneg ε) hC) (sq_nonneg ‖c‖))
    _ = ‖c‖ ^ 2 * (P * (ε ^ 2 * C) * (1 - θ ^ 2)) := by ring







def MertensActive (k : ℕ) : Prop :=
  ∑ n ∈ (Finset.range (k + 1)).filter
      (fun n => 2 ≤ n ∧ ¬ n ∣ k ∧ ArithmeticFunction.vonMangoldt n ≠ 0),
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤ Real.log k





def HGroundDependency : Prop :=
  ∀ k : ℕ, 2 ≤ k → MertensActive k → 0 < Real.log k



theorem hground_dependency : HGroundDependency := by
  intro k hk _
  exact Real.log_pos (by exact_mod_cast (by omega : 1 < k))

end RHLean.GateII.Components



end Inline_GateII_Components

section Inline_GateII_Reduction








































open Set MeasureTheory
open scoped BigOperators
open scoped InnerProductSpace
open Matrix

namespace RHLean.GateII.Reduction

open RHLean
open RHLean.GateII.Collar
open RHLean.GateII.Harmonic



private lemma re_mul_star_comm__GateII_Reduction (u v : ℂ) : (u * star v).re = (v * star u).re := by
  change (u * starRingEnd ℂ v).re = (v * starRingEnd ℂ u).re
  rw [Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.conj_re, Complex.conj_im]
  ring

private lemma re_mul_star_self__GateII_Reduction (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  change (z * starRingEnd ℂ z).re = ‖z‖ ^ 2
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]





noncomputable def archBilin (a : ℝ) (f g : ℝ → ℂ) : ℝ :=
  (1 / 4) * ∫ x in Set.Ioo (-a) a, ∫ y in Set.Ioo (-a) a,
    ((f x - f y) * star (g x - g y)).re / ‖x - y‖



noncomputable def gammaBilin (a : ℝ) (f g : ℝ → ℂ) : ℝ :=
  (1 / 2) * (∫ x in Set.Ioo (-a) a, ∫ y in Set.Ioo (-a) a,
      gammaKernel ‖x - y‖ * (f x * star (g y)).re)
    + (1 / 2) * (∫ x in Set.Ioo (-a) a, ∫ y in Set.Ioo (-a) a,
      gammaKernel ‖x - y‖ * (g x * star (f y)).re)


noncomputable def potentialBilin (a : ℝ) (f g : ℝ → ℂ) : ℝ :=
  ∫ x in Set.Ioo (-a) a, endpointPotential a x * (f x * star (g x)).re


noncomputable def massBilin (a : ℝ) (f g : ℝ → ℂ) : ℝ :=
  ∫ x in Set.Ioo (-a) a, (f x * star (g x)).re


noncomputable def polarBilin (a : ℝ) (f g : ℝ → ℂ) : ℝ :=
  2 * (polarInner a f * star (polarInner a g)).re


noncomputable def shiftBilin (a : ℝ) (f g : ℝ → ℂ) : ℝ :=
  ∑ n ∈ arithSupport a, arithCoeff n *
    ((∫ x in Set.Ioo (-a) a, f x * star (g (x + shiftLength n))).re
      + (∫ x in Set.Ioo (-a) a, g x * star (f (x + shiftLength n))).re)



theorem archBilin_self (a : ℝ) (f : ℝ → ℂ) : archBilin a f f = archForm a f := by
  unfold archBilin archForm
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x _
  apply setIntegral_congr_fun measurableSet_Ioo
  intro y _
  simp only [re_mul_star_self__GateII_Reduction]

theorem gammaBilin_self (a : ℝ) (f : ℝ → ℂ) : gammaBilin a f f = gammaForm a f := by
  unfold gammaBilin gammaForm
  ring

theorem potentialBilin_self (a : ℝ) (f : ℝ → ℂ) :
    potentialBilin a f f = potentialForm a f := by
  unfold potentialBilin potentialForm
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x _
  simp only [re_mul_star_self__GateII_Reduction]

theorem massBilin_self (a : ℝ) (f : ℝ → ℂ) :
    massBilin a f f = ∫ x in Set.Ioo (-a) a, ‖f x‖ ^ 2 := by
  unfold massBilin
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x _
  simp only [re_mul_star_self__GateII_Reduction]

theorem polarBilin_self (a : ℝ) (f : ℝ → ℂ) : polarBilin a f f = polarForm a f := by
  unfold polarBilin polarForm
  rw [re_mul_star_self__GateII_Reduction]

theorem shiftBilin_self (a : ℝ) (f : ℝ → ℂ) : shiftBilin a f f = shiftForm a f := by
  unfold shiftBilin shiftForm
  apply Finset.sum_congr rfl
  intro n _
  ring



theorem archBilin_comm (a : ℝ) (f g : ℝ → ℂ) : archBilin a f g = archBilin a g f := by
  unfold archBilin
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x _
  apply setIntegral_congr_fun measurableSet_Ioo
  intro y _
  simp only [re_mul_star_comm__GateII_Reduction]

theorem gammaBilin_comm (a : ℝ) (f g : ℝ → ℂ) : gammaBilin a f g = gammaBilin a g f := by
  unfold gammaBilin
  rw [add_comm]

theorem potentialBilin_comm (a : ℝ) (f g : ℝ → ℂ) :
    potentialBilin a f g = potentialBilin a g f := by
  unfold potentialBilin
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x _
  simp only [re_mul_star_comm__GateII_Reduction]

theorem massBilin_comm (a : ℝ) (f g : ℝ → ℂ) : massBilin a f g = massBilin a g f := by
  unfold massBilin
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x _
  simp only [re_mul_star_comm__GateII_Reduction]

theorem polarBilin_comm (a : ℝ) (f g : ℝ → ℂ) : polarBilin a f g = polarBilin a g f := by
  unfold polarBilin
  rw [re_mul_star_comm__GateII_Reduction]

theorem shiftBilin_comm (a : ℝ) (f g : ℝ → ℂ) : shiftBilin a f g = shiftBilin a g f := by
  unfold shiftBilin
  apply Finset.sum_congr rfl
  intro n _
  rw [add_comm]




noncomputable def localizedBilin (a : ℝ) (f g : ℝ → ℂ) : ℝ :=
  archBilin a f g + physicalConstant * massBilin a f g + potentialBilin a f g
    - gammaBilin a f g - polarBilin a f g - shiftBilin a f g

theorem localizedBilin_self (a : ℝ) (f : ℝ → ℂ) :
    localizedBilin a f f = localizedForm a f := by
  unfold localizedBilin localizedForm
  rw [archBilin_self, massBilin_self, potentialBilin_self, gammaBilin_self,
    polarBilin_self, shiftBilin_self]

theorem localizedBilin_comm (a : ℝ) (f g : ℝ → ℂ) :
    localizedBilin a f g = localizedBilin a g f := by
  unfold localizedBilin
  rw [archBilin_comm, massBilin_comm, potentialBilin_comm, gammaBilin_comm,
    polarBilin_comm, shiftBilin_comm]


noncomputable def gramMatrix {ι : Type*} (a : ℝ) (φ : ι → ℝ → ℂ) : Matrix ι ι ℝ :=
  fun i j => localizedBilin a (φ i) (φ j)

theorem gramMatrix_isSymm {ι : Type*} (a : ℝ) (φ : ι → ℝ → ℂ) :
    (gramMatrix a φ).IsSymm :=
  Matrix.IsSymm.ext fun i j => (localizedBilin_comm a (φ i) (φ j)).symm

theorem gramMatrix_diagonal {ι : Type*} (a : ℝ) (φ : ι → ℝ → ℂ) (i : ι) :
    gramMatrix a φ i i = localizedForm a (φ i) :=
  localizedBilin_self a (φ i)




noncomputable def oldOldBlock {ι : Type*} (a : ℝ) (φ : ι → ℝ → ℂ) :
    Matrix ι ι ℝ :=
  gramMatrix a φ


noncomputable def oldCollarBlock {ιO ιC : Type*} (a : ℝ) (φO : ιO → ℝ → ℂ)
    (φC : ιC → ℝ → ℂ) : Matrix ιO ιC ℝ :=
  fun i j => localizedBilin a (φO i) (φC j)


noncomputable def collarCollarBlock {ι : Type*} (a : ℝ) (φ : ι → ℝ → ℂ) :
    Matrix ι ι ℝ :=
  gramMatrix a φ



theorem oldCollarBlock_transpose {ιO ιC : Type*} (a : ℝ) (φO : ιO → ℝ → ℂ)
    (φC : ιC → ℝ → ℂ) :
    Matrix.transpose (oldCollarBlock a φO φC) = oldCollarBlock a φC φO := by
  ext j i
  exact localizedBilin_comm a (φO i) (φC j)







private lemma mul_star_re_eq_zero_of_disjoint__GateII_Reduction {f g : ℝ → ℂ}
    (h : Disjoint (Function.support f) (Function.support g)) (x : ℝ) :
    (f x * star (g x)).re = 0 := by
  by_cases hf : f x = 0
  · rw [hf]
    simp
  · have hg : g x = 0 := by
      by_contra hg
      exact (Set.disjoint_left.mp h) (by simpa [Function.mem_support] using hf)
        (by simpa [Function.mem_support] using hg)
    rw [hg]
    simp

theorem massBilin_eq_zero_of_disjoint_support {a : ℝ} {f g : ℝ → ℂ}
    (h : Disjoint (Function.support f) (Function.support g)) :
    massBilin a f g = 0 := by
  unfold massBilin
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x _
  exact mul_star_re_eq_zero_of_disjoint__GateII_Reduction h x

theorem potentialBilin_eq_zero_of_disjoint_support {a : ℝ} {f g : ℝ → ℂ}
    (h : Disjoint (Function.support f) (Function.support g)) :
    potentialBilin a f g = 0 := by
  unfold potentialBilin
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x _
  rw [mul_star_re_eq_zero_of_disjoint__GateII_Reduction h x, mul_zero]





noncomputable def oldBasis (a : ℝ) (n : ℕ) : ℝ → ℂ := by
  classical
  exact Set.indicator (Set.Ioo (-a) a) (fun x => Y7Matrix.phiC n (x / a))


noncomputable def collarBasisRight (a b : ℝ) (n : ℕ) : ℝ → ℂ := by
  classical
  exact Set.indicator (Set.Ioo a b)
    (fun x => Y7Matrix.phiC n ((2 * x - (a + b)) / (b - a)))


noncomputable def collarBasisLeft (a b : ℝ) (n : ℕ) : ℝ → ℂ := by
  classical
  exact Set.indicator (Set.Ioo (-b) (-a))
    (fun x => Y7Matrix.phiC n ((2 * x + (a + b)) / (b - a)))




noncomputable def archBilinKernel (f g : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ((f p.1 - f p.2) * star (g p.1 - g p.2)).re / ‖p.1 - p.2‖


noncomputable def archBilinOO (a b : ℝ) (f g : ℝ → ℂ) : ℝ :=
  (1 / 4) * ∫ x in Set.Ioo (-a) a, ∫ y in Set.Ioo (-a) a, archBilinKernel f g (x, y)


noncomputable def archBilinOC (a b : ℝ) (f g : ℝ → ℂ) : ℝ :=
  (1 / 4) * ∫ x in Set.Ioo (-a) a, ∫ y in collarSet a b, archBilinKernel f g (x, y)


noncomputable def archBilinCO (a b : ℝ) (f g : ℝ → ℂ) : ℝ :=
  (1 / 4) * ∫ x in collarSet a b, ∫ y in Set.Ioo (-a) a, archBilinKernel f g (x, y)


noncomputable def archBilinCC (a b : ℝ) (f g : ℝ → ℂ) : ℝ :=
  (1 / 4) * ∫ x in collarSet a b, ∫ y in collarSet a b, archBilinKernel f g (x, y)





theorem archBilin_block_split {a b : ℝ} (hab : a ≤ b) (f g : ℝ → ℂ)
    (hK : IntegrableOn (archBilinKernel f g)
      (Set.Ioo (-b) b ×ˢ Set.Ioo (-b) b) (volume.prod volume)) :
    archBilin b f g
      = archBilinOO a b f g + archBilinOC a b f g
        + archBilinCO a b f g + archBilinCC a b f g := by
  have hsubO : Set.Ioo (-a) a ⊆ Set.Ioo (-b) b := fun x hx =>
    ⟨lt_of_le_of_lt (neg_le_neg hab) hx.1, lt_of_lt_of_le hx.2 hab⟩
  have hOC : Set.Ioo (-b) b = Set.Ioo (-a) a ∪ collarSet a b := by
    unfold collarSet
    exact (Set.union_sdiff_cancel hsubO).symm
  have hdisj : Disjoint (Set.Ioo (-a) a) (collarSet a b) := by
    unfold collarSet
    rw [Set.disjoint_left]
    rintro x hx ⟨-, hx'⟩
    exact hx' hx
  have hsplit := setIntegral_prod_block_split (K := archBilinKernel f g)
    hOC hdisj measurableSet_Ioo (measurableSet_Ioo.diff measurableSet_Ioo) hK
  have hL : archBilin b f g
      = (1 / 4) * ∫ x in Set.Ioo (-b) b, ∫ y in Set.Ioo (-b) b,
          archBilinKernel f g (x, y) := rfl
  rw [hL, hsplit]
  unfold archBilinOO archBilinOC archBilinCO archBilinCC
  ring





theorem archBilin_of_support {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℂ}
    (hK : IntegrableOn (archBilinKernel f g)
      (Set.Ioo (-b) b ×ˢ Set.Ioo (-b) b) (volume.prod volume))
    (hf : ∀ x ∉ Set.Ioo (-a) a, f x = 0)
    (hg : ∀ x ∉ collarSet a b, g x = 0) :
    archBilin b f g = archBilinOC a b f g + archBilinCO a b f g := by
  have hOO : archBilinOO a b f g = 0 := by
    unfold archBilinOO archBilinKernel
    rw [mul_eq_zero]
    right
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    rw [hg x (fun h => h.2 hx), hg y (fun h => h.2 hy)]
    simp
  have hCC : archBilinCC a b f g = 0 := by
    unfold archBilinCC archBilinKernel
    rw [mul_eq_zero]
    right
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    rw [hf x (fun h => hx.2 h), hf y (fun h => hy.2 h)]
    simp
  rw [archBilin_block_split hab f g hK, hOO, hCC]
  ring








theorem integrableOn_gammaBilinKernel_of_bound {b B : ℝ} {f g : ℝ → ℂ}
    (hB : 0 ≤ B) (hf : ∀ x, ‖f x‖ ≤ B) (hg : ∀ x, ‖g x‖ ≤ B)
    (hfm : Measurable f) (hgm : Measurable g) :
    IntegrableOn (fun p : ℝ × ℝ => gammaKernel ‖p.1 - p.2‖ * (f p.1 * star (g p.2)).re)
      (Set.Ioo (-b) b ×ˢ Set.Ioo (-b) b) := by
  set C := Real.exp (2 * |b|) / 2 + Real.exp ((2 * |b|) / 2) / 4 with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    positivity
  refine IntegrableOn.of_bound ?hfin ?hmeas (C * B ^ 2) ?hbound
  · change (volume.prod volume) (Set.Ioo (-b) b ×ˢ Set.Ioo (-b) b) < ⊤
    rw [Measure.prod_prod, Real.volume_Ioo]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · have hre : Measurable (fun p : ℝ × ℝ => (f p.1 * star (g p.2)).re) :=
      Complex.continuous_re.measurable.comp
        ((hfm.comp measurable_fst).mul (continuous_star.measurable.comp (hgm.comp measurable_snd)))
    exact ((measurable_gammaKernel.comp
      ((continuous_fst.sub continuous_snd).norm.measurable)).mul hre).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    have hp1 : |p.1| ≤ |b| := by
      have hb : b ≤ |b| := le_abs_self b
      have hnb : -b ≤ |b| := neg_le_abs b
      rw [abs_le]
      exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
    have hp2 : |p.2| ≤ |b| := by
      have hb : b ≤ |b| := le_abs_self b
      have hnb : -b ≤ |b| := neg_le_abs b
      rw [abs_le]
      exact ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
    have hdistb : ‖p.1 - p.2‖ ≤ 2 * |b| := by
      calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
        _ = |p.1| + |p.2| := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 2 * |b| := by linarith
    have hgB : |gammaKernel ‖p.1 - p.2‖| ≤ C := by
      rw [hCdef]
      exact gammaKernel_abs_le (by positivity) ⟨norm_nonneg _, hdistb⟩
    have hprod : |(f p.1 * star (g p.2)).re| ≤ B ^ 2 := by
      calc |(f p.1 * star (g p.2)).re| ≤ ‖f p.1 * star (g p.2)‖ :=
            Complex.abs_re_le_norm _
        _ = ‖f p.1‖ * ‖star (g p.2)‖ := norm_mul _ _
        _ = ‖f p.1‖ * ‖g p.2‖ := by rw [norm_star]
        _ ≤ B * B := mul_le_mul (hf p.1) (hg p.2) (norm_nonneg _) hB
        _ = B ^ 2 := by ring
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hgB hprod (abs_nonneg _) hC0








theorem integrableOn_archBilinKernel_of_lipschitz {c d Kf Kg : ℝ} {f g : ℝ → ℂ}
    (hcd : c ≤ d) (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg)
    (hf : ∀ x ∈ Set.Ioo c d, ∀ y ∈ Set.Ioo c d, ‖f x - f y‖ ≤ Kf * ‖x - y‖)
    (hg : ∀ x ∈ Set.Ioo c d, ∀ y ∈ Set.Ioo c d, ‖g x - g y‖ ≤ Kg * ‖x - y‖)
    (hfm : Measurable f) (hgm : Measurable g) :
    IntegrableOn (archBilinKernel f g) (Set.Ioo c d ×ˢ Set.Ioo c d) := by
  have hconst : 0 ≤ Kf * Kg * (d - c) :=
    mul_nonneg (mul_nonneg hKf hKg) (sub_nonneg.mpr hcd)
  refine IntegrableOn.of_bound ?hfin ?hmeas (Kf * Kg * (d - c)) ?hbound
  · change (volume.prod volume) (Set.Ioo c d ×ˢ Set.Ioo c d) < ⊤
    rw [Measure.prod_prod, Real.volume_Ioo]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · have hre : Measurable (fun p : ℝ × ℝ =>
        ((f p.1 - f p.2) * star (g p.1 - g p.2)).re) :=
      Complex.continuous_re.measurable.comp
        (((hfm.comp measurable_fst).sub (hfm.comp measurable_snd)).mul
          (continuous_star.measurable.comp
            ((hgm.comp measurable_fst).sub (hgm.comp measurable_snd))))
    exact (hre.div ((continuous_fst.sub continuous_snd).norm.measurable)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    have hp1 : p.1 ∈ Set.Ioo c d := hp.1
    have hp2 : p.2 ∈ Set.Ioo c d := hp.2
    have hnum : ‖(f p.1 - f p.2) * star (g p.1 - g p.2)‖
        ≤ (Kf * Kg) * ‖p.1 - p.2‖ ^ 2 := by
      rw [norm_mul, norm_star]
      calc ‖f p.1 - f p.2‖ * ‖g p.1 - g p.2‖
          ≤ (Kf * ‖p.1 - p.2‖) * (Kg * ‖p.1 - p.2‖) :=
            mul_le_mul (hf p.1 hp1 p.2 hp2) (hg p.1 hp1 p.2 hp2)
              (norm_nonneg _) (mul_nonneg hKf (norm_nonneg _))
        _ = (Kf * Kg) * ‖p.1 - p.2‖ ^ 2 := by ring
    have hre_le : |((f p.1 - f p.2) * star (g p.1 - g p.2)).re|
        ≤ (Kf * Kg) * ‖p.1 - p.2‖ ^ 2 :=
      le_trans (Complex.abs_re_le_norm _) hnum
    have hdistb : ‖p.1 - p.2‖ ≤ d - c := by
      rw [Real.norm_eq_abs]
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith [hp1.1, hp2.2]
      · linarith [hp1.2, hp2.1]
    unfold archBilinKernel
    rw [Real.norm_eq_abs, abs_div]
    by_cases hd : p.1 = p.2
    · rw [hd]
      simp only [sub_self, norm_zero, div_zero, abs_zero]
      exact hconst
    · have hpos : 0 < ‖p.1 - p.2‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr hd)
      rw [abs_of_pos hpos]
      calc |((f p.1 - f p.2) * star (g p.1 - g p.2)).re| / ‖p.1 - p.2‖
          ≤ ((Kf * Kg) * ‖p.1 - p.2‖ ^ 2) / ‖p.1 - p.2‖ :=
            div_le_div_of_nonneg_right hre_le hpos.le
        _ = (Kf * Kg) * ‖p.1 - p.2‖ := by
            rw [div_eq_iff hpos.ne']
            ring
        _ ≤ (Kf * Kg) * (d - c) :=
            mul_le_mul_of_nonneg_left hdistb (mul_nonneg hKf hKg)






theorem integrableOn_sub_rpow_neg_half {c r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => (c - x) ^ (-(1 / 2) : ℝ)) (Set.Ioo (c - r) c) := by
  have hpow : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2) : ℝ)) (Set.Ioo (0 : ℝ) r) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hr]
    norm_num
  have himage : (fun x : ℝ => c - x) '' Set.Ioo (c - r) c = Set.Ioo (0 : ℝ) r := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    · intro hu
      exact ⟨c - u, ⟨by linarith [hu.2], by linarith [hu.1]⟩, by ring⟩
  have h := (Measure.measurePreserving_sub_left volume c).integrableOn_image
    (measurableEmbedding_subLeft c) (s := Set.Ioo (c - r) c)
    (f := fun u : ℝ => u ^ (-(1 / 2) : ℝ))
  rw [himage] at h
  exact h.mp hpow



theorem integrableOn_add_rpow_neg_half {c d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun y : ℝ => (y - c) ^ (-(1 / 2) : ℝ)) (Set.Ioo c (c + d)) := by
  have hpow : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2) : ℝ)) (Set.Ioo (0 : ℝ) d) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hd]
    norm_num
  have himage : (fun y : ℝ => y - c) '
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · intro hv
      exact ⟨v + c, ⟨by linarith [hv.1], by linarith [hv.2]⟩, by ring⟩
  have h := (measurePreserving_sub_right volume c).integrableOn_image
    (measurableEmbedding_subRight c) (s := Set.Ioo c (c + d))
    (f := fun u : ℝ => u ^ (-(1 / 2) : ℝ))
  rw [himage] at h
  exact h.mp hpow






theorem integrableOn_inv_norm_corner {c r d : ℝ} (hr : 0 < r) (hd : 0 < d) :
    IntegrableOn (fun p : ℝ × ℝ => (1 : ℝ) / ‖p.1 - p.2‖)
      (Set.Ioo (c - r) c ×ˢ Set.Ioo c (c + d)) (volume.prod volume) := by
  have hleft := integrableOn_sub_rpow_neg_half (c := c) hr
  have hright := integrableOn_add_rpow_neg_half (c := c) hd
  have hdom : IntegrableOn
      (fun p : ℝ × ℝ => (c - p.1) ^ (-(1 / 2) : ℝ) * (p.2 - c) ^ (-(1 / 2) : ℝ))
      (Set.Ioo (c - r) c ×ˢ Set.Ioo c (c + d)) (volume.prod volume) := by
    rw [IntegrableOn] at hleft hright
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hleft.mul_prod hright
  rw [IntegrableOn] at hdom ⊢
  refine hdom.mono' ?hmeas ?hbound
  · exact (measurable_const.div
      (((continuous_fst.sub continuous_snd).norm).measurable)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    have hp1 : p.1 < c := hp.1.2
    have hp2 : c < p.2 := hp.2.1
    have hu : 0 < c - p.1 := sub_pos.mpr hp1
    have hv : 0 < p.2 - c := sub_pos.mpr hp2
    have hdist : ‖p.1 - p.2‖ = (c - p.1) + (p.2 - c) := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have hsqrt_pos : 0 < Real.sqrt ((c - p.1) * (p.2 - c)) :=
      Real.sqrt_pos.mpr (mul_pos hu hv)
    have hgm : Real.sqrt ((c - p.1) * (p.2 - c)) ≤ (c - p.1) + (p.2 - c) := by
      have hsq : 0 ≤ (Real.sqrt (c - p.1) - Real.sqrt (p.2 - c)) ^ 2 := sq_nonneg _
      have h1 : Real.sqrt (c - p.1) ^ 2 = c - p.1 := Real.sq_sqrt hu.le
      have h2 : Real.sqrt (p.2 - c) ^ 2 = p.2 - c := Real.sq_sqrt hv.le
      have h3 : Real.sqrt ((c - p.1) * (p.2 - c))
          = Real.sqrt (c - p.1) * Real.sqrt (p.2 - c) := Real.sqrt_mul hu.le _
      have hsu : 0 ≤ Real.sqrt (c - p.1) := Real.sqrt_nonneg _
      have hsv : 0 ≤ Real.sqrt (p.2 - c) := Real.sqrt_nonneg _
      nlinarith
    have hpow : (c - p.1) ^ (-(1 / 2) : ℝ) * (p.2 - c) ^ (-(1 / 2) : ℝ)
        = 1 / Real.sqrt ((c - p.1) * (p.2 - c)) := by
      rw [Real.rpow_neg hu.le, Real.rpow_neg hv.le, ← Real.sqrt_eq_rpow,
        ← Real.sqrt_eq_rpow, ← mul_inv, ← Real.sqrt_mul hu.le, one_div]
    rw [Real.norm_eq_abs, hdist, abs_of_nonneg (by positivity), hpow]
    exact one_div_le_one_div_of_le hsqrt_pos hgm



theorem integrableOn_inv_norm_corner_swap {c r d : ℝ} (hr : 0 < r) (hd : 0 < d) :
    IntegrableOn (fun p : ℝ × ℝ => (1 : ℝ) / ‖p.1 - p.2‖)
      (Set.Ioo c (c + d) ×ˢ Set.Ioo (c - r) c) (volume.prod volume) := by
  have h := (integrableOn_inv_norm_corner (c := c) hr hd).swap
  simpa [Function.comp_def, abs_sub_comm] using h


theorem integrableOn_inv_norm_old_right {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IntegrableOn (fun p : ℝ × ℝ => (1 : ℝ) / ‖p.1 - p.2‖)
      (Set.Ioo (-a) a ×ˢ Set.Ioo a b) (volume.prod volume) := by
  have h := integrableOn_inv_norm_corner (c := a) (r := 2 * a) (d := b - a)
    (by linarith) (by linarith)
  rw [show a - 2 * a = -a by ring, show a + (b - a) = b by ring] at h
  exact h


theorem integrableOn_inv_norm_old_left {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IntegrableOn (fun p : ℝ × ℝ => (1 : ℝ) / ‖p.1 - p.2‖)
      (Set.Ioo (-a) a ×ˢ Set.Ioo (-b) (-a)) (volume.prod volume) := by
  have h := integrableOn_inv_norm_corner_swap (c := -a) (r := b - a) (d := 2 * a)
    (by linarith) (by linarith)
  rw [show -a + 2 * a = a by ring, show -a - (b - a) = -b by ring] at h
  exact h


theorem integrableOn_inv_norm_right_old {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IntegrableOn (fun p : ℝ × ℝ => (1 : ℝ) / ‖p.1 - p.2‖)
      (Set.Ioo a b ×ˢ Set.Ioo (-a) a) (volume.prod volume) := by
  have h := integrableOn_inv_norm_corner_swap (c := a) (r := 2 * a) (d := b - a)
    (by linarith) (by linarith)
  rw [show a + (b - a) = b by ring, show a - 2 * a = -a by ring] at h
  exact h


theorem integrableOn_inv_norm_left_old {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IntegrableOn (fun p : ℝ × ℝ => (1 : ℝ) / ‖p.1 - p.2‖)
      (Set.Ioo (-b) (-a) ×ˢ Set.Ioo (-a) a) (volume.prod volume) := by
  have h := integrableOn_inv_norm_corner (c := -a) (r := b - a) (d := 2 * a)
    (by linarith) (by linarith)
  rw [show -a - (b - a) = -b by ring, show -a + 2 * a = a by ring] at h
  exact h






theorem integrableOn_archBilinKernel_of_bound_of_corner {s t : Set ℝ}
    (hcorner : IntegrableOn (fun p : ℝ × ℝ => (1 : ℝ) / ‖p.1 - p.2‖)
      (s ×ˢ t) (volume.prod volume))
    {Bf Bg : ℝ} (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg) {f g : ℝ → ℂ}
    (hf : ∀ x, ‖f x‖ ≤ Bf) (hg : ∀ x, ‖g x‖ ≤ Bg)
    (hfm : Measurable f) (hgm : Measurable g) :
    IntegrableOn (archBilinKernel f g) (s ×ˢ t) (volume.prod volume) := by
  have hdom : IntegrableOn (fun p : ℝ × ℝ => (4 * Bf * Bg) / ‖p.1 - p.2‖)
      (s ×ˢ t) (volume.prod volume) := by
    rw [IntegrableOn] at hcorner ⊢
    simpa [div_eq_mul_inv, one_div] using hcorner.const_mul (4 * Bf * Bg)
  rw [IntegrableOn] at hdom ⊢
  refine hdom.mono' ?hmeas ?hbound
  · have hre : Measurable (fun p : ℝ × ℝ =>
        ((f p.1 - f p.2) * star (g p.1 - g p.2)).re) :=
      Complex.continuous_re.measurable.comp
        (((hfm.comp measurable_fst).sub (hfm.comp measurable_snd)).mul
          (continuous_star.measurable.comp
            ((hgm.comp measurable_fst).sub (hgm.comp measurable_snd))))
    exact (hre.div ((continuous_fst.sub continuous_snd).norm.measurable)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by
      have hnum : ‖(f p.1 - f p.2) * star (g p.1 - g p.2)‖ ≤ 4 * Bf * Bg := by
        rw [norm_mul, norm_star]
        calc ‖f p.1 - f p.2‖ * ‖g p.1 - g p.2‖
            ≤ (2 * Bf) * (2 * Bg) := by
              refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
              · calc ‖f p.1 - f p.2‖ ≤ ‖f p.1‖ + ‖f p.2‖ := norm_sub_le _ _
                  _ ≤ Bf + Bf := add_le_add (hf p.1) (hf p.2)
                  _ = 2 * Bf := by ring
              · calc ‖g p.1 - g p.2‖ ≤ ‖g p.1‖ + ‖g p.2‖ := norm_sub_le _ _
                  _ ≤ Bg + Bg := add_le_add (hg p.1) (hg p.2)
                  _ = 2 * Bg := by ring
          _ = 4 * Bf * Bg := by ring
      have hre_le : |((f p.1 - f p.2) * star (g p.1 - g p.2)).re| ≤ 4 * Bf * Bg :=
        le_trans (Complex.abs_re_le_norm _) hnum
      unfold archBilinKernel
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg _)]
      exact div_le_div_of_nonneg_right hre_le (norm_nonneg _)



theorem integrableOn_archBilinKernel_old_rightCollar {a b Bf Bg : ℝ}
    (ha : 0 < a) (hab : a < b) (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    {f g : ℝ → ℂ} (hf : ∀ x, ‖f x‖ ≤ Bf) (hg : ∀ x, ‖g x‖ ≤ Bg)
    (hfm : Measurable f) (hgm : Measurable g) :
    IntegrableOn (archBilinKernel f g) (Set.Ioo (-a) a ×ˢ Set.Ioo a b) :=
  integrableOn_archBilinKernel_of_bound_of_corner
    (integrableOn_inv_norm_old_right ha hab) hBf hBg hf hg hfm hgm



theorem integrableOn_archBilinKernel_old_leftCollar {a b Bf Bg : ℝ}
    (ha : 0 < a) (hab : a < b) (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    {f g : ℝ → ℂ} (hf : ∀ x, ‖f x‖ ≤ Bf) (hg : ∀ x, ‖g x‖ ≤ Bg)
    (hfm : Measurable f) (hgm : Measurable g) :
    IntegrableOn (archBilinKernel f g) (Set.Ioo (-a) a ×ˢ Set.Ioo (-b) (-a)) :=
  integrableOn_archBilinKernel_of_bound_of_corner
    (integrableOn_inv_norm_old_left ha hab) hBf hBg hf hg hfm hgm



theorem integrableOn_archBilinKernel_rightCollar_old {a b Bf Bg : ℝ}
    (ha : 0 < a) (hab : a < b) (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    {f g : ℝ → ℂ} (hf : ∀ x, ‖f x‖ ≤ Bf) (hg : ∀ x, ‖g x‖ ≤ Bg)
    (hfm : Measurable f) (hgm : Measurable g) :
    IntegrableOn (archBilinKernel f g) (Set.Ioo a b ×ˢ Set.Ioo (-a) a) :=
  integrableOn_archBilinKernel_of_bound_of_corner
    (integrableOn_inv_norm_right_old ha hab) hBf hBg hf hg hfm hgm



theorem integrableOn_archBilinKernel_leftCollar_old {a b Bf Bg : ℝ}
    (ha : 0 < a) (hab : a < b) (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    {f g : ℝ → ℂ} (hf : ∀ x, ‖f x‖ ≤ Bf) (hg : ∀ x, ‖g x‖ ≤ Bg)
    (hfm : Measurable f) (hgm : Measurable g) :
    IntegrableOn (archBilinKernel f g) (Set.Ioo (-b) (-a) ×ˢ Set.Ioo (-a) a) :=
  integrableOn_archBilinKernel_of_bound_of_corner
    (integrableOn_inv_norm_left_old ha hab) hBf hBg hf hg hfm hgm



theorem collarSet_eq_union_insert {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    collarSet a b = Set.Ioo a b ∪ Set.Ioo (-b) (-a) ∪ ({a, -a} : Set ℝ) := by
  ext x
  constructor
  · intro hx
    rw [collarSet, Set.mem_diff] at hx
    obtain ⟨hxb, hxa⟩ := hx
    rw [Set.mem_Ioo] at hxb
    have hx' : x ≤ -a ∨ a ≤ x := by
      by_contra h
      push_neg at h
      exact hxa (Set.mem_Ioo.mpr ⟨h.1, h.2⟩)
    rcases hx' with hx' | hx'
    · rcases eq_or_lt_of_le hx' with hxe | hxlt
      · exact Or.inr (by rw [hxe]; simp)
      · exact Or.inl (Or.inr (Set.mem_Ioo.mpr ⟨hxb.1, hxlt⟩))
    · rcases eq_or_lt_of_le hx' with hxe | hxlt
      · exact Or.inr (by rw [hxe]; simp)
      · exact Or.inl (Or.inl (Set.mem_Ioo.mpr ⟨hxlt, hxb.2⟩))
  · intro hx
    rw [collarSet, Set.mem_diff]
    rcases hx with (hx | hx) | hx
    · rw [Set.mem_Ioo] at hx
      exact ⟨⟨by linarith [hx.1], hx.2⟩, fun h => by linarith [h.2, hx.1]⟩
    · rw [Set.mem_Ioo] at hx
      exact ⟨⟨hx.1, by linarith [hx.2]⟩, fun h => by linarith [h.1, hx.2]⟩
    · rcases hx with rfl | rfl
      · exact ⟨⟨by linarith, by linarith⟩, fun h => by linarith [h.2]⟩
      · exact ⟨⟨by linarith, by linarith⟩, fun h => by linarith [h.1]⟩



theorem integrableOn_archBilinKernel_old_collar {a b Bf Bg : ℝ}
    (ha : 0 < a) (hab : a < b) (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    {f g : ℝ → ℂ} (hf : ∀ x, ‖f x‖ ≤ Bf) (hg : ∀ x, ‖g x‖ ≤ Bg)
    (hfm : Measurable f) (hgm : Measurable g) :
    IntegrableOn (archBilinKernel f g) (Set.Ioo (-a) a ×ˢ collarSet a b) := by
  have hset : Set.Ioo (-a) a ×ˢ collarSet a b
      = (Set.Ioo (-a) a ×ˢ Set.Ioo a b
          ∪ Set.Ioo (-a) a ×ˢ Set.Ioo (-b) (-a))
        ∪ Set.Ioo (-a) a ×ˢ ({a, -a} : Set ℝ) := by
    rw [collarSet_eq_union_insert ha hab, Set.prod_union, Set.prod_union]
  rw [hset]
  refine IntegrableOn.union (IntegrableOn.union ?_ ?_) ?_
  · exact integrableOn_archBilinKernel_old_rightCollar ha hab hBf hBg hf hg hfm hgm
  · exact integrableOn_archBilinKernel_old_leftCollar ha hab hBf hBg hf hg hfm hgm
  · refine IntegrableOn.of_measure_zero ?_
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod]
    have hfin : ({a, -a} : Set ℝ).Finite := (Set.finite_singleton (-a)).insert a
    simp [hfin.measure_zero volume]


theorem integrableOn_archBilinKernel_collar_old {a b Bf Bg : ℝ}
    (ha : 0 < a) (hab : a < b) (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    {f g : ℝ → ℂ} (hf : ∀ x, ‖f x‖ ≤ Bf) (hg : ∀ x, ‖g x‖ ≤ Bg)
    (hfm : Measurable f) (hgm : Measurable g) :
    IntegrableOn (archBilinKernel f g) (collarSet a b ×ˢ Set.Ioo (-a) a) := by
  have hset : collarSet a b ×ˢ Set.Ioo (-a) a
      = (Set.Ioo a b ×ˢ Set.Ioo (-a) a
          ∪ Set.Ioo (-b) (-a) ×ˢ Set.Ioo (-a) a)
        ∪ ({a, -a} : Set ℝ) ×ˢ Set.Ioo (-a) a := by
    rw [collarSet_eq_union_insert ha hab, Set.union_prod, Set.union_prod]
  rw [hset]
  refine IntegrableOn.union (IntegrableOn.union ?_ ?_) ?_
  · exact integrableOn_archBilinKernel_rightCollar_old ha hab hBf hBg hf hg hfm hgm
  · exact integrableOn_archBilinKernel_leftCollar_old ha hab hBf hBg hf hg hfm hgm
  · refine IntegrableOn.of_measure_zero ?_
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod]
    have hfin : ({a, -a} : Set ℝ).Finite := (Set.finite_singleton (-a)).insert a
    simp [hfin.measure_zero volume]





theorem exists_bound_phiC (n : ℕ) :
    ∃ B : ℝ, ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖Y7Matrix.phiC n t‖ ≤ B := by
  have hcont : Continuous (fun t : ℝ => Y7Matrix.phiC n t) := by
    have h : (fun t : ℝ => Y7Matrix.phiC n t)
        = fun t : ℝ => (((Y7Legendre.phi n).eval t : ℝ) : ℂ) := by
      funext x
      exact Y7Matrix.phiC_apply n x
    rw [h]
    exact Complex.continuous_ofReal.comp (Y7Legendre.phi n).continuous
  obtain ⟨x0, -, hx0⟩ := isCompact_Icc.exists_isMaxOn
    (s := Set.Icc (-1 : ℝ) 1)
    (show (Set.Icc (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩)
    hcont.continuousOn.norm
  exact ⟨‖Y7Matrix.phiC n x0‖, fun t ht => hx0 ht⟩


theorem oldBasis_norm_le {a B : ℝ} (ha : 0 < a) {n : ℕ}
    (hB : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖Y7Matrix.phiC n t‖ ≤ B) :
    ∀ x, ‖oldBasis a n x‖ ≤ B := by
  intro x
  by_cases hx : x ∈ Set.Ioo (-a) a
  · have hxa : x / a ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Ioo] at hx
      rw [Set.mem_Icc]
      constructor
      · rw [le_div_iff₀ ha]
        linarith [hx.1]
      · rw [div_le_iff₀ ha]
        linarith [hx.2]
    simpa [oldBasis, hx] using hB (x / a) hxa
  · have hB0 : 0 ≤ B :=
      le_trans (norm_nonneg _) (hB 0 ⟨by norm_num, by norm_num⟩)
    simp [oldBasis, hx, hB0]


theorem collarBasisRight_norm_le {a b B : ℝ} (hab : a < b) {n : ℕ}
    (hB : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖Y7Matrix.phiC n t‖ ≤ B) :
    ∀ x, ‖collarBasisRight a b n x‖ ≤ B := by
  intro x
  by_cases hx : x ∈ Set.Ioo a b
  · have hba : 0 < b - a := sub_pos.mpr hab
    have hxa : (2 * x - (a + b)) / (b - a) ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Ioo] at hx
      rw [Set.mem_Icc]
      constructor
      · rw [le_div_iff₀ hba]
        linarith [hx.1]
      · rw [div_le_iff₀ hba]
        linarith [hx.2]
    simpa [collarBasisRight, hx] using hB ((2 * x - (a + b)) / (b - a)) hxa
  · have hB0 : 0 ≤ B :=
      le_trans (norm_nonneg _) (hB 0 ⟨by norm_num, by norm_num⟩)
    simp [collarBasisRight, hx, hB0]


theorem collarBasisLeft_norm_le {a b B : ℝ} (hab : a < b) {n : ℕ}
    (hB : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖Y7Matrix.phiC n t‖ ≤ B) :
    ∀ x, ‖collarBasisLeft a b n x‖ ≤ B := by
  intro x
  by_cases hx : x ∈ Set.Ioo (-b) (-a)
  · have hba : 0 < b - a := sub_pos.mpr hab
    have hxa : (2 * x + (a + b)) / (b - a) ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Ioo] at hx
      rw [Set.mem_Icc]
      constructor
      · rw [le_div_iff₀ hba]
        linarith [hx.1]
      · rw [div_le_iff₀ hba]
        linarith [hx.2]
    simpa [collarBasisLeft, hx] using hB ((2 * x + (a + b)) / (b - a)) hxa
  · have hB0 : 0 ≤ B :=
      le_trans (norm_nonneg _) (hB 0 ⟨by norm_num, by norm_num⟩)
    simp [collarBasisLeft, hx, hB0]





theorem exists_lipschitz_phiC (n : ℕ) :
    ∃ K : NNReal, LipschitzOnWith K (fun t : ℝ => Y7Matrix.phiC n t)
      (Set.Icc (-1 : ℝ) 1) := by
  have hcd : ContDiff ℝ 1 (fun t : ℝ => Y7Matrix.phiC n t) := by
    have hpoly : ContDiff ℝ 1 (fun t : ℝ => (Y7Legendre.phi n).eval t) := by
      simpa [Polynomial.aeval_def, Polynomial.eval₂_id] using
        (Y7Legendre.phi n).contDiff_aeval (𝕜 := ℝ) (n := 1)
    simpa [Y7Matrix.phiC, Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp hpoly
  exact (hcd.contDiffOn (s := Set.Icc (-1 : ℝ) 1)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc


theorem oldBasis_lipschitz {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Set.Ioo (-a) a, ∀ y ∈ Set.Ioo (-a) a,
      ‖oldBasis a n x - oldBasis a n y‖ ≤ K * ‖x - y‖ := by
  obtain ⟨K, hK⟩ := exists_lipschitz_phiC n
  refine ⟨(K : ℝ) / a, by positivity, ?_⟩
  intro x hx y hy
  have hxI : x / a ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Set.mem_Ioo] at hx
    rw [Set.mem_Icc]
    exact ⟨by rw [le_div_iff₀ ha]; linarith [hx.1],
      by rw [div_le_iff₀ ha]; linarith [hx.2]⟩
  have hyI : y / a ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Set.mem_Ioo] at hy
    rw [Set.mem_Icc]
    exact ⟨by rw [le_div_iff₀ ha]; linarith [hy.1],
      by rw [div_le_iff₀ ha]; linarith [hy.2]⟩
  have hxy : ‖Y7Matrix.phiC n (x / a) - Y7Matrix.phiC n (y / a)‖
      ≤ (K : ℝ) * ‖x / a - y / a‖ := by
    have h := (lipschitzOnWith_iff_dist_le_mul.mp hK) (x / a) hxI (y / a) hyI
    simpa [dist_eq_norm] using h
  have hxval : oldBasis a n x = Y7Matrix.phiC n (x / a) := by simp [oldBasis, hx]
  have hyval : oldBasis a n y = Y7Matrix.phiC n (y / a) := by simp [oldBasis, hy]
  rw [hxval, hyval]
  calc ‖Y7Matrix.phiC n (x / a) - Y7Matrix.phiC n (y / a)‖
      ≤ (K : ℝ) * ‖x / a - y / a‖ := hxy
    _ = ((K : ℝ) / a) * ‖x - y‖ := by
        rw [div_sub_div_same, norm_div, Real.norm_of_nonneg ha.le]
        ring



theorem collarBasisRight_lipschitz {a b : ℝ} (hab : a < b) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b,
      ‖collarBasisRight a b n x - collarBasisRight a b n y‖ ≤ K * ‖x - y‖ := by
  obtain ⟨K, hK⟩ := exists_lipschitz_phiC n
  have hba : 0 < b - a := sub_pos.mpr hab
  refine ⟨2 * (K : ℝ) / (b - a), by positivity, ?_⟩
  intro x hx y hy
  have hxI : (2 * x - (a + b)) / (b - a) ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Set.mem_Ioo] at hx
    rw [Set.mem_Icc]
    exact ⟨by rw [le_div_iff₀ hba]; linarith [hx.1],
      by rw [div_le_iff₀ hba]; linarith [hx.2]⟩
  have hyI : (2 * y - (a + b)) / (b - a) ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Set.mem_Ioo] at hy
    rw [Set.mem_Icc]
    exact ⟨by rw [le_div_iff₀ hba]; linarith [hy.1],
      by rw [div_le_iff₀ hba]; linarith [hy.2]⟩
  have hxy : ‖Y7Matrix.phiC n ((2 * x - (a + b)) / (b - a))
        - Y7Matrix.phiC n ((2 * y - (a + b)) / (b - a))‖
      ≤ (K : ℝ) * ‖(2 * x - (a + b)) / (b - a)
          - (2 * y - (a + b)) / (b - a)‖ := by
    have h := (lipschitzOnWith_iff_dist_le_mul.mp hK) _ hxI _ hyI
    simpa [dist_eq_norm] using h
  have hxval : collarBasisRight a b n x
      = Y7Matrix.phiC n ((2 * x - (a + b)) / (b - a)) := by
    simp [collarBasisRight, hx]
  have hyval : collarBasisRight a b n y
      = Y7Matrix.phiC n ((2 * y - (a + b)) / (b - a)) := by
    simp [collarBasisRight, hy]
  rw [hxval, hyval]
  calc ‖Y7Matrix.phiC n ((2 * x - (a + b)) / (b - a))
        - Y7Matrix.phiC n ((2 * y - (a + b)) / (b - a))‖
      ≤ (K : ℝ) * ‖(2 * x - (a + b)) / (b - a)
          - (2 * y - (a + b)) / (b - a)‖ := hxy
    _ = (2 * (K : ℝ) / (b - a)) * ‖x - y‖ := by
        rw [div_sub_div_same]
        have hnum : 2 * x - (a + b) - (2 * y - (a + b)) = 2 * (x - y) := by ring
        rw [hnum, norm_div, norm_mul,
          Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          Real.norm_of_nonneg hba.le]
        ring


theorem collarBasisLeft_lipschitz {a b : ℝ} (hab : a < b) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Set.Ioo (-b) (-a), ∀ y ∈ Set.Ioo (-b) (-a),
      ‖collarBasisLeft a b n x - collarBasisLeft a b n y‖ ≤ K * ‖x - y‖ := by
  obtain ⟨K, hK⟩ := exists_lipschitz_phiC n
  have hba : 0 < b - a := sub_pos.mpr hab
  refine ⟨2 * (K : ℝ) / (b - a), by positivity, ?_⟩
  intro x hx y hy
  have hxI : (2 * x + (a + b)) / (b - a) ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Set.mem_Ioo] at hx
    rw [Set.mem_Icc]
    exact ⟨by rw [le_div_iff₀ hba]; linarith [hx.1],
      by rw [div_le_iff₀ hba]; linarith [hx.2]⟩
  have hyI : (2 * y + (a + b)) / (b - a) ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Set.mem_Ioo] at hy
    rw [Set.mem_Icc]
    exact ⟨by rw [le_div_iff₀ hba]; linarith [hy.1],
      by rw [div_le_iff₀ hba]; linarith [hy.2]⟩
  have hxy : ‖Y7Matrix.phiC n ((2 * x + (a + b)) / (b - a))
        - Y7Matrix.phiC n ((2 * y + (a + b)) / (b - a))‖
      ≤ (K : ℝ) * ‖(2 * x + (a + b)) / (b - a)
          - (2 * y + (a + b)) / (b - a)‖ := by
    have h := (lipschitzOnWith_iff_dist_le_mul.mp hK) _ hxI _ hyI
    simpa [dist_eq_norm] using h
  have hxval : collarBasisLeft a b n x
      = Y7Matrix.phiC n ((2 * x + (a + b)) / (b - a)) := by
    simp [collarBasisLeft, hx]
  have hyval : collarBasisLeft a b n y
      = Y7Matrix.phiC n ((2 * y + (a + b)) / (b - a)) := by
    simp [collarBasisLeft, hy]
  rw [hxval, hyval]
  calc ‖Y7Matrix.phiC n ((2 * x + (a + b)) / (b - a))
        - Y7Matrix.phiC n ((2 * y + (a + b)) / (b - a))‖
      ≤ (K : ℝ) * ‖(2 * x + (a + b)) / (b - a)
          - (2 * y + (a + b)) / (b - a)‖ := hxy
    _ = (2 * (K : ℝ) / (b - a)) * ‖x - y‖ := by
        rw [div_sub_div_same]
        have hnum : 2 * x + (a + b) - (2 * y + (a + b)) = 2 * (x - y) := by ring
        rw [hnum, norm_div, norm_mul,
          Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          Real.norm_of_nonneg hba.le]
        ring




theorem measurable_oldBasis (a : ℝ) (n : ℕ) : Measurable (oldBasis a n) := by
  have hcont : Continuous (fun x : ℝ => Y7Matrix.phiC n (x / a)) :=
    (Complex.continuous_ofReal.comp (Y7Legendre.phi n).continuous).comp
      (continuous_id.div_const a)
  simpa [oldBasis, Y7Matrix.phiC] using hcont.measurable.indicator measurableSet_Ioo


theorem measurable_collarBasisRight (a b : ℝ) (n : ℕ) :
    Measurable (collarBasisRight a b n) := by
  have hcont : Continuous
      (fun x : ℝ => Y7Matrix.phiC n ((2 * x - (a + b)) / (b - a))) :=
    (Complex.continuous_ofReal.comp (Y7Legendre.phi n).continuous).comp
      (((continuous_const.mul continuous_id).sub continuous_const).div_const (b - a))
  simpa [collarBasisRight, Y7Matrix.phiC] using
    hcont.measurable.indicator measurableSet_Ioo


theorem measurable_collarBasisLeft (a b : ℝ) (n : ℕ) :
    Measurable (collarBasisLeft a b n) := by
  have hcont : Continuous
      (fun x : ℝ => Y7Matrix.phiC n ((2 * x + (a + b)) / (b - a))) :=
    (Complex.continuous_ofReal.comp (Y7Legendre.phi n).continuous).comp
      (((continuous_const.mul continuous_id).add continuous_const).div_const (b - a))
  simpa [collarBasisLeft, Y7Matrix.phiC] using
    hcont.measurable.indicator measurableSet_Ioo


theorem exists_bound_oldBasis {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖oldBasis a n x‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_bound_phiC n
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨by norm_num, by norm_num⟩)
  exact ⟨B, hB0, oldBasis_norm_le ha hB⟩


theorem exists_bound_collarBasisRight {a b : ℝ} (hab : a < b) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖collarBasisRight a b n x‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_bound_phiC n
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨by norm_num, by norm_num⟩)
  exact ⟨B, hB0, collarBasisRight_norm_le hab hB⟩


theorem exists_bound_collarBasisLeft {a b : ℝ} (hab : a < b) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖collarBasisLeft a b n x‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_bound_phiC n
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨by norm_num, by norm_num⟩)
  exact ⟨B, hB0, collarBasisLeft_norm_le hab hB⟩


theorem integrableOn_archBilinKernel_oldBasis {a : ℝ} (ha : 0 < a) (m n : ℕ) :
    IntegrableOn (archBilinKernel (oldBasis a m) (oldBasis a n))
      (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) := by
  obtain ⟨Kf, hKf0, hKf⟩ := oldBasis_lipschitz ha m
  obtain ⟨Kg, hKg0, hKg⟩ := oldBasis_lipschitz ha n
  exact integrableOn_archBilinKernel_of_lipschitz (by linarith) hKf0 hKg0 hKf hKg
    (measurable_oldBasis a m) (measurable_oldBasis a n)


theorem integrableOn_archBilinKernel_collarBasisRight {a b : ℝ} (hab : a < b)
    (m n : ℕ) :
    IntegrableOn (archBilinKernel (collarBasisRight a b m) (collarBasisRight a b n))
      (Set.Ioo a b ×ˢ Set.Ioo a b) := by
  obtain ⟨Kf, hKf0, hKf⟩ := collarBasisRight_lipschitz hab m
  obtain ⟨Kg, hKg0, hKg⟩ := collarBasisRight_lipschitz hab n
  exact integrableOn_archBilinKernel_of_lipschitz hab.le hKf0 hKg0 hKf hKg
    (measurable_collarBasisRight a b m) (measurable_collarBasisRight a b n)


theorem integrableOn_archBilinKernel_collarBasisLeft {a b : ℝ} (hab : a < b)
    (m n : ℕ) :
    IntegrableOn (archBilinKernel (collarBasisLeft a b m) (collarBasisLeft a b n))
      (Set.Ioo (-b) (-a) ×ˢ Set.Ioo (-b) (-a)) := by
  obtain ⟨Kf, hKf0, hKf⟩ := collarBasisLeft_lipschitz hab m
  obtain ⟨Kg, hKg0, hKg⟩ := collarBasisLeft_lipschitz hab n
  exact integrableOn_archBilinKernel_of_lipschitz (by linarith) hKf0 hKg0 hKf hKg
    (measurable_collarBasisLeft a b m) (measurable_collarBasisLeft a b n)


theorem integrableOn_archBilinKernel_oldBasis_collarBasisRight {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m n : ℕ) :
    IntegrableOn (archBilinKernel (oldBasis a m) (collarBasisRight a b n))
      (Set.Ioo (-a) a ×ˢ Set.Ioo a b) := by
  obtain ⟨Bf, hBf0, hBf⟩ := exists_bound_oldBasis ha m
  obtain ⟨Bg, hBg0, hBg⟩ := exists_bound_collarBasisRight hab n
  exact integrableOn_archBilinKernel_old_rightCollar ha hab hBf0 hBg0 hBf hBg
    (measurable_oldBasis a m) (measurable_collarBasisRight a b n)


theorem integrableOn_archBilinKernel_oldBasis_collarBasisLeft {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m n : ℕ) :
    IntegrableOn (archBilinKernel (oldBasis a m) (collarBasisLeft a b n))
      (Set.Ioo (-a) a ×ˢ Set.Ioo (-b) (-a)) := by
  obtain ⟨Bf, hBf0, hBf⟩ := exists_bound_oldBasis ha m
  obtain ⟨Bg, hBg0, hBg⟩ := exists_bound_collarBasisLeft hab n
  exact integrableOn_archBilinKernel_old_leftCollar ha hab hBf0 hBg0 hBf hBg
    (measurable_oldBasis a m) (measurable_collarBasisLeft a b n)


theorem integrableOn_archBilinKernel_collarBasisRight_oldBasis {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m n : ℕ) :
    IntegrableOn (archBilinKernel (collarBasisRight a b m) (oldBasis a n))
      (Set.Ioo a b ×ˢ Set.Ioo (-a) a) := by
  obtain ⟨Bf, hBf0, hBf⟩ := exists_bound_collarBasisRight hab m
  obtain ⟨Bg, hBg0, hBg⟩ := exists_bound_oldBasis ha n
  exact integrableOn_archBilinKernel_rightCollar_old ha hab hBf0 hBg0 hBf hBg
    (measurable_collarBasisRight a b m) (measurable_oldBasis a n)


theorem integrableOn_archBilinKernel_collarBasisLeft_oldBasis {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m n : ℕ) :
    IntegrableOn (archBilinKernel (collarBasisLeft a b m) (oldBasis a n))
      (Set.Ioo (-b) (-a) ×ˢ Set.Ioo (-a) a) := by
  obtain ⟨Bf, hBf0, hBf⟩ := exists_bound_collarBasisLeft hab m
  obtain ⟨Bg, hBg0, hBg⟩ := exists_bound_oldBasis ha n
  exact integrableOn_archBilinKernel_leftCollar_old ha hab hBf0 hBg0 hBf hBg
    (measurable_collarBasisLeft a b m) (measurable_oldBasis a n)




theorem aestronglyMeasurable_archBilinKernel {μ : Measure (ℝ × ℝ)} {f g : ℝ → ℂ}
    (hfm : Measurable f) (hgm : Measurable g) :
    AEStronglyMeasurable (archBilinKernel f g) μ := by
  have hre : Measurable (fun p : ℝ × ℝ =>
      ((f p.1 - f p.2) * star (g p.1 - g p.2)).re) :=
    Complex.continuous_re.measurable.comp
      (((hfm.comp measurable_fst).sub (hfm.comp measurable_snd)).mul
        (continuous_star.measurable.comp
          ((hgm.comp measurable_fst).sub (hgm.comp measurable_snd))))
  exact (hre.div ((continuous_fst.sub continuous_snd).norm.measurable)).aestronglyMeasurable



theorem integrableOn_archBilinKernel_of_support_zero {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : (volume.prod volume) (s ×ˢ s) < ⊤)
    {f g : ℝ → ℂ} (hfm : Measurable f) (hgm : Measurable g)
    (hfg : (∀ x ∈ s, f x = 0) ∨ (∀ x ∈ s, g x = 0)) :
    IntegrableOn (archBilinKernel f g) (s ×ˢ s) (volume.prod volume) := by
  refine IntegrableOn.of_bound hfin (aestronglyMeasurable_archBilinKernel hfm hgm) 0 ?_
  filter_upwards [ae_restrict_mem (hs.prod hs)] with p hp
  rcases hfg with hf | hg
  · have h1 : f p.1 = 0 := hf p.1 hp.1
    have h2 : f p.2 = 0 := hf p.2 hp.2
    simp [archBilinKernel, h1, h2]
  · have h1 : g p.1 = 0 := hg p.1 hp.1
    have h2 : g p.2 = 0 := hg p.2 hp.2
    simp [archBilinKernel, h1, h2]


theorem prod_measure_prod_Ioo_lt_top {b : ℝ} {s t : Set ℝ}
    (hs : s ⊆ Set.Ioo (-b) b) (ht : t ⊆ Set.Ioo (-b) b) :
    (volume.prod volume) (s ×ˢ t) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (Set.prod_mono hs ht)) ?_
  rw [Measure.prod_prod, Real.volume_Ioo]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top




theorem integrableOn_archBilinKernel_of_norm_le {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hfin : (volume.prod volume) s < ⊤) {f g : ℝ → ℂ} (hfm : Measurable f)
    (hgm : Measurable g) {Bf Bg c : ℝ} (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg) (hc : 0 < c)
    (hf : ∀ x, ‖f x‖ ≤ Bf) (hg : ∀ x, ‖g x‖ ≤ Bg)
    (hden : ∀ p ∈ s, c ≤ ‖p.1 - p.2‖) :
    IntegrableOn (archBilinKernel f g) s (volume.prod volume) := by
  refine IntegrableOn.of_bound hfin (aestronglyMeasurable_archBilinKernel hfm hgm)
    (4 * Bf * Bg / c) ?_
  filter_upwards [ae_restrict_mem hs] with p hp
  have hnum : ‖(f p.1 - f p.2) * star (g p.1 - g p.2)‖ ≤ 4 * Bf * Bg := by
    rw [norm_mul, norm_star]
    calc ‖f p.1 - f p.2‖ * ‖g p.1 - g p.2‖
        ≤ (2 * Bf) * (2 * Bg) := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
          · calc ‖f p.1 - f p.2‖ ≤ ‖f p.1‖ + ‖f p.2‖ := norm_sub_le _ _
              _ ≤ Bf + Bf := add_le_add (hf p.1) (hf p.2)
              _ = 2 * Bf := by ring
          · calc ‖g p.1 - g p.2‖ ≤ ‖g p.1‖ + ‖g p.2‖ := norm_sub_le _ _
              _ ≤ Bg + Bg := add_le_add (hg p.1) (hg p.2)
              _ = 2 * Bg := by ring
      _ = 4 * Bf * Bg := by ring
  have hre_le : |((f p.1 - f p.2) * star (g p.1 - g p.2)).re| ≤ 4 * Bf * Bg :=
    le_trans (Complex.abs_re_le_norm _) hnum
  unfold archBilinKernel
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg _)]
  calc |((f p.1 - f p.2) * star (g p.1 - g p.2)).re| / ‖p.1 - p.2‖
      ≤ (4 * Bf * Bg) / ‖p.1 - p.2‖ :=
        div_le_div_of_nonneg_right hre_le (norm_nonneg _)
    _ ≤ (4 * Bf * Bg) / c :=
        div_le_div_of_nonneg_left (by positivity) hc (hden p hp)




theorem integrableOn_archBilinKernel_collar_collar {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {f g : ℝ → ℂ} (hfm : Measurable f) (hgm : Measurable g)
    (hRR : IntegrableOn (archBilinKernel f g)
      (Set.Ioo a b ×ˢ Set.Ioo a b) (volume.prod volume))
    (hRL : IntegrableOn (archBilinKernel f g)
      (Set.Ioo a b ×ˢ Set.Ioo (-b) (-a)) (volume.prod volume))
    (hLR : IntegrableOn (archBilinKernel f g)
      (Set.Ioo (-b) (-a) ×ˢ Set.Ioo a b) (volume.prod volume))
    (hLL : IntegrableOn (archBilinKernel f g)
      (Set.Ioo (-b) (-a) ×ˢ Set.Ioo (-b) (-a)) (volume.prod volume)) :
    IntegrableOn (archBilinKernel f g) (collarSet a b ×ˢ collarSet a b)
      (volume.prod volume) := by
  set C' : Set ℝ := Set.Ioo a b ∪ Set.Ioo (-b) (-a) ∪ ({a, -a} : Set ℝ) with hC'
  have hnullR : IntegrableOn (archBilinKernel f g)
      (Set.Ioo a b ×ˢ ({a, -a} : Set ℝ)) (volume.prod volume) := by
    refine IntegrableOn.of_measure_zero ?_
    rw [Measure.prod_prod]
    have hfin : ({a, -a} : Set ℝ).Finite := (Set.finite_singleton (-a)).insert a
    simp [hfin.measure_zero volume]
  have hnullL : IntegrableOn (archBilinKernel f g)
      (Set.Ioo (-b) (-a) ×ˢ ({a, -a} : Set ℝ)) (volume.prod volume) := by
    refine IntegrableOn.of_measure_zero ?_
    rw [Measure.prod_prod]
    have hfin : ({a, -a} : Set ℝ).Finite := (Set.finite_singleton (-a)).insert a
    simp [hfin.measure_zero volume]
  have hnullC : IntegrableOn (archBilinKernel f g)
      (({a, -a} : Set ℝ) ×ˢ C') (volume.prod volume) := by
    refine IntegrableOn.of_measure_zero ?_
    rw [Measure.prod_prod]
    have hfin : ({a, -a} : Set ℝ).Finite := (Set.finite_singleton (-a)).insert a
    simp [hfin.measure_zero volume]
  have hRC : IntegrableOn (archBilinKernel f g)
      (Set.Ioo a b ×ˢ C') (volume.prod volume) := by
    have h : Set.Ioo a b ×ˢ C'
        = (Set.Ioo a b ×ˢ Set.Ioo a b ∪ Set.Ioo a b ×ˢ Set.Ioo (-b) (-a))
          ∪ Set.Ioo a b ×ˢ ({a, -a} : Set ℝ) := by
      rw [hC', Set.prod_union, Set.prod_union]
    rw [h]
    exact (hRR.union hRL).union hnullR
  have hLC : IntegrableOn (archBilinKernel f g)
      (Set.Ioo (-b) (-a) ×ˢ C') (volume.prod volume) := by
    have h : Set.Ioo (-b) (-a) ×ˢ C'
        = (Set.Ioo (-b) (-a) ×ˢ Set.Ioo a b ∪ Set.Ioo (-b) (-a) ×ˢ Set.Ioo (-b) (-a))
          ∪ Set.Ioo (-b) (-a) ×ˢ ({a, -a} : Set ℝ) := by
      rw [hC', Set.prod_union, Set.prod_union]
    rw [h]
    exact (hLR.union hLL).union hnullL
  have hCC' : IntegrableOn (archBilinKernel f g) (C' ×ˢ C') (volume.prod volume) := by
    have h : C' ×ˢ C'
        = ((Set.Ioo a b ×ˢ C') ∪ (Set.Ioo (-b) (-a) ×ˢ C'))
          ∪ (({a, -a} : Set ℝ) ×ˢ C') := by
      rw [hC', Set.union_prod, Set.union_prod]
    rw [h]
    exact (hRC.union hLC).union hnullC
  rw [show collarSet a b = C' from by rw [hC']; exact collarSet_eq_union_insert ha hab]
  exact hCC'



theorem integrableOn_archBilinKernel_full_square {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℂ}
    (hOO : IntegrableOn (archBilinKernel f g)
      (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) (volume.prod volume))
    (hOC : IntegrableOn (archBilinKernel f g)
      (Set.Ioo (-a) a ×ˢ collarSet a b) (volume.prod volume))
    (hCO : IntegrableOn (archBilinKernel f g)
      (collarSet a b ×ˢ Set.Ioo (-a) a) (volume.prod volume))
    (hCC : IntegrableOn (archBilinKernel f g)
      (collarSet a b ×ˢ collarSet a b) (volume.prod volume)) :
    IntegrableOn (archBilinKernel f g) (Set.Ioo (-b) b ×ˢ Set.Ioo (-b) b)
      (volume.prod volume) := by
  have hsubO : Set.Ioo (-a) a ⊆ Set.Ioo (-b) b := fun x hx =>
    ⟨lt_of_le_of_lt (neg_le_neg hab) hx.1, lt_of_lt_of_le hx.2 hab⟩
  have hB : Set.Ioo (-b) b = Set.Ioo (-a) a ∪ collarSet a b := by
    unfold collarSet
    exact (Set.union_sdiff_cancel hsubO).symm
  have hsquare : Set.Ioo (-b) b ×ˢ Set.Ioo (-b) b
      = ((Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) ∪ (Set.Ioo (-a) a ×ˢ collarSet a b))
        ∪ ((collarSet a b ×ˢ Set.Ioo (-a) a) ∪ (collarSet a b ×ˢ collarSet a b)) := by
    rw [hB]
    simp only [Set.union_prod, Set.prod_union]
    ac_rfl
  rw [hsquare]
  exact (hOO.union hOC).union (hCO.union hCC)



theorem oldBasis_eq_zero_of_notMem {a : ℝ} (n : ℕ) {x : ℝ}
    (hx : x ∉ Set.Ioo (-a) a) : oldBasis a n x = 0 := by
  simp [oldBasis, hx]

theorem collarBasisRight_eq_zero_of_notMem {a b : ℝ} (n : ℕ) {x : ℝ}
    (hx : x ∉ Set.Ioo a b) : collarBasisRight a b n x = 0 := by
  simp [collarBasisRight, hx]

theorem collarBasisLeft_eq_zero_of_notMem {a b : ℝ} (n : ℕ) {x : ℝ}
    (hx : x ∉ Set.Ioo (-b) (-a)) : collarBasisLeft a b n x = 0 := by
  simp [collarBasisLeft, hx]

theorem collarSet_subset_Ioo {a b : ℝ} : collarSet a b ⊆ Set.Ioo (-b) b := by
  intro x hx
  have hx' : x ∈ Set.Ioo (-b) b ∧ x ∉ Set.Ioo (-a) a := by simpa [collarSet] using hx
  exact hx'.1

theorem oldSet_subset_Ioo {a b : ℝ} (hab : a ≤ b) :
    Set.Ioo (-a) a ⊆ Set.Ioo (-b) b := fun x hx =>
  ⟨lt_of_le_of_lt (neg_le_neg hab) hx.1, lt_of_lt_of_le hx.2 hab⟩

theorem collarRight_subset_Ioo {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Set.Ioo a b ⊆ Set.Ioo (-b) b := by
  intro x hx
  exact ⟨by linarith [hx.1, ha, hab], hx.2⟩

theorem collarLeft_subset_Ioo {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Set.Ioo (-b) (-a) ⊆ Set.Ioo (-b) b := by
  intro x hx
  exact ⟨hx.1, by linarith [hx.2, ha, hab]⟩



theorem integrableOn_archBilinKernel_full_oldBasis {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (m n : ℕ) :
    IntegrableOn (archBilinKernel (oldBasis a m) (oldBasis a n))
      (Set.Ioo (-b) b ×ˢ Set.Ioo (-b) b) := by
  obtain ⟨Bf, hBf0, hBf⟩ := exists_bound_oldBasis ha m
  obtain ⟨Bg, hBg0, hBg⟩ := exists_bound_oldBasis ha n
  refine integrableOn_archBilinKernel_full_square hab.le ?_ ?_ ?_ ?_
  · exact integrableOn_archBilinKernel_oldBasis ha m n
  · exact integrableOn_archBilinKernel_old_collar ha hab hBf0 hBg0 hBf hBg
      (measurable_oldBasis a m) (measurable_oldBasis a n)
  · exact integrableOn_archBilinKernel_collar_old ha hab hBf0 hBg0 hBf hBg
      (measurable_oldBasis a m) (measurable_oldBasis a n)
  · refine integrableOn_archBilinKernel_of_support_zero
      (s := collarSet a b) (measurableSet_Ioo.diff measurableSet_Ioo)
      (prod_measure_prod_Ioo_lt_top collarSet_subset_Ioo collarSet_subset_Ioo)
      (measurable_oldBasis a m) (measurable_oldBasis a n) (Or.inl ?_)
    intro x hx
    have hx' : x ∈ Set.Ioo (-b) b ∧ x ∉ Set.Ioo (-a) a := by
      simpa [collarSet] using hx
    exact oldBasis_eq_zero_of_notMem m hx'.2

theorem integrableOn_archBilinKernel_full_oldBasis_collarBasisRight {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m n : ℕ) :
    IntegrableOn (archBilinKernel (oldBasis a m) (collarBasisRight a b n))
      (Set.Ioo (-b) b ×ˢ Set.Ioo (-b) b) := by
  obtain ⟨Bf, hBf0, hBf⟩ := exists_bound_oldBasis ha m
  obtain ⟨Bg, hBg0, hBg⟩ := exists_bound_collarBasisRight hab n
  refine integrableOn_archBilinKernel_full_square hab.le ?_ ?_ ?_ ?_
  · refine integrableOn_archBilinKernel_of_support_zero (s := Set.Ioo (-a) a)
      measurableSet_Ioo
      (prod_measure_prod_Ioo_lt_top (oldSet_subset_Ioo hab.le) (oldSet_subset_Ioo hab.le))
      (measurable_oldBasis a m) (measurable_collarBasisRight a b n) (Or.inr ?_)
    intro x hx
    exact collarBasisRight_eq_zero_of_notMem n (by
      rintro ⟨h1, _⟩
      linarith [hx.2, ha, h1])
  · exact integrableOn_archBilinKernel_old_collar ha hab hBf0 hBg0 hBf hBg
      (measurable_oldBasis a m) (measurable_collarBasisRight a b n)
  · exact integrableOn_archBilinKernel_collar_old ha hab hBf0 hBg0 hBf hBg
      (measurable_oldBasis a m) (measurable_collarBasisRight a b n)
  · refine integrableOn_archBilinKernel_of_support_zero
      (s := collarSet a b) (measurableSet_Ioo.diff measurableSet_Ioo)
      (prod_measure_prod_Ioo_lt_top collarSet_subset_Ioo collarSet_subset_Ioo)
      (measurable_oldBasis a m) (measurable_collarBasisRight a b n) (Or.inl ?_)
    intro x hx
    have hx' : x ∈ Set.Ioo (-b) b ∧ x ∉ Set.Ioo (-a) a := by
      simpa [collarSet] using hx
    exact oldBasis_eq_zero_of_notMem m hx'.2

theorem integrableOn_archBilinKernel_full_oldBasis_collarBasisLeft {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m n : ℕ) :
    IntegrableOn (archBilinKernel (oldBasis a m) (collarBasisLeft a b n))
      (Set.Ioo (-b) b ×ˢ Set.Ioo (-b) b) := by
  obtain ⟨Bf, hBf0, hBf⟩ := exists_bound_oldBasis ha m
  obtain ⟨Bg, hBg0, hBg⟩ := exists_bound_collarBasisLeft hab n
  refine integrableOn_archBilinKernel_full_square hab.le ?_ ?_ ?_ ?_
  · refine integrableOn_archBilinKernel_of_support_zero (s := Set.Ioo (-a) a)
      measurableSet_Ioo
      (prod_measure_prod_Ioo_lt_top (oldSet_subset_Ioo hab.le) (oldSet_subset_Ioo hab.le))
      (measurable_oldBasis a m) (measurable_collarBasisLeft a b n) (Or.inr ?_)
    intro x hx
    exact collarBasisLeft_eq_zero_of_notMem n (by
      rintro ⟨_, h2⟩
      linarith [hx.1, ha, h2])
  · exact integrableOn_archBilinKernel_old_collar ha hab hBf0 hBg0 hBf hBg
      (measurable_oldBasis a m) (measurable_collarBasisLeft a b n)
  · exact integrableOn_archBilinKernel_collar_old ha hab hBf0 hBg0 hBf hBg
      (measurable_oldBasis a m) (measurable_collarBasisLeft a b n)
  · refine integrableOn_archBilinKernel_of_support_zero
      (s := collarSet a b) (measurableSet_Ioo.diff measurableSet_Ioo)
      (prod_measure_prod_Ioo_lt_top collarSet_subset_Ioo collarSet_subset_Ioo)
      (measurable_oldBasis a m) (measurable_collarBasisLeft a b n) (Or.inl ?_)
    intro x hx
    have hx' : x ∈ Set.Ioo (-b) b ∧ x ∉ Set.Ioo (-a) a := by
      simpa [collarSet] using hx
    exact oldBasis_eq_zero_of_notMem m hx'.2

theorem integrableOn_archBilinKernel_full_collarBasisRight {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (m n : ℕ) :
    IntegrableOn (archBilinKernel (collarBasisRight a b m) (collarBasisRight a b n))
      (Set.Ioo (-b) b ×ˢ Set.Ioo (-b) b) := by
  obtain ⟨Bf, hBf0, hBf⟩ := exists_bound_collarBasisRight hab m
  obtain ⟨Bg, hBg0, hBg⟩ := exists_bound_collarBasisRight hab n
  have hfinR : (volume.prod volume) (Set.Ioo a b ×ˢ Set.Ioo a b) < ⊤ :=
    prod_measure_prod_Ioo_lt_top (collarRight_subset_Ioo ha.le hab)
      (collarRight_subset_Ioo ha.le hab)
  have hfinL : (volume.prod volume) (Set.Ioo (-b) (-a) ×ˢ Set.Ioo (-b) (-a)) < ⊤ :=
    prod_measure_prod_Ioo_lt_top (collarLeft_subset_Ioo ha.le hab)
      (collarLeft_subset_Ioo ha.le hab)
  have hfinRL : (volume.prod volume) (Set.Ioo a b ×ˢ Set.Ioo (-b) (-a)) < ⊤ :=
    prod_measure_prod_Ioo_lt_top (collarRight_subset_Ioo ha.le hab)
      (collarLeft_subset_Ioo ha.le hab)
  have hfinLR : (volume.prod volume) (Set.Ioo (-b) (-a) ×ˢ Set.Ioo a b) < ⊤ :=
    prod_measure_prod_Ioo_lt_top (collarLeft_subset_Ioo ha.le hab)
      (collarRight_subset_Ioo ha.le hab)
  refine integrableOn_archBilinKernel_full_square hab.le ?_ ?_ ?_ ?_
  · refine integrableOn_archBilinKernel_of_support_zero (s := Set.Ioo (-a) a)
      measurableSet_Ioo
      (prod_measure_prod_Ioo_lt_top (oldSet_subset_Ioo hab.le) (oldSet_subset_Ioo hab.le))
      (measurable_collarBasisRight a b m) (measurable_collarBasisRight a b n) (Or.inl ?_)
    intro x hx
    exact collarBasisRight_eq_zero_of_notMem m (by
      rintro ⟨h1, _⟩
      linarith [hx.2, ha, h1])
  · exact integrableOn_archBilinKernel_old_collar ha hab hBf0 hBg0 hBf hBg
      (measurable_collarBasisRight a b m) (measurable_collarBasisRight a b n)
  · exact integrableOn_archBilinKernel_collar_old ha hab hBf0 hBg0 hBf hBg
      (measurable_collarBasisRight a b m) (measurable_collarBasisRight a b n)
  · refine integrableOn_archBilinKernel_collar_collar ha hab
      (measurable_collarBasisRight a b m) (measurable_collarBasisRight a b n) ?_ ?_ ?_ ?_
    · exact integrableOn_archBilinKernel_collarBasisRight hab m n
    · refine integrableOn_archBilinKernel_of_norm_le
        (measurableSet_Ioo.prod measurableSet_Ioo) hfinRL
        (measurable_collarBasisRight a b m) (measurable_collarBasisRight a b n)
        hBf0 hBg0 (c := 2 * a) (by linarith) hBf hBg ?_
      intro p hp
      rw [Real.norm_eq_abs, abs_of_pos (by linarith [hp.1.1, hp.2.2])]
      linarith [hp.1.1, hp.2.2]
    · refine integrableOn_archBilinKernel_of_norm_le
        (measurableSet_Ioo.prod measurableSet_Ioo) hfinLR
        (measurable_collarBasisRight a b m) (measurable_collarBasisRight a b n)
        hBf0 hBg0 (c := 2 * a) (by linarith) hBf hBg ?_
      intro p hp
      rw [Real.norm_eq_abs, abs_of_neg (by linarith [hp.1.2, hp.2.1])]
      linarith [hp.1.2, hp.2.1]
    · refine integrableOn_archBilinKernel_of_support_zero (s := Set.Ioo (-b) (-a))
        measurableSet_Ioo hfinL
        (measurable_collarBasisRight a b m) (measurable_collarBasisRight a b n)
        (Or.inl ?_)
      intro x hx
      exact collarBasisRight_eq_zero_of_notMem m (by
        rintro ⟨h1, _⟩
        linarith [hx.2, ha, h1])

theorem integrableOn_archBilinKernel_full_collarBasisLeft {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (m n : ℕ) :
    IntegrableOn (archBilinKernel (collarBasisLeft a b m) (collarBasisLeft a b n))
      (Set.Ioo (-b) b ×ˢ Set.Ioo (-b) b) := by
  obtain ⟨Bf, hBf0, hBf⟩ := exists_bound_collarBasisLeft hab m
  obtain ⟨Bg, hBg0, hBg⟩ := exists_bound_collarBasisLeft hab n
  have hfinR : (volume.prod volume) (Set.Ioo a b ×ˢ Set.Ioo a b) < ⊤ :=
    prod_measure_prod_Ioo_lt_top (collarRight_subset_Ioo ha.le hab)
      (collarRight_subset_Ioo ha.le hab)
  have hfinL : (volume.prod volume) (Set.Ioo (-b) (-a) ×ˢ Set.Ioo (-b) (-a)) < ⊤ :=
    prod_measure_prod_Ioo_lt_top (collarLeft_subset_Ioo ha.le hab)
      (collarLeft_subset_Ioo ha.le hab)
  have hfinRL : (volume.prod volume) (Set.Ioo a b ×ˢ Set.Ioo (-b) (-a)) < ⊤ :=
    prod_measure_prod_Ioo_lt_top (collarRight_subset_Ioo ha.le hab)
      (collarLeft_subset_Ioo ha.le hab)
  have hfinLR : (volume.prod volume) (Set.Ioo (-b) (-a) ×ˢ Set.Ioo a b) < ⊤ :=
    prod_measure_prod_Ioo_lt_top (collarLeft_subset_Ioo ha.le hab)
      (collarRight_subset_Ioo ha.le hab)
  refine integrableOn_archBilinKernel_full_square hab.le ?_ ?_ ?_ ?_
  · refine integrableOn_archBilinKernel_of_support_zero (s := Set.Ioo (-a) a)
      measurableSet_Ioo
      (prod_measure_prod_Ioo_lt_top (oldSet_subset_Ioo hab.le) (oldSet_subset_Ioo hab.le))
      (measurable_collarBasisLeft a b m) (measurable_collarBasisLeft a b n) (Or.inl ?_)
    intro x hx
    exact collarBasisLeft_eq_zero_of_notMem m (by
      rintro ⟨_, h2⟩
      linarith [hx.1, ha, h2])
  · exact integrableOn_archBilinKernel_old_collar ha hab hBf0 hBg0 hBf hBg
      (measurable_collarBasisLeft a b m) (measurable_collarBasisLeft a b n)
  · exact integrableOn_archBilinKernel_collar_old ha hab hBf0 hBg0 hBf hBg
      (measurable_collarBasisLeft a b m) (measurable_collarBasisLeft a b n)
  · refine integrableOn_archBilinKernel_collar_collar ha hab
      (measurable_collarBasisLeft a b m) (measurable_collarBasisLeft a b n) ?_ ?_ ?_ ?_
    · refine integrableOn_archBilinKernel_of_support_zero (s := Set.Ioo a b)
        measurableSet_Ioo hfinR
        (measurable_collarBasisLeft a b m) (measurable_collarBasisLeft a b n) (Or.inl ?_)
      intro x hx
      exact collarBasisLeft_eq_zero_of_notMem m (by
        rintro ⟨_, h2⟩
        linarith [hx.1, ha, h2])
    · refine integrableOn_archBilinKernel_of_norm_le
        (measurableSet_Ioo.prod measurableSet_Ioo) hfinRL
        (measurable_collarBasisLeft a b m) (measurable_collarBasisLeft a b n)
        hBf0 hBg0 (c := 2 * a) (by linarith) hBf hBg ?_
      intro p hp
      rw [Real.norm_eq_abs, abs_of_pos (by linarith [hp.1.1, hp.2.2])]
      linarith [hp.1.1, hp.2.2]
    · refine integrableOn_archBilinKernel_of_norm_le
        (measurableSet_Ioo.prod measurableSet_Ioo) hfinLR
        (measurable_collarBasisLeft a b m) (measurable_collarBasisLeft a b n)
        hBf0 hBg0 (c := 2 * a) (by linarith) hBf hBg ?_
      intro p hp
      rw [Real.norm_eq_abs, abs_of_neg (by linarith [hp.1.2, hp.2.1])]
      linarith [hp.1.2, hp.2.1]
    · exact integrableOn_archBilinKernel_collarBasisLeft hab m n

theorem integrableOn_archBilinKernel_full_collarBasisRight_collarBasisLeft {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m n : ℕ) :
    IntegrableOn (archBilinKernel (collarBasisRight a b m) (collarBasisLeft a b n))
      (Set.Ioo (-b) b ×ˢ Set.Ioo (-b) b) := by
  obtain ⟨Bf, hBf0, hBf⟩ := exists_bound_collarBasisRight hab m
  obtain ⟨Bg, hBg0, hBg⟩ := exists_bound_collarBasisLeft hab n
  have hfinR : (volume.prod volume) (Set.Ioo a b ×ˢ Set.Ioo a b) < ⊤ :=
    prod_measure_prod_Ioo_lt_top (collarRight_subset_Ioo ha.le hab)
      (collarRight_subset_Ioo ha.le hab)
  have hfinL : (volume.prod volume) (Set.Ioo (-b) (-a) ×ˢ Set.Ioo (-b) (-a)) < ⊤ :=
    prod_measure_prod_Ioo_lt_top (collarLeft_subset_Ioo ha.le hab)
      (collarLeft_subset_Ioo ha.le hab)
  have hfinRL : (volume.prod volume) (Set.Ioo a b ×ˢ Set.Ioo (-b) (-a)) < ⊤ :=
    prod_measure_prod_Ioo_lt_top (collarRight_subset_Ioo ha.le hab)
      (collarLeft_subset_Ioo ha.le hab)
  have hfinLR : (volume.prod volume) (Set.Ioo (-b) (-a) ×ˢ Set.Ioo a b) < ⊤ :=
    prod_measure_prod_Ioo_lt_top (collarLeft_subset_Ioo ha.le hab)
      (collarRight_subset_Ioo ha.le hab)
  refine integrableOn_archBilinKernel_full_square hab.le ?_ ?_ ?_ ?_
  · refine integrableOn_archBilinKernel_of_support_zero (s := Set.Ioo (-a) a)
      measurableSet_Ioo
      (prod_measure_prod_Ioo_lt_top (oldSet_subset_Ioo hab.le) (oldSet_subset_Ioo hab.le))
      (measurable_collarBasisRight a b m) (measurable_collarBasisLeft a b n) (Or.inl ?_)
    intro x hx
    exact collarBasisRight_eq_zero_of_notMem m (by
      rintro ⟨h1, _⟩
      linarith [hx.2, ha, h1])
  · exact integrableOn_archBilinKernel_old_collar ha hab hBf0 hBg0 hBf hBg
      (measurable_collarBasisRight a b m) (measurable_collarBasisLeft a b n)
  · exact integrableOn_archBilinKernel_collar_old ha hab hBf0 hBg0 hBf hBg
      (measurable_collarBasisRight a b m) (measurable_collarBasisLeft a b n)
  · refine integrableOn_archBilinKernel_collar_collar ha hab
      (measurable_collarBasisRight a b m) (measurable_collarBasisLeft a b n) ?_ ?_ ?_ ?_
    · refine integrableOn_archBilinKernel_of_support_zero (s := Set.Ioo a b)
        measurableSet_Ioo hfinR
        (measurable_collarBasisRight a b m) (measurable_collarBasisLeft a b n) (Or.inr ?_)
      intro x hx
      exact collarBasisLeft_eq_zero_of_notMem n (by
        rintro ⟨_, h2⟩
        linarith [hx.1, ha, h2])
    · refine integrableOn_archBilinKernel_of_norm_le
        (measurableSet_Ioo.prod measurableSet_Ioo) hfinRL
        (measurable_collarBasisRight a b m) (measurable_collarBasisLeft a b n)
        hBf0 hBg0 (c := 2 * a) (by linarith) hBf hBg ?_
      intro p hp
      rw [Real.norm_eq_abs, abs_of_pos (by linarith [hp.1.1, hp.2.2])]
      linarith [hp.1.1, hp.2.2]
    · refine integrableOn_archBilinKernel_of_norm_le
        (measurableSet_Ioo.prod measurableSet_Ioo) hfinLR
        (measurable_collarBasisRight a b m) (measurable_collarBasisLeft a b n)
        hBf0 hBg0 (c := 2 * a) (by linarith) hBf hBg ?_
      intro p hp
      rw [Real.norm_eq_abs, abs_of_neg (by linarith [hp.1.2, hp.2.1])]
      linarith [hp.1.2, hp.2.1]
    · refine integrableOn_archBilinKernel_of_support_zero (s := Set.Ioo (-b) (-a))
        measurableSet_Ioo hfinL
        (measurable_collarBasisRight a b m) (measurable_collarBasisLeft a b n) (Or.inl ?_)
      intro x hx
      exact collarBasisRight_eq_zero_of_notMem m (by
        rintro ⟨h1, _⟩
        linarith [hx.2, ha, h1])




noncomputable def combinedCollarBasis (a b : ℝ) : (ℕ ⊕ ℕ) → ℝ → ℂ :=
  Sum.elim (collarBasisRight a b) (collarBasisLeft a b)


noncomputable def combinedBasis (a b : ℝ) : (ℕ ⊕ (ℕ ⊕ ℕ)) → ℝ → ℂ :=
  Sum.elim (oldBasis a) (combinedCollarBasis a b)


noncomputable def truncBasis (a b : ℝ) (N : ℕ) :
    (Fin N ⊕ (Fin N ⊕ Fin N)) → ℝ → ℂ :=
  Sum.elim (fun i : Fin N => oldBasis a i)
    (Sum.elim (fun i : Fin N => collarBasisRight a b i)
      (fun i : Fin N => collarBasisLeft a b i))


noncomputable def truncCollarBasis (a b : ℝ) (N : ℕ) : (Fin N ⊕ Fin N) → ℝ → ℂ :=
  Sum.elim (fun i : Fin N => collarBasisRight a b i)
    (fun i : Fin N => collarBasisLeft a b i)

@[simp] theorem combinedBasis_inl (a b : ℝ) (n : ℕ) :
    combinedBasis a b (Sum.inl n) = oldBasis a n := rfl

@[simp] theorem combinedBasis_inr_inl (a b : ℝ) (n : ℕ) :
    combinedBasis a b (Sum.inr (Sum.inl n)) = collarBasisRight a b n := rfl

@[simp] theorem combinedBasis_inr_inr (a b : ℝ) (n : ℕ) :
    combinedBasis a b (Sum.inr (Sum.inr n)) = collarBasisLeft a b n := rfl


theorem gramMatrix_sum_eq_fromBlocks {ιO ιC : Type*} (b : ℝ)
    (φO : ιO → ℝ → ℂ) (φC : ιC → ℝ → ℂ) :
    gramMatrix b (Sum.elim φO φC)
      = Matrix.fromBlocks (oldOldBlock b φO) (oldCollarBlock b φO φC)
          (oldCollarBlock b φC φO) (collarCollarBlock b φC) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [gramMatrix, oldOldBlock, oldCollarBlock, collarCollarBlock, localizedBilin_comm]



theorem gramMatrix_sum_eq_oldNewBlock {ιO ιC : Type*} [Fintype ιO] [Fintype ιC]
    (b : ℝ) (φO : ιO → ℝ → ℂ) (φC : ιC → ℝ → ℂ) :
    gramMatrix b (Sum.elim φO φC)
      = oldNewBlock (oldOldBlock b φO) (oldCollarBlock b φO φC)
          (collarCollarBlock b φC) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [gramMatrix, oldNewBlock, oldOldBlock, oldCollarBlock, collarCollarBlock,
      Matrix.conjTranspose_apply, localizedBilin_comm, star_trivial]



theorem gramMatrix_combinedBasis_eq_fromBlocks (a b : ℝ) :
    gramMatrix b (combinedBasis a b)
      = Matrix.fromBlocks (oldOldBlock b (oldBasis a))
          (oldCollarBlock b (oldBasis a) (combinedCollarBasis a b))
          (oldCollarBlock b (combinedCollarBasis a b) (oldBasis a))
          (collarCollarBlock b (combinedCollarBasis a b)) :=
  gramMatrix_sum_eq_fromBlocks b (oldBasis a) (combinedCollarBasis a b)


theorem gramMatrix_truncBasis_eq_oldNewBlock (a b : ℝ) (N : ℕ) :
    gramMatrix b (truncBasis a b N)
      = oldNewBlock (oldOldBlock b (fun i : Fin N => oldBasis a i))
          (oldCollarBlock b (fun i : Fin N => oldBasis a i) (truncCollarBasis a b N))
          (collarCollarBlock b (truncCollarBasis a b N)) :=
  gramMatrix_sum_eq_oldNewBlock b (fun i : Fin N => oldBasis a i) (truncCollarBasis a b N)

theorem gramMatrix_combinedBasis_isSymm (a b : ℝ) :
    (gramMatrix b (combinedBasis a b)).IsSymm :=
  gramMatrix_isSymm b (combinedBasis a b)

theorem oldNewBlock_trunc_isSymm (a b : ℝ) (N : ℕ) :
    (oldNewBlock (oldOldBlock b (fun i : Fin N => oldBasis a i))
      (oldCollarBlock b (fun i : Fin N => oldBasis a i) (truncCollarBasis a b N))
      (collarCollarBlock b (truncCollarBasis a b N))).IsSymm := by
  rw [← gramMatrix_truncBasis_eq_oldNewBlock]
  exact gramMatrix_isSymm b (truncBasis a b N)



@[instance_reducible]
noncomputable def posDef_invertible_of_posDef {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℝ) (hD : D.PosDef) : Invertible D :=
  ((Matrix.isUnit_iff_isUnit_det D).mpr
    (isUnit_iff_ne_zero.mpr hD.det_pos.ne')).nonempty_invertible.some




theorem truncBasis_posDef_of_schur (a b : ℝ) (N : ℕ)
    [Invertible (collarCollarBlock b (truncCollarBasis a b N))]
    (hA : (oldOldBlock b (fun i : Fin N => oldBasis a i)).PosDef)
    (hD : (collarCollarBlock b (truncCollarBasis a b N)).PosDef)
    (hT : (harmonicForm (oldOldBlock b (fun i : Fin N => oldBasis a i))
        (oldCollarBlock b (fun i : Fin N => oldBasis a i) (truncCollarBasis a b N))
        (collarCollarBlock b (truncCollarBasis a b N))).PosDef) :
    (gramMatrix b (truncBasis a b N)).PosDef := by
  rw [gramMatrix_truncBasis_eq_oldNewBlock]
  exact oldNew_schur _ _ _ hA hD hT



theorem oldBasis_support_subset (a : ℝ) (n : ℕ) :
    Function.support (oldBasis a n) ⊆ Set.Ioo (-a) a := by
  intro x hx
  by_contra hx'
  exact hx (oldBasis_eq_zero_of_notMem n hx')

theorem collarBasisRight_support_subset (a b : ℝ) (n : ℕ) :
    Function.support (collarBasisRight a b n) ⊆ Set.Ioo a b := by
  intro x hx
  by_contra hx'
  exact hx (collarBasisRight_eq_zero_of_notMem n hx')

theorem collarBasisLeft_support_subset (a b : ℝ) (n : ℕ) :
    Function.support (collarBasisLeft a b n) ⊆ Set.Ioo (-b) (-a) := by
  intro x hx
  by_contra hx'
  exact hx (collarBasisLeft_eq_zero_of_notMem n hx')

theorem disjoint_support_oldBasis_collarBasisRight {a b : ℝ} (m n : ℕ) :
    Disjoint (Function.support (oldBasis a m))
      (Function.support (collarBasisRight a b n)) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have h1 := oldBasis_support_subset a m hx1
  have h2 := collarBasisRight_support_subset a b n hx2
  linarith [h1.2, h2.1]

theorem disjoint_support_oldBasis_collarBasisLeft {a b : ℝ} (m n : ℕ) :
    Disjoint (Function.support (oldBasis a m))
      (Function.support (collarBasisLeft a b n)) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have h1 := oldBasis_support_subset a m hx1
  have h2 := collarBasisLeft_support_subset a b n hx2
  linarith [h1.1, h2.2]


theorem massBilin_oldBasis_collarBasisRight_eq_zero {a b : ℝ} (m n : ℕ) :
    massBilin b (oldBasis a m) (collarBasisRight a b n) = 0 :=
  massBilin_eq_zero_of_disjoint_support (disjoint_support_oldBasis_collarBasisRight m n)


theorem massBilin_oldBasis_collarBasisLeft_eq_zero {a b : ℝ} (m n : ℕ) :
    massBilin b (oldBasis a m) (collarBasisLeft a b n) = 0 :=
  massBilin_eq_zero_of_disjoint_support (disjoint_support_oldBasis_collarBasisLeft m n)


theorem potentialBilin_oldBasis_collarBasisRight_eq_zero {a b : ℝ} (m n : ℕ) :
    potentialBilin b (oldBasis a m) (collarBasisRight a b n) = 0 :=
  potentialBilin_eq_zero_of_disjoint_support (disjoint_support_oldBasis_collarBasisRight m n)


theorem potentialBilin_oldBasis_collarBasisLeft_eq_zero {a b : ℝ} (m n : ℕ) :
    potentialBilin b (oldBasis a m) (collarBasisLeft a b n) = 0 :=
  potentialBilin_eq_zero_of_disjoint_support (disjoint_support_oldBasis_collarBasisLeft m n)



theorem localizedBilin_oldBasis_collarBasisRight_eq {a b : ℝ} (m n : ℕ) :
    localizedBilin b (oldBasis a m) (collarBasisRight a b n)
      = archBilin b (oldBasis a m) (collarBasisRight a b n)
        - gammaBilin b (oldBasis a m) (collarBasisRight a b n)
        - polarBilin b (oldBasis a m) (collarBasisRight a b n)
        - shiftBilin b (oldBasis a m) (collarBasisRight a b n) := by
  unfold localizedBilin
  rw [massBilin_oldBasis_collarBasisRight_eq_zero,
    potentialBilin_oldBasis_collarBasisRight_eq_zero]
  ring



theorem localizedBilin_oldBasis_collarBasisLeft_eq {a b : ℝ} (m n : ℕ) :
    localizedBilin b (oldBasis a m) (collarBasisLeft a b n)
      = archBilin b (oldBasis a m) (collarBasisLeft a b n)
        - gammaBilin b (oldBasis a m) (collarBasisLeft a b n)
        - polarBilin b (oldBasis a m) (collarBasisLeft a b n)
        - shiftBilin b (oldBasis a m) (collarBasisLeft a b n) := by
  unfold localizedBilin
  rw [massBilin_oldBasis_collarBasisLeft_eq_zero,
    potentialBilin_oldBasis_collarBasisLeft_eq_zero]
  ring



theorem endpoint_pos {k : ℕ} (hk : 1 < k) : 0 < endpoint k := by
  rw [endpoint]
  exact div_pos (Real.log_pos (by exact_mod_cast hk)) (by norm_num)

theorem endpoint_succ_gt {k : ℕ} (hk : 1 ≤ k) : endpoint k < endpoint (k + 1) :=
  endpoint_strict_mono hk (Nat.lt_succ_self k)



theorem gramMatrix_truncBasis_endpoint_eq_oldNewBlock (k N : ℕ) :
    gramMatrix (endpoint (k + 1)) (truncBasis (endpoint k) (endpoint (k + 1)) N)
      = oldNewBlock (oldOldBlock (endpoint (k + 1)) (fun i : Fin N => oldBasis (endpoint k) i))
          (oldCollarBlock (endpoint (k + 1)) (fun i : Fin N => oldBasis (endpoint k) i)
            (truncCollarBasis (endpoint k) (endpoint (k + 1)) N))
          (collarCollarBlock (endpoint (k + 1))
            (truncCollarBasis (endpoint k) (endpoint (k + 1)) N)) :=
  gramMatrix_truncBasis_eq_oldNewBlock _ _ _






theorem inner_toEuclideanLin {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℝ) (x y : EuclideanSpace ℝ n) :
    ⟪x, T.toEuclideanLin y⟫_ℝ = WithLp.ofLp x ⬝ᵥ (T *ᵥ WithLp.ofLp y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  simp only [Pi.star_apply, star_trivial]
  rw [dotProduct_comm]





theorem posDef_of_components {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℝ) (hT : T.PosSemidef)
    (e : EuclideanSpace ℝ n) (he : e ≠ 0) (g : ℝ) (hg : 0 < g)
    (hground : g * ‖e‖ ^ 2 ≤ ⟪e, T.toEuclideanLin e⟫_ℝ)
    (hplace : ∀ f : EuclideanSpace ℝ n,
      0 ≤ groundCoord e f * ⟪e, T.toEuclideanLin (transversePart e f)⟫_ℝ)
    (hres : ∀ w : EuclideanSpace ℝ n, ⟪e, w⟫_ℝ = 0 → w ≠ 0 →
      0 < ⟪w, T.toEuclideanLin w⟫_ℝ) :
    T.PosDef := by
  have hpos := master_posDef_of_components T.toEuclideanLin
    (Matrix.isPositive_toEuclideanLin_iff.mpr hT) e he g hg hground hplace hres
  refine (Matrix.posDef_iff_dotProduct_mulVec).mpr ⟨hT.isHermitian, ?_⟩
  intro x hx
  have hne : (WithLp.toLp 2 x : EuclideanSpace ℝ n) ≠ 0 := by
    intro h
    apply hx
    simpa [WithLp.ofLp_toLp] using congrArg WithLp.ofLp h
  have h := hpos (WithLp.toLp 2 x) hne
  rw [inner_toEuclideanLin] at h
  simpa [WithLp.ofLp_toLp, Pi.star_apply, star_trivial] using h




theorem harmonicForm_posDef_of_components {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ) [Invertible D]
    (hT : (harmonicForm A B D).PosSemidef)
    (e : EuclideanSpace ℝ m) (he : e ≠ 0) (g : ℝ) (hg : 0 < g)
    (hground : g * ‖e‖ ^ 2 ≤ ⟪e, (harmonicForm A B D).toEuclideanLin e⟫_ℝ)
    (hplace : ∀ f : EuclideanSpace ℝ m,
      0 ≤ groundCoord e f
        * ⟪e, (harmonicForm A B D).toEuclideanLin (transversePart e f)⟫_ℝ)
    (hres : ∀ w : EuclideanSpace ℝ m, ⟪e, w⟫_ℝ = 0 → w ≠ 0 →
      0 < ⟪w, (harmonicForm A B D).toEuclideanLin w⟫_ℝ) :
    (harmonicForm A B D).PosDef :=
  posDef_of_components (harmonicForm A B D) hT e he g hg hground hplace hres




noncomputable def truncOldBlock (a b : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  oldOldBlock b (fun i : Fin N => oldBasis a i)


noncomputable def truncCrossBlock (a b : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N ⊕ Fin N) ℝ :=
  oldCollarBlock b (fun i : Fin N => oldBasis a i) (truncCollarBasis a b N)


noncomputable def truncCollarBlock (a b : ℝ) (N : ℕ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  collarCollarBlock b (truncCollarBasis a b N)


noncomputable def truncHarmonicForm (a b : ℝ) (N : ℕ)
    [Invertible (truncCollarBlock a b N)] : Matrix (Fin N) (Fin N) ℝ :=
  harmonicForm (truncOldBlock a b N) (truncCrossBlock a b N) (truncCollarBlock a b N)


theorem truncHarmonicForm_posDef_of_components (a b : ℝ) (N : ℕ)
    [Invertible (truncCollarBlock a b N)]
    (hT : (truncHarmonicForm a b N).PosSemidef)
    (e : EuclideanSpace ℝ (Fin N)) (he : e ≠ 0) (g : ℝ) (hg : 0 < g)
    (hground : g * ‖e‖ ^ 2 ≤ ⟪e, (truncHarmonicForm a b N).toEuclideanLin e⟫_ℝ)
    (hplace : ∀ f : EuclideanSpace ℝ (Fin N),
      0 ≤ groundCoord e f
        * ⟪e, (truncHarmonicForm a b N).toEuclideanLin (transversePart e f)⟫_ℝ)
    (hres : ∀ w : EuclideanSpace ℝ (Fin N), ⟪e, w⟫_ℝ = 0 → w ≠ 0 →
      0 < ⟪w, (truncHarmonicForm a b N).toEuclideanLin w⟫_ℝ) :
    (truncHarmonicForm a b N).PosDef :=
  harmonicForm_posDef_of_components (truncOldBlock a b N) (truncCrossBlock a b N)
    (truncCollarBlock a b N) hT e he g hg hground hplace hres




theorem truncBasis_posDef_of_components (a b : ℝ) (N : ℕ)
    [Invertible (truncCollarBlock a b N)]
    (hA : (truncOldBlock a b N).PosDef)
    (hD : (truncCollarBlock a b N).PosDef)
    (hT : (truncHarmonicForm a b N).PosSemidef)
    (e : EuclideanSpace ℝ (Fin N)) (he : e ≠ 0) (g : ℝ) (hg : 0 < g)
    (hground : g * ‖e‖ ^ 2 ≤ ⟪e, (truncHarmonicForm a b N).toEuclideanLin e⟫_ℝ)
    (hplace : ∀ f : EuclideanSpace ℝ (Fin N),
      0 ≤ groundCoord e f
        * ⟪e, (truncHarmonicForm a b N).toEuclideanLin (transversePart e f)⟫_ℝ)
    (hres : ∀ w : EuclideanSpace ℝ (Fin N), ⟪e, w⟫_ℝ = 0 → w ≠ 0 →
      0 < ⟪w, (truncHarmonicForm a b N).toEuclideanLin w⟫_ℝ) :
    (gramMatrix b (truncBasis a b N)).PosDef := by
  haveI : Invertible (collarCollarBlock b (truncCollarBasis a b N)) :=
    inferInstanceAs (Invertible (truncCollarBlock a b N))
  refine truncBasis_posDef_of_schur a b N hA hD ?_
  exact truncHarmonicForm_posDef_of_components a b N hT e he g hg hground hplace hres




theorem truncHarmonicForm_dotProduct (a b : ℝ) (N : ℕ)
    [Invertible (truncCollarBlock a b N)]
    (hD : (truncCollarBlock a b N).PosDef) (v : Fin N → ℝ) :
    harmonicExtension (truncCrossBlock a b N) (truncCollarBlock a b N) v
        ⬝ᵥ (oldNewBlock (truncOldBlock a b N) (truncCrossBlock a b N)
          (truncCollarBlock a b N) *ᵥ
          harmonicExtension (truncCrossBlock a b N) (truncCollarBlock a b N) v)
      = v ⬝ᵥ ((truncHarmonicForm a b N) *ᵥ v) :=
  dotProduct_harmonicExtension _ _ _ hD.isHermitian v

end RHLean.GateII.Reduction



end Inline_GateII_Reduction









namespace RHLean.GateII



structure ArithmeticResiduals where
  sweep : Chain.FiniteSweep
  awgcTail : Chain.AWGCTail
  mertensSweep : AWGC.MertensSweep
  mertensTail : AWGC.MertensTail
  Vtail : ∀ k : ℕ, 3594642 ≤ k →
    Chain.Vsum k ≤ (12 / 100) * Real.log k + (2873 / 1000)
  W : ℕ → ℝ
  Wtail : ∀ k : ℕ, 3594642 ≤ k → W k ≤ (47 / 1000) * Real.log k
  Wsweep : ∀ k : ℕ, 7 ≤ k → k ≤ 3594641 → 0 < Chain.masterGap k (W k)
  chihat : ℕ → ℕ → ℝ
  chi : ∀ k m : ℕ, chihat k m ≤ Chain.V k m / Real.log 2




theorem gateII_arithmetic_budget_of_residuals (R : ArithmeticResiduals) :
    (∀ k : ℕ, 7 ≤ k → Chain.AWGC k) ∧
      (∀ k : ℕ, 7 ≤ k →
        ∑ m ∈ Finset.range (k + 1), R.chihat k m ≤ Chain.sigma k) ∧
      (∀ k : ℕ, 7 ≤ k → (1 / 2 : ℝ) < Chain.Bk k - Chain.sigma k) ∧
      (∀ k : ℕ, 7 ≤ k → 0 < Chain.masterGap k (R.W k)) :=
  Chain.gateII_arithmetic_budget (W := R.W) (chihat := R.chihat)
    R.sweep R.awgcTail
    (fun k hk => AWGC.MertensActive_of_sweep_tail R.mertensSweep R.mertensTail k hk)
    R.Vtail R.Wtail R.Wsweep R.chi

end RHLean.GateII



section Inline_GateII_SweepIncremental

















open Finset
open scoped BigOperators

namespace RHLean.GateII.Sweep

set_option maxHeartbeats 2000000

open RHLean.GateII.Chain






theorem activeN_succ (k : ℕ) (hk : 2 ≤ k) :
    activeN k =
      (activeN (k - 1)).filter (fun n => ¬ n ∣ k)
        ∪ ((Finset.range k).filter (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1))) := by
  ext n
  simp only [activeN, Finset.mem_filter, Finset.mem_range, Finset.mem_union]
  constructor
  · rintro ⟨hnk, hΛ, hndvd⟩
    have hn_ne_k : n ≠ k := by rintro rfl; exact hndvd dvd_rfl
    have hnk' : n < k := by omega
    by_cases hd : n ∣ k - 1
    · exact Or.inr ⟨by omega, hΛ, hd⟩
    · exact Or.inl ⟨⟨by omega, hΛ, hd⟩, hndvd⟩
  · rintro (⟨⟨hnk', hΛ, hnd1⟩, hnd2⟩ | ⟨hnk', hΛ, hd⟩)
    · exact ⟨by omega, hΛ, hnd2⟩
    · have hnd2 : ¬ n ∣ k := by
        intro hdk
        have hsub : n ∣ k - (k - 1) := Nat.dvd_sub hdk hd
        have hkm : k - (k - 1) = 1 := by omega
        rw [hkm] at hsub
        have hn1 : n = 1 := Nat.dvd_one.mp hsub
        exact hΛ (by simp [Lambda, hn1])
      exact ⟨by omega, hΛ, hnd2⟩





theorem div_eq_pred_div {k n : ℕ} (hn : 0 < n) (hnd : ¬ n ∣ k) :
    (k - 1) / n = k / n := by
  set q := k / n with hq
  set r := k % n with hr
  have hk : k = q * n + r := by
    have h := Nat.div_add_mod k n
    rw [show k / n = q from rfl, show k % n = r from rfl] at h
    rw [mul_comm n q] at h
    omega
  have hrlt : r < n := Nat.mod_lt k hn
  have hrpos : 0 < r := Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
  have hle : q * n ≤ k - 1 := by omega
  have hdist : (q + 1) * n = q * n + n := by ring
  have hlt : k - 1 < (q + 1) * n := by
    rw [hdist]
    omega
  exact Nat.div_eq_of_lt_le hle hlt


theorem div_eq_pred_div_add {k n : ℕ} (hn : 0 < n) (hk : 0 < k) (hdvd : n ∣ k) :
    k / n = (k - 1) / n + 1 := by
  obtain ⟨c, rfl⟩ := hdvd
  rw [mul_comm n c]
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; simp at hk
    · exact h
  have hle : (c - 1) * n ≤ c * n - 1 := by
    have hc1 : 1 ≤ c := hc
    have hsplit : c * n = (c - 1) * n + n := by
      calc c * n = ((c - 1) + 1) * n := by rw [Nat.sub_add_cancel hc1]
        _ = (c - 1) * n + n := by ring
    rw [hsplit]
    omega
  have hlt : c * n - 1 < ((c - 1) + 1) * n := by
    have hc1 : 1 ≤ c := hc
    rw [Nat.sub_add_cancel hc1]
    have hpos : 0 < c * n := Nat.mul_pos hc hn
    omega
  have hdiv : (c * n - 1) / n = c - 1 := Nat.div_eq_of_lt_le hle hlt
  have hmul : c * n / n = c := by
    rw [mul_comm c n]
    exact Nat.mul_div_cancel_left c hn
  rw [hmul, hdiv]
  omega




theorem Nset_succ (k m : ℕ) (hk : 2 ≤ k) :
    Nset k m =
      (Nset (k - 1) m).filter (fun n => ¬ n ∣ k)
        ∪ ((Finset.range k).filter
            (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1) ∧ k / n = m)) := by
  ext n
  simp only [Nset, Finset.mem_filter, Finset.mem_range, Finset.mem_union]
  constructor
  · rintro ⟨hnk, hΛ, hndvd, hdiv⟩
    have hn_ne_k : n ≠ k := by rintro rfl; exact hndvd dvd_rfl
    have hnk' : n < k := by omega
    by_cases hd : n ∣ k - 1
    · exact Or.inr ⟨hnk', hΛ, hd, hdiv⟩
    · have hn0 : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp [Lambda] at hΛ
        · exact h
      have hdiv' : (k - 1) / n = m := by
        rw [div_eq_pred_div hn0 hndvd]
        exact hdiv
      exact Or.inl ⟨⟨by omega, hΛ, hd, hdiv'⟩, hndvd⟩
  · rintro (⟨⟨hnk', hΛ, hd1, hdiv⟩, hnd⟩ | ⟨hnk', hΛ, hd, hdiv⟩)
    · have hn0 : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp [Lambda] at hΛ
        · exact h
      have hkdiv : k / n = m := by
        rw [← div_eq_pred_div hn0 hnd]
        exact hdiv
      exact ⟨by omega, hΛ, hnd, hkdiv⟩
    · have hnd2 : ¬ n ∣ k := by
        intro hdk
        have hsub : n ∣ k - (k - 1) := Nat.dvd_sub hdk hd
        have hkm : k - (k - 1) = 1 := by omega
        rw [hkm] at hsub
        have hn1 : n = 1 := Nat.dvd_one.mp hsub
        exact hΛ (by simp [Lambda, hn1])
      have hn0 : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp [Lambda] at hΛ
        · exact h
      have hdiv' : (k - 1) / n = m := by
        rw [div_eq_pred_div hn0 hnd2]
        exact hdiv
      exact ⟨by omega, hΛ, hnd2, hdiv⟩





noncomputable def binA (k m : ℕ) (hi : ℕ → ℚ) : ℚ :=
  ∑ n ∈ Nset k m, (hi n) ^ 2 / (n : ℚ)


noncomputable def binB (k m : ℕ) (lo : ℕ → ℚ) : ℚ :=
  ∑ n ∈ Nset k m, lo n


noncomputable def binC (k m : ℕ) : ℚ :=
  ∑ n ∈ Nset k m, (n : ℚ)

theorem binA_succ (k m : ℕ) (hk : 2 ≤ k) (hi : ℕ → ℚ) :
    binA k m hi = binA (k - 1) m hi
      - ∑ n ∈ (Nset (k - 1) m).filter (fun n => n ∣ k), (hi n) ^ 2 / (n : ℚ)
      + ∑ n ∈ (Finset.range k).filter
          (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1) ∧ k / n = m), (hi n) ^ 2 / (n : ℚ) := by
  unfold binA
  rw [Nset_succ k m hk]
  have hdisj : Disjoint ((Nset (k - 1) m).filter (fun n => ¬ n ∣ k))
      ((Finset.range k).filter
        (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1) ∧ k / n = m)) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    rw [Finset.mem_filter] at hn1 hn2
    exact (mem_Nset.mp hn1.1).2.2.1 hn2.2.2.1
  rw [Finset.sum_union hdisj]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := Nset (k - 1) m) (p := fun n => n ∣ k) (f := fun n => (hi n) ^ 2 / (n : ℚ))
  linarith

theorem binB_succ (k m : ℕ) (hk : 2 ≤ k) (lo : ℕ → ℚ) :
    binB k m lo = binB (k - 1) m lo
      - ∑ n ∈ (Nset (k - 1) m).filter (fun n => n ∣ k), lo n
      + ∑ n ∈ (Finset.range k).filter
          (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1) ∧ k / n = m), lo n := by
  unfold binB
  rw [Nset_succ k m hk]
  have hdisj : Disjoint ((Nset (k - 1) m).filter (fun n => ¬ n ∣ k))
      ((Finset.range k).filter
        (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1) ∧ k / n = m)) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    rw [Finset.mem_filter] at hn1 hn2
    exact (mem_Nset.mp hn1.1).2.2.1 hn2.2.2.1
  rw [Finset.sum_union hdisj]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := Nset (k - 1) m) (p := fun n => n ∣ k) (f := fun n => lo n)
  linarith

theorem binC_succ (k m : ℕ) (hk : 2 ≤ k) :
    binC k m = binC (k - 1) m
      - ∑ n ∈ (Nset (k - 1) m).filter (fun n => n ∣ k), (n : ℚ)
      + ∑ n ∈ (Finset.range k).filter
          (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1) ∧ k / n = m), (n : ℚ) := by
  unfold binC
  rw [Nset_succ k m hk]
  have hdisj : Disjoint ((Nset (k - 1) m).filter (fun n => ¬ n ∣ k))
      ((Finset.range k).filter
        (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1) ∧ k / n = m)) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    rw [Finset.mem_filter] at hn1 hn2
    exact (mem_Nset.mp hn1.1).2.2.1 hn2.2.2.1
  rw [Finset.sum_union hdisj]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := Nset (k - 1) m) (p := fun n => n ∣ k) (f := fun n => (n : ℚ))
  linarith







noncomputable def binTerm (A B C : ℚ) : ℚ := if C = 0 then 0 else A - B ^ 2 / C


theorem Vhi_eq_binTerm (k m : ℕ) (lo hi : ℕ → ℚ) :
    Vhi k m lo hi = binTerm (binA k m hi) (binB k m lo) (binC k m) := by
  unfold Vhi binTerm binA binB binC
  by_cases h : (∑ n ∈ Nset k m, (n : ℚ)) = 0
  · have hemp : Nset k m = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro n hn
      have hpos : (0 : ℚ) < (n : ℚ) := by
        exact_mod_cast Nset_pos hn
      have hle : (n : ℚ) ≤ ∑ x ∈ Nset k m, (x : ℚ) :=
        Finset.single_le_sum (f := fun x : ℕ => (x : ℚ))
          (fun x hx => by exact_mod_cast Nat.zero_le x) hn
      linarith
    simp [hemp]
  · simp [h]


theorem binTerm_add (A B C a b c : ℚ) (hC : C ≠ 0) (hCc : C + c ≠ 0) :
    binTerm (A + a) (B + b) (C + c) - binTerm A B C
      = (A + a - (B + b) ^ 2 / (C + c)) - (A - B ^ 2 / C) := by
  unfold binTerm
  simp [hC, hCc]


theorem binTerm_sub (A B C a b c : ℚ) (hC : C ≠ 0) (hCc : C - c ≠ 0) :
    binTerm (A - a) (B - b) (C - c) - binTerm A B C
      = (A - a - (B - b) ^ 2 / (C - c)) - (A - B ^ 2 / C) := by
  unfold binTerm
  simp [hC, hCc]


theorem VhiSum_eq_binTerms (k : ℕ) (lo hi : ℕ → ℚ) :
    (∑ m ∈ Finset.range (k + 1), Vhi k m lo hi)
      = ∑ m ∈ Finset.range (k + 1),
          binTerm (binA k m hi) (binB k m lo) (binC k m) := by
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Vhi_eq_binTerm]





structure BinState where
  A : ℚ
  B : ℚ
  C : ℚ

namespace BinState


noncomputable def term (s : BinState) : ℚ := binTerm s.A s.B s.C


def add (s : BinState) (a b c : ℚ) : BinState :=
  ⟨s.A + a, s.B + b, s.C + c⟩


def sub (s : BinState) (a b c : ℚ) : BinState :=
  ⟨s.A - a, s.B - b, s.C - c⟩

end BinState


theorem sum_term_update (f : ℕ → BinState) (m K : ℕ) (s : BinState)
    (hm : m < K) :
    (∑ x ∈ Finset.range K, if x = m then s.term else (f x).term)
      = (∑ x ∈ Finset.range K, (f x).term) - (f m).term + s.term := by
  have h : ∀ x, (if x = m then s.term else (f x).term)
      = (if x = m then (s.term - (f m).term) else 0) + (f x).term := by
    intro x
    by_cases hx : x = m <;> simp [hx]
  calc (∑ x ∈ Finset.range K, if x = m then s.term else (f x).term)
      = ∑ x ∈ Finset.range K,
          ((if x = m then (s.term - (f m).term) else 0) + (f x).term) := by
        exact Finset.sum_congr rfl (fun x _ => h x)
    _ = (∑ x ∈ Finset.range K, if x = m then (s.term - (f m).term) else 0)
          + ∑ x ∈ Finset.range K, (f x).term := by
        rw [Finset.sum_add_distrib]
    _ = (s.term - (f m).term) + ∑ x ∈ Finset.range K, (f x).term := by
        rw [Finset.sum_ite_eq']
        simp [hm]
    _ = (∑ x ∈ Finset.range K, (f x).term) - (f m).term + s.term := by ring


theorem sum_term_add (f : ℕ → BinState) (m K : ℕ) (a b c : ℚ) (hm : m < K) :
    (∑ x ∈ Finset.range K,
        if x = m then ((f m).add a b c).term else (f x).term)
      = (∑ x ∈ Finset.range K, (f x).term) - (f m).term
        + ((f m).add a b c).term :=
  sum_term_update f m K _ hm


theorem sum_term_sub (f : ℕ → BinState) (m K : ℕ) (a b c : ℚ) (hm : m < K) :
    (∑ x ∈ Finset.range K,
        if x = m then ((f m).sub a b c).term else (f x).term)
      = (∑ x ∈ Finset.range K, (f x).term) - (f m).term
        + ((f m).sub a b c).term :=
  sum_term_update f m K _ hm

end RHLean.GateII.Sweep



end Inline_GateII_SweepIncremental

section Inline_wp_WP_B1



























open Finset
open scoped BigOperators

namespace RHLean.GateII.Sweep

open RHLean.GateII.Chain




noncomputable def BinState.ofSums (k m : ℕ) (lo hi : ℕ → ℚ) : BinState :=
  ⟨binA k m hi, binB k m lo, binC k m⟩


noncomputable def total (f : ℕ → BinState) (K : ℕ) : ℚ :=
  ∑ m ∈ Finset.range K, (f m).term



theorem total_ofSums_eq_VhiSum (k : ℕ) (lo hi : ℕ → ℚ) :
    total (fun m => BinState.ofSums k m lo hi) (k + 1)
      = ∑ m ∈ Finset.range (k + 1), Vhi k m lo hi := by
  refine Finset.sum_congr rfl (fun m _ => ?_)
  exact (Vhi_eq_binTerm k m lo hi).symm


theorem total_ofSums_eq_VhiSum' (k : ℕ) (lo hi : ℕ → ℚ) :
    total (fun m => BinState.ofSums k m lo hi) (k + 1)
      = ∑ m ∈ Finset.range (k + 1), Vhi k m lo hi :=
  total_ofSums_eq_VhiSum k lo hi




noncomputable def checkK (k : ℕ) (lo hi hiLog : ℕ → ℚ) (log2lo log2hi : ℚ) : Bool :=
  decide ((1 / log2lo) * (∑ m ∈ Finset.range (k + 1), Vhi k m lo hi)
    ≤ Slow k lo hiLog (log2hi + 1 / 2))



theorem checkK_sound {k : ℕ} {lo hi hiLog : ℕ → ℚ} {log2lo log2hi : ℚ}
    (h : checkK k lo hi hiLog log2lo log2hi = true) :
    (1 / (log2lo : ℝ)) * ((∑ m ∈ Finset.range (k + 1), Vhi k m lo hi : ℚ) : ℝ)
      ≤ ((Slow k lo hiLog (log2hi + 1 / 2) : ℚ) : ℝ) := by
  have h' : (1 / log2lo) * (∑ m ∈ Finset.range (k + 1), Vhi k m lo hi)
      ≤ Slow k lo hiLog (log2hi + 1 / 2) := of_decide_eq_true h
  calc (1 / (log2lo : ℝ)) * ((∑ m ∈ Finset.range (k + 1), Vhi k m lo hi : ℚ) : ℝ)
      = (((1 / log2lo) * (∑ m ∈ Finset.range (k + 1), Vhi k m lo hi) : ℚ) : ℝ) := by
        push_cast
        ring
    _ ≤ ((Slow k lo hiLog (log2hi + 1 / 2) : ℚ) : ℝ) := by exact_mod_cast h'




noncomputable def checkUpTo (lo hi hiLog : ℕ → ℚ) (log2lo log2hi : ℚ) : ℕ → Bool
  | 0 => true
  | (m + 1) =>
      checkK (m + 2) lo hi hiLog log2lo log2hi
        && checkUpTo lo hi hiLog log2lo log2hi m


noncomputable def checkRange (N : ℕ) (lo hi hiLog : ℕ → ℚ) (log2lo log2hi : ℚ) : Bool :=
  checkUpTo lo hi hiLog log2lo log2hi N


theorem checkUpTo_sound {lo hi hiLog : ℕ → ℚ} {log2lo log2hi : ℚ} (m : ℕ) :
    checkUpTo lo hi hiLog log2lo log2hi m = true →
      ∀ k : ℕ, 2 ≤ k → k < m + 2 →
        (1 / (log2lo : ℝ)) * ((∑ j ∈ Finset.range (k + 1), Vhi k j lo hi : ℚ) : ℝ)
          ≤ ((Slow k lo hiLog (log2hi + 1 / 2) : ℚ) : ℝ) := by
  induction m with
  | zero => intro _ k hk hklt; omega
  | succ m ih =>
      intro h k hk hklt
      have hs : checkK (m + 2) lo hi hiLog log2lo log2hi = true ∧
          checkUpTo lo hi hiLog log2lo log2hi m = true := by
        simpa [checkUpTo] using h
      rcases Nat.lt_or_ge k (m + 2) with hlt | hge
      · exact ih hs.2 k hk hlt
      · have hk_eq : k = m + 2 := by omega
        subst hk_eq
        exact checkK_sound hs.1


theorem checkRange_sound {N : ℕ} {lo hi hiLog : ℕ → ℚ} {log2lo log2hi : ℚ}
    (h : checkRange N lo hi hiLog log2lo log2hi = true) :
    ∀ k : ℕ, 2 ≤ k → k < N + 2 →
      (1 / (log2lo : ℝ)) * ((∑ j ∈ Finset.range (k + 1), Vhi k j lo hi : ℚ) : ℝ)
        ≤ ((Slow k lo hiLog (log2hi + 1 / 2) : ℚ) : ℝ) :=
  checkUpTo_sound N h




theorem FiniteSweep_of_checkRange {lo hi hiLog : ℕ → ℚ} {log2lo log2hi : ℚ}
    (hlog2lo_pos : 0 < log2lo)
    (hlog2lo : (log2lo : ℝ) ≤ Real.log 2)
    (hlog2hi : Real.log 2 ≤ (log2hi : ℝ))
    (hlo0 : ∀ n, 0 ≤ lo n)
    (hlo : ∀ n, IsPrimePow n → (lo n : ℝ) ≤ Lambda n)
    (hhi : ∀ n, IsPrimePow n → Lambda n ≤ (hi n : ℝ))
    (hlog : ∀ n : ℕ, IsPrimePow n → Real.log (n : ℝ) ≤ (hiLog n : ℝ))
    (hcheck : checkRange 3594640 lo hi hiLog log2lo log2hi = true) :
    FiniteSweep :=
  FiniteSweep_of_boxes hlog2lo_pos hlog2lo hlog2hi hlo0 hlo hhi hlog
    (fun k hk hkX => checkRange_sound hcheck k hk (by omega))









theorem fixedPoint_check_sound {log2lo VhiSum Vhat eps Slow : ℝ}
    (hlo : 0 < log2lo)
    (hV : VhiSum ≤ Vhat + eps)
    (hcheck : (1 / log2lo) * Vhat + eps / log2lo ≤ Slow) :
    (1 / log2lo) * VhiSum ≤ Slow := by
  have hcoef : 0 < 1 / log2lo := by positivity
  have h1 : (1 / log2lo) * VhiSum ≤ (1 / log2lo) * (Vhat + eps) :=
    mul_le_mul_of_nonneg_left hV hcoef.le
  have h2 : (1 / log2lo) * (Vhat + eps) = (1 / log2lo) * Vhat + eps / log2lo := by
    field_simp
  linarith




noncomputable def removeSet (k m : ℕ) : Finset ℕ :=
  (Nset (k - 1) m).filter (fun n => n ∣ k)


noncomputable def insertSet (k m : ℕ) : Finset ℕ :=
  (Finset.range k).filter (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1) ∧ k / n = m)






theorem ofSums_succ (k m : ℕ) (hk : 2 ≤ k) (lo hi : ℕ → ℚ) :
    BinState.ofSums k m lo hi
      = ((BinState.ofSums (k - 1) m lo hi).sub
          (∑ n ∈ removeSet k m, (hi n) ^ 2 / (n : ℚ))
          (∑ n ∈ removeSet k m, lo n)
          (∑ n ∈ removeSet k m, (n : ℚ))).add
        (∑ n ∈ insertSet k m, (hi n) ^ 2 / (n : ℚ))
        (∑ n ∈ insertSet k m, lo n)
        (∑ n ∈ insertSet k m, (n : ℚ)) := by
  simp only [BinState.ofSums, BinState.sub, BinState.add, removeSet, insertSet,
    binA_succ k m hk hi, binB_succ k m hk lo, binC_succ k m hk]




noncomputable def stepBin (k m : ℕ) (s : BinState) (lo hi : ℕ → ℚ) : BinState :=
  (s.sub
    (∑ n ∈ removeSet k m, (hi n) ^ 2 / (n : ℚ))
    (∑ n ∈ removeSet k m, lo n)
    (∑ n ∈ removeSet k m, (n : ℚ))).add
  (∑ n ∈ insertSet k m, (hi n) ^ 2 / (n : ℚ))
  (∑ n ∈ insertSet k m, lo n)
  (∑ n ∈ insertSet k m, (n : ℚ))



theorem stepBin_correct (k m : ℕ) (hk : 2 ≤ k) (lo hi : ℕ → ℚ) :
    stepBin k m (BinState.ofSums (k - 1) m lo hi) lo hi = BinState.ofSums k m lo hi :=
  (ofSums_succ k m hk lo hi).symm

end RHLean.GateII.Sweep

#print axioms RHLean.GateII.Sweep.stepBin_correct

#print axioms RHLean.GateII.Sweep.total_ofSums_eq_VhiSum
#print axioms RHLean.GateII.Sweep.checkK_sound
#print axioms RHLean.GateII.Sweep.checkUpTo_sound
#print axioms RHLean.GateII.Sweep.checkRange_sound
#print axioms RHLean.GateII.Sweep.FiniteSweep_of_checkRange
#print axioms RHLean.GateII.Sweep.fixedPoint_check_sound
#print axioms RHLean.GateII.Sweep.ofSums_succ
#print axioms RHLean.GateII.Sweep.stepBin_correct



end Inline_wp_WP_B1

section Inline_wp_WP_B1_loop















open Finset
open scoped BigOperators

namespace RHLean.GateII.Sweep

open RHLean.GateII.Chain




def lsum (f : ℚ × ℚ × ℚ → ℚ) (l : List (ℚ × ℚ × ℚ)) : ℚ := (l.map f).sum

@[simp] theorem lsum_nil (f : ℚ × ℚ × ℚ → ℚ) : lsum f [] = 0 := rfl

theorem lsum_cons (f : ℚ × ℚ × ℚ → ℚ) (x : ℚ × ℚ × ℚ) (l : List (ℚ × ℚ × ℚ)) :
    lsum f (x :: l) = f x + lsum f l := by
  simp [lsum]




def BinState.subTriple (s : BinState) (t : ℚ × ℚ × ℚ) : BinState :=
  s.sub t.1 t.2.1 t.2.2


def BinState.addTriple (s : BinState) (t : ℚ × ℚ × ℚ) : BinState :=
  s.add t.1 t.2.1 t.2.2

theorem BinState.sub_sub (s : BinState) (a b c a' b' c' : ℚ) :
    (s.sub a b c).sub a' b' c' = s.sub (a + a') (b + b') (c + c') := by
  obtain ⟨A, B, C⟩ := s
  simp only [BinState.sub, BinState.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

theorem BinState.add_add (s : BinState) (a b c a' b' c' : ℚ) :
    (s.add a b c).add a' b' c' = s.add (a + a') (b + b') (c + c') := by
  obtain ⟨A, B, C⟩ := s
  simp only [BinState.add, BinState.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

theorem BinState.sub_add (s : BinState) (a b c a' b' c' : ℚ) :
    (s.sub a b c).add a' b' c' = ⟨s.A - a + a', s.B - b + b', s.C - c + c'⟩ := rfl

theorem BinState.add_sub (s : BinState) (a b c a' b' c' : ℚ) :
    (s.add a b c).sub a' b' c' = ⟨s.A + a - a', s.B + b - b', s.C + c - c'⟩ := rfl




theorem foldl_subTriple (l : List (ℚ × ℚ × ℚ)) (s : BinState) :
    l.foldl BinState.subTriple s
      = s.sub (lsum (fun t => t.1) l) (lsum (fun t => t.2.1) l)
          (lsum (fun t => t.2.2) l) := by
  induction l generalizing s with
  | nil => simp [BinState.sub]
  | cons x xs ih =>
      rw [List.foldl_cons, ih, lsum_cons, lsum_cons, lsum_cons, BinState.subTriple,
        BinState.sub_sub]


theorem foldl_addTriple (l : List (ℚ × ℚ × ℚ)) (s : BinState) :
    l.foldl BinState.addTriple s
      = s.add (lsum (fun t => t.1) l) (lsum (fun t => t.2.1) l)
          (lsum (fun t => t.2.2) l) := by
  induction l generalizing s with
  | nil => simp [BinState.add]
  | cons x xs ih =>
      rw [List.foldl_cons, ih, lsum_cons, lsum_cons, lsum_cons, BinState.addTriple,
        BinState.add_add]



theorem foldl_sub_addTriple (l₁ l₂ : List (ℚ × ℚ × ℚ)) (s : BinState) :
    l₂.foldl BinState.addTriple (l₁.foldl BinState.subTriple s)
      = BinState.add
          (BinState.sub s (lsum (fun t => t.1) l₁) (lsum (fun t => t.2.1) l₁)
            (lsum (fun t => t.2.2) l₁))
          (lsum (fun t => t.1) l₂) (lsum (fun t => t.2.1) l₂) (lsum (fun t => t.2.2) l₂) := by
  rw [foldl_subTriple, foldl_addTriple]






structure SweepState where
  bins : ℕ → BinState
  tot : ℚ

namespace SweepState


noncomputable def upd (s : SweepState) (m : ℕ) (f : BinState → BinState) : SweepState :=
  ⟨fun x => if x = m then f (s.bins m) else s.bins x,
   s.tot - (s.bins m).term + (f (s.bins m)).term⟩



def Inv (K : ℕ) (s : SweepState) : Prop :=
  s.tot = ∑ x ∈ Finset.range K, (s.bins x).term

theorem term_ite {c : Prop} [Decidable c] (a b : BinState) :
    (if c then a else b).term = if c then a.term else b.term := by
  by_cases h : c <;> simp [h]

theorem Inv.upd {K : ℕ} {s : SweepState} (hinv : Inv K s) {m : ℕ} (hm : m < K)
    (f : BinState → BinState) : Inv K (s.upd m f) := by
  have h := sum_term_update (f := s.bins) (m := m) (K := K)
    (s := f (s.bins m)) hm
  show s.tot - (s.bins m).term + (f (s.bins m)).term
      = ∑ x ∈ Finset.range K, (if x = m then f (s.bins m) else s.bins x).term
  rw [Finset.sum_congr rfl (fun x _ =>
    term_ite (c := x = m) (f (s.bins m)) (s.bins x)), h, hinv]

end SweepState




noncomputable def foldUpd (u : BinState → (ℚ × ℚ × ℚ) → BinState) (s : ℕ → BinState)
    (l : List (ℕ × (ℚ × ℚ × ℚ))) : ℕ → BinState :=
  l.foldl (fun (s : ℕ → BinState) p => fun x => if x = p.1 then u (s p.1) p.2 else s x) s




theorem foldUpd_apply (u : BinState → (ℚ × ℚ × ℚ) → BinState) (s : ℕ → BinState)
    (l : List (ℕ × (ℚ × ℚ × ℚ))) (m : ℕ) :
    foldUpd u s l m
      = List.foldl u (s m) ((l.filter (fun p => p.1 = m)).map (fun p => p.2)) := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
      simp only [foldUpd, List.foldl_cons] at ih ⊢
      rw [ih]
      by_cases hp : p.1 = m
      · rw [List.filter_cons_of_pos (p := fun p : ℕ × (ℚ × ℚ × ℚ) => p.1 = m)
          (by simpa using hp),
          List.map_cons, List.foldl_cons]
        simp [hp]
      · rw [List.filter_cons_of_neg (p := fun p : ℕ × (ℚ × ℚ × ℚ) => p.1 = m)
          (by simpa using hp), if_neg (by simpa [eq_comm] using hp)]



theorem lsum_map_val_toList (s : Finset ℕ) (f : ℕ → ℚ × ℚ × ℚ) (sel : (ℚ × ℚ × ℚ) → ℚ) :
    lsum sel ((s.val.toList).map f) = ∑ n ∈ s, sel (f n) := by
  unfold lsum
  rw [List.map_map, ← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList,
    Finset.sum_eq_multiset_sum]
  rfl





noncomputable def remAll (k : ℕ) : Finset ℕ :=
  (activeN (k - 1)).filter (fun n => n ∣ k)



noncomputable def insAll (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1))


noncomputable def affected (k : ℕ) : Finset ℕ :=
  (remAll k).image (fun n => (k - 1) / n) ∪ (insAll k).image (fun n => k / n)


theorem Nset_eq_activeN_filter (k m : ℕ) :
    Nset k m = (activeN k).filter (fun n => k / n = m) := by
  unfold Nset activeN
  rw [Finset.filter_filter]
  refine Finset.filter_congr ?_
  intro n _
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩



theorem removeSet_eq_remAll (k m : ℕ) :
    removeSet k m = (remAll k).filter (fun n => (k - 1) / n = m) := by
  unfold removeSet remAll
  rw [Nset_eq_activeN_filter]
  ext n
  simp only [Finset.mem_filter]
  tauto


theorem insertSet_eq_insAll (k m : ℕ) :
    insertSet k m = (insAll k).filter (fun n => k / n = m) := by
  unfold insertSet insAll
  rw [Finset.filter_filter]
  refine Finset.filter_congr ?_
  intro n _
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩




theorem foldl_bin_apply (l : List ℕ) (F : ℕ → BinState → BinState) (s : ℕ → BinState)
    (m : ℕ) :
    (l.foldl (fun s b x => if x = b then F b (s b) else s x) s) m
      = (l.filter (fun b => b = m)).foldl (fun acc b => F b acc) (s m) := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih =>
      simp only [List.foldl_cons] at ih ⊢
      rw [ih]
      by_cases hb : b = m
      · subst hb
        have hf : List.filter (fun x => decide (x = b)) (b :: l)
            = b :: List.filter (fun x => decide (x = b)) l :=
          List.filter_cons_of_pos (p := fun x => x = b) (by simp)
        rw [hf, List.foldl_cons, if_pos rfl]
      · rw [List.filter_cons_of_neg (p := fun x => x = m) (by simpa using hb),
          if_neg (fun h => hb h.symm)]


theorem SweepState.bins_foldl (l : List ℕ) (F : ℕ → BinState → BinState) (s : SweepState) :
    (l.foldl (fun s b => s.upd b (F b)) s).bins
      = l.foldl (fun f b x => if x = b then F b (f b) else f x) s.bins := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rfl


theorem SweepState.Inv.foldl_upd {K : ℕ} (l : List ℕ) (F : ℕ → BinState → BinState)
    {s : SweepState} (hinv : Inv K s) (hK : ∀ m ∈ l, m < K) :
    Inv K (l.foldl (fun s b => s.upd b (F b)) s) := by
  induction l generalizing s with
  | nil => exact hinv
  | cons b l ih =>
      simp only [List.foldl_cons]
      exact ih (hinv.upd (hK b (List.mem_cons_self ..)) (F b))
        (fun m hm => hK m (List.mem_cons_of_mem _ hm))



noncomputable def sweepStep (k : ℕ) (lo hi : ℕ → ℚ) (s : SweepState) : SweepState :=
  (affected k).toList.foldl (fun s m => s.upd m (fun b => stepBin k m b lo hi)) s


theorem SweepState.bins_sweepStep (k : ℕ) (lo hi : ℕ → ℚ) (s : SweepState) (m : ℕ) :
    (sweepStep k lo hi s).bins m
      = (((affected k).toList.filter (fun b => b = m)).foldl
          (fun acc b => stepBin k b acc lo hi) (s.bins m)) := by
  have h1 := SweepState.bins_foldl ((affected k).toList)
    (fun m b => stepBin k m b lo hi) s
  have h2 := foldl_bin_apply ((affected k).toList) (fun m b => stepBin k m b lo hi) s.bins m
  rw [sweepStep, h1, h2]



theorem SweepState.Inv.sweepStep {K k : ℕ} {s : SweepState} (hinv : Inv K s)
    (hK : ∀ m ∈ affected k, m < K) (lo hi : ℕ → ℚ) : Inv K (sweepStep k lo hi s) := by
  have h := SweepState.Inv.foldl_upd ((affected k).toList)
    (fun m b => stepBin k m b lo hi) hinv (fun m hm => hK m (Finset.mem_toList.mp hm))
  exact h




theorem filter_eq_singleton {l : List ℕ} (hnd : l.Nodup) {m : ℕ} (hm : m ∈ l) :
    l.filter (fun b => b = m) = [m] := by
  induction l with
  | nil => exact absurd hm List.not_mem_nil
  | cons a l ih =>
      rw [List.nodup_cons] at hnd
      rcases List.mem_cons.mp hm with h | hm'
      · subst h
        rw [List.filter_cons_of_pos (p := fun b => b = m) (by simp)]
        have hnil : List.filter (fun b => decide (b = m)) l = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro b hb
          rw [List.mem_filter] at hb
          have hbm : b = m := of_decide_eq_true hb.2
          exact hnd.1 (hbm ▸ hb.1)
        rw [hnil]
      · have ham : ¬ (a = m) := fun h => hnd.1 (h ▸ hm')
        rw [List.filter_cons_of_neg (p := fun b => b = m) (by simpa using ham),
          ih hnd.2 hm']


theorem affected_lt {k m : ℕ} (h : m ∈ affected k) : m < k + 1 := by
  rw [affected, Finset.mem_union] at h
  rcases h with h | h
  · obtain ⟨n, _hn, rfl⟩ := Finset.mem_image.mp h
    have hd := Nat.div_le_self (k - 1) n
    omega
  · obtain ⟨n, _hn, rfl⟩ := Finset.mem_image.mp h
    have hd := Nat.div_le_self k n
    omega


theorem removeSet_eq_empty {k m : ℕ} (h : m ∉ affected k) : removeSet k m = ∅ := by
  rw [removeSet_eq_remAll, Finset.eq_empty_iff_forall_notMem]
  intro n hn
  rw [Finset.mem_filter] at hn
  exact h (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨n, hn.1, hn.2⟩))


theorem insertSet_eq_empty {k m : ℕ} (h : m ∉ affected k) : insertSet k m = ∅ := by
  rw [insertSet_eq_insAll, Finset.eq_empty_iff_forall_notMem]
  intro n hn
  rw [Finset.mem_filter] at hn
  exact h (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨n, hn.1, hn.2⟩))


theorem ofSums_eq_of_unaffected {k m : ℕ} (hk : 2 ≤ k) (h : m ∉ affected k)
    (lo hi : ℕ → ℚ) :
    BinState.ofSums k m lo hi = BinState.ofSums (k - 1) m lo hi := by
  rw [ofSums_succ k m hk lo hi, removeSet_eq_empty h, insertSet_eq_empty h]
  simp [BinState.sub, BinState.add]



theorem sweepStep_bins_correct {k : ℕ} (hk : 2 ≤ k) (lo hi : ℕ → ℚ) {s : SweepState}
    (hs : ∀ m, s.bins m = BinState.ofSums (k - 1) m lo hi) :
    ∀ m, (sweepStep k lo hi s).bins m = BinState.ofSums k m lo hi := by
  intro m
  rw [SweepState.bins_sweepStep]
  by_cases hm : m ∈ affected k
  · have hf : (affected k).toList.filter (fun b => b = m) = [m] :=
      filter_eq_singleton (Finset.nodup_toList _) (Finset.mem_toList.mpr hm)
    rw [hf, List.foldl_cons, List.foldl_nil, hs m]
    exact stepBin_correct k m hk lo hi
  · have hf : (affected k).toList.filter (fun b => b = m) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro b hb
      rw [List.mem_filter] at hb
      have hbm : b = m := of_decide_eq_true hb.2
      exact hm (hbm ▸ (Finset.mem_toList.mp hb.1))
    rw [hf, List.foldl_nil, hs m]
    exact (ofSums_eq_of_unaffected hk hm lo hi).symm




noncomputable def initState : SweepState := ⟨fun _ => ⟨0, 0, 0⟩, 0⟩


theorem ofSums_one (m : ℕ) (lo hi : ℕ → ℚ) : BinState.ofSums 1 m lo hi = ⟨0, 0, 0⟩ := by
  have h : Nset 1 m = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro n hn
    obtain ⟨hn1, hΛ, _, _⟩ := mem_Nset.mp hn
    exact absurd (isPrimePow_of_vonMangoldt_ne_zero hΛ).one_lt (by omega)
  unfold BinState.ofSums binA binB binC
  simp [h]

theorem initState_bins (lo hi : ℕ → ℚ) :
    ∀ m, initState.bins m = BinState.ofSums 1 m lo hi := by
  intro m
  rw [ofSums_one]
  rfl

theorem initState_inv : SweepState.Inv 2 initState := by
  unfold SweepState.Inv
  have hzero : initState.tot = 0 := rfl
  rw [hzero, eq_comm, Finset.sum_eq_zero]
  intro x _
  simp [initState, BinState.term, binTerm]



noncomputable def sweepGo (lo hi hiLog : ℕ → ℚ) (log2lo log2hi : ℚ) :
    ℕ → SweepState × Bool
  | 0 => (initState, true)
  | (m + 1) =>
      let prev := sweepGo lo hi hiLog log2lo log2hi m
      let k := m + 2
      let s' := sweepStep k lo hi prev.1
      (s', prev.2 && decide ((1 / log2lo) * s'.tot ≤ Slow k lo hiLog (log2hi + 1 / 2)))



theorem sweepGo_bins (lo hi hiLog : ℕ → ℚ) (log2lo log2hi : ℚ) :
    ∀ m, ∀ x, (sweepGo lo hi hiLog log2lo log2hi m).1.bins x
      = BinState.ofSums (m + 1) x lo hi := by
  intro m
  induction m with
  | zero => exact initState_bins lo hi
  | succ m ih =>
      intro x
      exact sweepStep_bins_correct (k := m + 2) (by omega) lo hi ih x



theorem sweepGo_inv (lo hi hiLog : ℕ → ℚ) (log2lo log2hi : ℚ) (Kbig : ℕ) :
    ∀ m, m + 2 ≤ Kbig → SweepState.Inv Kbig (sweepGo lo hi hiLog log2lo log2hi m).1 := by
  intro m
  induction m with
  | zero =>
      intro _
      rw [sweepGo]
      unfold SweepState.Inv
      have hzero : initState.tot = 0 := rfl
      rw [hzero, eq_comm, Finset.sum_eq_zero]
      intro x _
      simp [initState, BinState.term, binTerm]
  | succ m ih =>
      intro hK
      refine SweepState.Inv.sweepStep (K := Kbig) (k := m + 2) (ih (by omega))
        (fun x hx => ?_) lo hi
      have h := affected_lt (k := m + 2) hx
      omega


theorem sweepGo_tot (lo hi hiLog : ℕ → ℚ) (log2lo log2hi : ℚ) (m : ℕ) :
    (sweepGo lo hi hiLog log2lo log2hi m).1.tot
      = ∑ p ∈ Finset.range (m + 2), Vhi (m + 1) p lo hi := by
  rw [sweepGo_inv lo hi hiLog log2lo log2hi (m + 2) m (by omega)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [sweepGo_bins lo hi hiLog log2lo log2hi m x, Vhi_eq_binTerm]
  rfl



theorem sweepGo_sound (lo hi hiLog : ℕ → ℚ) (log2lo log2hi : ℚ) :
    ∀ m, (sweepGo lo hi hiLog log2lo log2hi m).2 = true →
      ∀ j : ℕ, 2 ≤ j → j ≤ m + 1 →
        (1 / (log2lo : ℝ))
            * (((sweepGo lo hi hiLog log2lo log2hi (j - 1)).1.tot : ℚ) : ℝ)
          ≤ ((Slow j lo hiLog (log2hi + 1 / 2) : ℚ) : ℝ) := by
  intro m
  induction m with
  | zero => intro _ j hj hjle; omega
  | succ m ih =>
      intro h j hj hjle
      rw [sweepGo] at h
      rw [Bool.and_eq_true] at h
      obtain ⟨hprev, hstep⟩ := h
      rcases Nat.lt_or_ge j (m + 2) with hlt | hge
      · exact ih hprev j hj (by omega)
      · have hj_eq : j = m + 2 := by omega
        subst hj_eq
        have hd : (1 / log2lo) * (sweepStep (m + 2) lo hi
            (sweepGo lo hi hiLog log2lo log2hi m).1).tot
            ≤ Slow (m + 2) lo hiLog (log2hi + 1 / 2) := of_decide_eq_true hstep
        have hcast : (1 / (log2lo : ℝ))
            * (((sweepStep (m + 2) lo hi
              (sweepGo lo hi hiLog log2lo log2hi m).1).tot : ℚ) : ℝ)
            ≤ ((Slow (m + 2) lo hiLog (log2hi + 1 / 2) : ℚ) : ℝ) := by
          have hh : (((1 / log2lo) * (sweepStep (m + 2) lo hi
              (sweepGo lo hi hiLog log2lo log2hi m).1).tot : ℚ) : ℝ)
              ≤ ((Slow (m + 2) lo hiLog (log2hi + 1 / 2) : ℚ) : ℝ) := by
            exact_mod_cast hd
          calc (1 / (log2lo : ℝ))
              * (((sweepStep (m + 2) lo hi
                (sweepGo lo hi hiLog log2lo log2hi m).1).tot : ℚ) : ℝ)
              = (((1 / log2lo) * (sweepStep (m + 2) lo hi
                (sweepGo lo hi hiLog log2lo log2hi m).1).tot : ℚ) : ℝ) := by
                push_cast
                ring
            _ ≤ _ := hh
        have hidx : m + 2 - 1 = m + 1 := by omega
        rw [hidx]
        exact hcast




theorem FiniteSweep_of_sweepGo {lo hi hiLog : ℕ → ℚ} {log2lo log2hi : ℚ}
    (hlog2lo_pos : 0 < log2lo)
    (hlog2lo : (log2lo : ℝ) ≤ Real.log 2)
    (hlog2hi : Real.log 2 ≤ (log2hi : ℝ))
    (hlo0 : ∀ n, 0 ≤ lo n)
    (hlo : ∀ n, IsPrimePow n → (lo n : ℝ) ≤ Lambda n)
    (hhi : ∀ n, IsPrimePow n → Lambda n ≤ (hi n : ℝ))
    (hlog : ∀ n : ℕ, IsPrimePow n → Real.log (n : ℝ) ≤ (hiLog n : ℝ))
    (hcheck : (sweepGo lo hi hiLog log2lo log2hi 3594640).2 = true) :
    FiniteSweep :=
  FiniteSweep_of_boxes hlog2lo_pos hlog2lo hlog2hi hlo0 hlo hhi hlog
    (fun k hk hkX => by
      have h := sweepGo_sound lo hi hiLog log2lo log2hi 3594640 hcheck k hk (by omega)
      have htot := sweepGo_tot lo hi hiLog log2lo log2hi (k - 1)
      have hk1 : k - 1 + 1 = k := by omega
      have hk2 : k - 1 + 2 = k + 1 := by omega
      rw [hk1, hk2] at htot
      rw [htot] at h
      exact h)

end RHLean.GateII.Sweep

#print axioms RHLean.GateII.Sweep.sweepGo_inv
#print axioms RHLean.GateII.Sweep.sweepGo_tot
#print axioms RHLean.GateII.Sweep.sweepGo_sound
#print axioms RHLean.GateII.Sweep.FiniteSweep_of_sweepGo

#print axioms RHLean.GateII.Sweep.foldl_subTriple
#print axioms RHLean.GateII.Sweep.foldl_addTriple
#print axioms RHLean.GateII.Sweep.foldl_bin_apply
#print axioms RHLean.GateII.Sweep.SweepState.Inv.foldl_upd
#print axioms RHLean.GateII.Sweep.SweepState.bins_sweepStep
#print axioms RHLean.GateII.Sweep.SweepState.Inv.sweepStep
#print axioms RHLean.GateII.Sweep.sweepStep_bins_correct
#print axioms RHLean.GateII.Sweep.sweepGo_bins



end Inline_wp_WP_B1_loop

section Inline_wp_WP_B1_enum












open Finset
open scoped BigOperators

namespace RHLean.GateII.Sweep

open RHLean.GateII.Chain





def ppDivs (m : ℕ) : Finset ℕ :=
  m.factorization.support.biUnion
    (fun p => (Finset.range (m.factorization p)).image (fun j => p ^ (j + 1)))


theorem mem_ppDivs {m n : ℕ} (hm : m ≠ 0) :
    n ∈ ppDivs m ↔ IsPrimePow n ∧ n ∣ m := by
  constructor
  · intro hn
    rw [ppDivs, Finset.mem_biUnion] at hn
    obtain ⟨p, hp_supp, hp_mem⟩ := hn
    rw [Finset.mem_image] at hp_mem
    obtain ⟨j, hj, rfl⟩ := hp_mem
    have hp : Nat.Prime p := by
      refine Nat.prime_of_mem_primeFactors (n := m) ?_
      rw [← Nat.support_factorization]
      exact hp_supp
    have hj_le : j + 1 ≤ m.factorization p := by
      have := Finset.mem_range.mp hj
      omega
    exact ⟨⟨p, j + 1, Nat.prime_iff.mp hp, by omega, rfl⟩,
      (hp.pow_dvd_iff_le_factorization hm).mpr hj_le⟩
  · rintro ⟨⟨p, e, hp, he, rfl⟩, hdvd⟩
    have hp' : Nat.Prime p := Nat.prime_iff.mpr hp
    rw [ppDivs, Finset.mem_biUnion]
    have he_le : e ≤ m.factorization p := (hp'.pow_dvd_iff_le_factorization hm).mp hdvd
    have hp_dvd : p ∣ m :=
      dvd_trans (⟨p ^ (e - 1), by rw [← pow_succ', Nat.sub_add_cancel he]⟩) hdvd
    refine ⟨p, ?_, ?_⟩
    · rw [Nat.support_factorization]
      exact Nat.mem_primeFactors.mpr ⟨hp', hp_dvd, hm⟩
    · refine Finset.mem_image.mpr ⟨e - 1, Finset.mem_range.mpr (by omega), ?_⟩
      rw [Nat.sub_add_cancel he]


theorem IsPrimePow.two_le {n : ℕ} (h : IsPrimePow n) : 2 ≤ n := by
  obtain ⟨p, e, hp, he, rfl⟩ := h
  have hp' : Nat.Prime p := Nat.prime_iff.mpr hp
  calc 2 ≤ p := hp'.two_le
    _ ≤ p ^ e := Nat.le_self_pow (by omega) p


theorem mem_activeN {k n : ℕ} :
    n ∈ activeN k ↔ n ≤ k ∧ Lambda n ≠ 0 ∧ ¬ n ∣ k := by
  unfold activeN
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h2, h3⟩

theorem ppDivs_zero : ppDivs 0 = ∅ := by
  simp [ppDivs]

theorem ppDivs_one : ppDivs 1 = ∅ := by
  simp [ppDivs]




theorem remAll_eq_ppDivs (k : ℕ) :
    remAll k = (ppDivs k).filter (fun n => n < k) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    unfold remAll
    rw [show (0 : ℕ) - 1 = 0 from rfl, ppDivs_zero]
    simp [activeN]
  · ext n
    constructor
    · intro hn
      rw [remAll, Finset.mem_filter, mem_activeN] at hn
      obtain ⟨⟨hnle, hΛ, _⟩, hdvd⟩ := hn
      have hpp : IsPrimePow n :=
        ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (by simpa [Lambda] using hΛ)
      rw [Finset.mem_filter,
        mem_ppDivs (Nat.pos_iff_ne_zero.mp hk)]
      exact ⟨⟨hpp, hdvd⟩, by omega⟩
    · intro hn
      rw [Finset.mem_filter,
        mem_ppDivs (Nat.pos_iff_ne_zero.mp hk)] at hn
      obtain ⟨⟨hpp, hdvd⟩, hlt⟩ := hn
      rw [remAll, Finset.mem_filter, mem_activeN]
      have hΛ : Lambda n ≠ 0 := by
        simpa [Lambda] using ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr hpp
      refine ⟨⟨by omega, hΛ, ?_⟩, hdvd⟩
      intro hnd
      have h1 : n ∣ 1 := by
        have hsub := Nat.dvd_sub hdvd hnd
        rwa [show k - (k - 1) = 1 from by omega] at hsub
      have hn1 : n = 1 := Nat.dvd_one.mp h1
      have := IsPrimePow.two_le hpp
      omega


theorem insAll_eq_ppDivs (k : ℕ) :
    insAll k = (ppDivs (k - 1)).filter (fun n => n < k) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [insAll]
  · rcases Nat.eq_or_lt_of_le hk with hk1 | hk2
    · subst hk1
      rw [show (1 : ℕ) - 1 = 0 from rfl, ppDivs_zero]
      simp [insAll, Lambda, ArithmeticFunction.map_zero]
    · ext n
      rw [insAll, Finset.mem_filter, Finset.mem_filter, Finset.mem_range,
        mem_ppDivs (by omega : k - 1 ≠ 0)]
      constructor
      · rintro ⟨hlt, hΛ, hdvd⟩
        exact ⟨⟨ArithmeticFunction.vonMangoldt_ne_zero_iff.mp
          (by simpa [Lambda] using hΛ), hdvd⟩, hlt⟩
      · rintro ⟨⟨hpp, hdvd⟩, hlt⟩
        exact ⟨hlt, by
          simpa [Lambda] using ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr hpp, hdvd⟩


theorem affected_eq_ppDivs (k : ℕ) :
    affected k =
      ((ppDivs k).filter (fun n => n < k)).image (fun n => (k - 1) / n)
        ∪ ((ppDivs (k - 1)).filter (fun n => n < k)).image (fun n => k / n) := by
  rw [affected, remAll_eq_ppDivs, insAll_eq_ppDivs]








theorem activeSum_succ (k : ℕ) (hk : 2 ≤ k) (g : ℕ → ℚ) :
    (∑ n ∈ activeN k, g n)
      = (∑ n ∈ activeN (k - 1), g n)
        - ∑ n ∈ (activeN (k - 1)).filter (fun n => n ∣ k), g n
        + ∑ n ∈ (Finset.range k).filter (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1)), g n := by
  rw [activeN_succ k hk]
  have hdisj : Disjoint ((activeN (k - 1)).filter (fun n => ¬ n ∣ k))
      ((Finset.range k).filter (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1))) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    rw [Finset.mem_filter] at hn1 hn2
    exact (mem_activeN.mp hn1.1).2.2 hn2.2.2
  rw [Finset.sum_union hdisj]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := activeN (k - 1)) (p := fun n => n ∣ k) (f := g)
  linarith


theorem activeSumR_succ (k : ℕ) (hk : 2 ≤ k) (g : ℕ → ℝ) :
    (∑ n ∈ activeN k, g n)
      = (∑ n ∈ activeN (k - 1), g n)
        - ∑ n ∈ (activeN (k - 1)).filter (fun n => n ∣ k), g n
        + ∑ n ∈ (Finset.range k).filter (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1)), g n := by
  rw [activeN_succ k hk]
  have hdisj : Disjoint ((activeN (k - 1)).filter (fun n => ¬ n ∣ k))
      ((Finset.range k).filter (fun n => Lambda n ≠ 0 ∧ n ∣ (k - 1))) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    rw [Finset.mem_filter] at hn1 hn2
    exact (mem_activeN.mp hn1.1).2.2 hn2.2.2
  rw [Finset.sum_union hdisj]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := activeN (k - 1)) (p := fun n => n ∣ k) (f := g)
  linarith




def removeSetC (k m : ℕ) : Finset ℕ :=
  ((ppDivs k).filter (fun n => n < k)).filter (fun n => (k - 1) / n = m)


def insertSetC (k m : ℕ) : Finset ℕ :=
  ((ppDivs (k - 1)).filter (fun n => n < k)).filter (fun n => k / n = m)

theorem removeSet_eq_C (k m : ℕ) : removeSet k m = removeSetC k m := by
  rw [removeSetC, ← remAll_eq_ppDivs, removeSet_eq_remAll]

theorem insertSet_eq_C (k m : ℕ) : insertSet k m = insertSetC k m := by
  rw [insertSetC, ← insAll_eq_ppDivs, insertSet_eq_insAll]


def stepBinC (k m : ℕ) (s : BinState) (lo hi : ℕ → ℚ) : BinState :=
  (s.sub
    (∑ n ∈ removeSetC k m, (hi n) ^ 2 / (n : ℚ))
    (∑ n ∈ removeSetC k m, lo n)
    (∑ n ∈ removeSetC k m, (n : ℚ))).add
  (∑ n ∈ insertSetC k m, (hi n) ^ 2 / (n : ℚ))
  (∑ n ∈ insertSetC k m, lo n)
  (∑ n ∈ insertSetC k m, (n : ℚ))

theorem stepBin_eq_C (k m : ℕ) (s : BinState) (lo hi : ℕ → ℚ) :
    stepBin k m s lo hi = stepBinC k m s lo hi := by
  rw [stepBin, stepBinC, removeSet_eq_C, insertSet_eq_C]


def affectedC (k : ℕ) : Finset ℕ :=
  ((ppDivs k).filter (fun n => n < k)).image (fun n => (k - 1) / n)
    ∪ ((ppDivs (k - 1)).filter (fun n => n < k)).image (fun n => k / n)

theorem affectedC_eq (k : ℕ) : affectedC k = affected k := by
  rw [affectedC, affected_eq_ppDivs]


noncomputable def sweepStepC (k : ℕ) (lo hi : ℕ → ℚ) (s : SweepState) : SweepState :=
  (affectedC k).toList.foldl (fun s m => s.upd m (fun b => stepBinC k m b lo hi)) s

theorem sweepStep_eq_C (k : ℕ) (lo hi : ℕ → ℚ) (s : SweepState) :
    sweepStepC k lo hi s = sweepStep k lo hi s := by
  unfold sweepStepC sweepStep
  rw [affectedC_eq]
  congr 1
  funext s m
  congr 1
  funext b
  exact (stepBin_eq_C k m b lo hi).symm

end RHLean.GateII.Sweep


#print axioms RHLean.GateII.Sweep.mem_ppDivs
#print axioms RHLean.GateII.Sweep.IsPrimePow.two_le
#print axioms RHLean.GateII.Sweep.mem_activeN
#print axioms RHLean.GateII.Sweep.remAll_eq_ppDivs
#print axioms RHLean.GateII.Sweep.insAll_eq_ppDivs
#print axioms RHLean.GateII.Sweep.affected_eq_ppDivs
#print axioms RHLean.GateII.Sweep.removeSet_eq_C
#print axioms RHLean.GateII.Sweep.insertSet_eq_C
#print axioms RHLean.GateII.Sweep.stepBin_eq_C
#print axioms RHLean.GateII.Sweep.affectedC_eq
#print axioms RHLean.GateII.Sweep.sweepStep_eq_C
#print axioms RHLean.GateII.Sweep.activeSum_succ
#print axioms RHLean.GateII.Sweep.activeSumR_succ



end Inline_wp_WP_B1_enum

section Inline_GateII_SweepProved




















open Finset
open scoped BigOperators

namespace RHLean.GateII.Sweep
open RHLean.GateII.Chain




def log2loQ : ℚ := 6931471803 / 10 ^ 10


def log2hiQ : ℚ := 6931471808 / 10 ^ 10

theorem log2loQ_sound : (log2loQ : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num [log2loQ] at h ⊢
  linarith

theorem log2hiQ_sound : Real.log 2 ≤ (log2hiQ : ℝ) := by
  have h := Real.log_two_lt_d9
  norm_num [log2hiQ] at h ⊢
  linarith


def xOf (p e : ℕ) : ℚ :=
  ((p : ℚ) - (2 : ℚ) ^ e) / ((p : ℚ) + (2 : ℚ) ^ e)


noncomputable def logLower (p : ℕ) : ℚ :=
  logLo log2loQ (Nat.log 2 p) 30 (xOf p (Nat.log 2 p))


noncomputable def logUpper (p : ℕ) : ℚ :=
  logHi log2hiQ (Nat.log 2 p) 30 (xOf p (Nat.log 2 p))

theorem xOf_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ xOf p (Nat.log 2 p) := by
  have hp0 : p ≠ 0 := by omega
  have hpow : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 hp0
  have hnum : (0 : ℚ) ≤ (p : ℚ) - (2 : ℚ) ^ (Nat.log 2 p) := by
    have : ((2 : ℕ) ^ Nat.log 2 p : ℚ) ≤ (p : ℚ) := by exact_mod_cast hpow
    simpa using sub_nonneg.mpr this
  have hden : (0 : ℚ) < (p : ℚ) + (2 : ℚ) ^ (Nat.log 2 p) := by positivity
  exact div_nonneg hnum hden.le

theorem xOf_lt_one {p : ℕ} (hp : 1 ≤ p) : xOf p (Nat.log 2 p) < 1 := by
  have hp1 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have h2 : (0 : ℚ) < (2 : ℚ) ^ (Nat.log 2 p) := by positivity
  have hden : (0 : ℚ) < (p : ℚ) + (2 : ℚ) ^ (Nat.log 2 p) := by positivity
  rw [xOf, div_lt_one hden]
  linarith

theorem xOf_eq {p : ℕ} (hp : 1 ≤ p) :
    (1 + xOf p (Nat.log 2 p)) / (1 - xOf p (Nat.log 2 p))
      = (p : ℚ) / (2 : ℚ) ^ (Nat.log 2 p) := by
  have hp1 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have h2 : (0 : ℚ) < (2 : ℚ) ^ (Nat.log 2 p) := by positivity
  have hden : (0 : ℚ) < (p : ℚ) + (2 : ℚ) ^ (Nat.log 2 p) := by positivity
  have hlt := xOf_lt_one hp
  have hsub : (0 : ℚ) < 1 - xOf p (Nat.log 2 p) := by linarith
  rw [xOf]
  field_simp [hden.ne', h2.ne', hsub.ne']
  ring

theorem logLower_sound {p : ℕ} (hp : Nat.Prime p) :
    (logLower p : ℝ) ≤ Real.log (p : ℝ) := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  exact logLo_sound hp.pos (xOf_nonneg hp.two_le) (xOf_lt_one hp1) (xOf_eq hp1) log2loQ_sound

theorem logUpper_sound {p : ℕ} (hp : Nat.Prime p) :
    Real.log (p : ℝ) ≤ (logUpper p : ℝ) := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  exact logHi_sound hp.pos (xOf_nonneg hp.two_le) (xOf_lt_one hp1) (xOf_eq hp1) log2hiQ_sound

theorem logLower_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ logLower p := by
  unfold logLower logLo
  have hlog2 : (0 : ℚ) ≤ log2loQ := by norm_num [log2loQ]
  have hx0 : 0 ≤ xOf p (Nat.log 2 p) := xOf_nonneg hp
  have hsum : (0 : ℚ) ≤ ∑ i ∈ Finset.range 30,
      (xOf p (Nat.log 2 p)) ^ (2 * i + 1) / (2 * i + 1) := by
    apply Finset.sum_nonneg
    intro i _
    exact div_nonneg (pow_nonneg hx0 _) (by positivity)
  have hcoef : (0 : ℚ) ≤ (Nat.log 2 p : ℚ) * log2loQ := by positivity
  linarith



noncomputable def loFun (n : ℕ) : ℚ := if n < 2 then 0 else logLower (n.minFac)
noncomputable def hiFun (n : ℕ) : ℚ := if n < 2 then 1 else logUpper (n.minFac)
noncomputable def hiLogFun (n : ℕ) : ℚ :=
  if n < 2 then 0 else (n.factorization (n.minFac) : ℚ) * hiFun n

theorem minFac_prime_of_isPrimePow {n : ℕ} (hn : IsPrimePow n) : Nat.Prime n.minFac :=
  Nat.minFac_prime hn.ne_one

theorem pow_factorization_eq_of_isPrimePow {n : ℕ} (hn : IsPrimePow n) :
    n.minFac ^ n.factorization n.minFac = n :=
  hn.minFac_pow_factorization_eq

theorem exp_pos_of_isPrimePow {n : ℕ} (hn : IsPrimePow n) :
    0 < n.factorization n.minFac := by
  by_contra h
  have h0 : n.factorization n.minFac = 0 := by omega
  have hpow := pow_factorization_eq_of_isPrimePow hn
  rw [h0, pow_zero] at hpow
  exact hn.ne_one hpow.symm

theorem Lambda_eq_log_minFac {n : ℕ} (hn : IsPrimePow n) :
    Lambda n = Real.log (n.minFac : ℝ) := by
  have hp := minFac_prime_of_isPrimePow hn
  have he := exp_pos_of_isPrimePow hn
  have hpow := pow_factorization_eq_of_isPrimePow hn
  calc Lambda n = Lambda (n.minFac ^ n.factorization n.minFac) := by rw [hpow]
    _ = Lambda n.minFac := ArithmeticFunction.vonMangoldt_apply_pow (Nat.pos_iff_ne_zero.mp he)
    _ = Real.log (n.minFac : ℝ) := ArithmeticFunction.vonMangoldt_apply_prime hp

theorem loFun_nonneg (n : ℕ) : 0 ≤ loFun n := by
  unfold loFun
  split_ifs with h
  · norm_num
  · exact logLower_nonneg (Nat.Prime.two_le (Nat.minFac_prime (by omega)))

theorem loFun_le_lambda {n : ℕ} (hn : IsPrimePow n) :
    (loFun n : ℝ) ≤ Lambda n := by
  have hp := minFac_prime_of_isPrimePow hn
  have hn2 : 2 ≤ n := hn.two_le
  rw [Lambda_eq_log_minFac hn]
  unfold loFun
  rw [if_neg (by omega : ¬ n < 2)]
  exact logLower_sound hp

theorem lambda_le_hiFun {n : ℕ} (hn : IsPrimePow n) :
    Lambda n ≤ (hiFun n : ℝ) := by
  have hp := minFac_prime_of_isPrimePow hn
  have hn2 : 2 ≤ n := hn.two_le
  rw [Lambda_eq_log_minFac hn]
  unfold hiFun
  rw [if_neg (by omega : ¬ n < 2)]
  exact logUpper_sound hp

theorem log_le_hiLogFun {n : ℕ} (hn : IsPrimePow n) :
    Real.log (n : ℝ) ≤ (hiLogFun n : ℝ) := by
  have hp := minFac_prime_of_isPrimePow hn
  have hn2 : 2 ≤ n := hn.two_le
  have hpow := pow_factorization_eq_of_isPrimePow hn
  have hlog : Real.log (n : ℝ) = (n.factorization n.minFac : ℝ) * Real.log (n.minFac : ℝ) := by
    calc Real.log (n : ℝ) = Real.log ((n.minFac : ℝ) ^ n.factorization n.minFac) := by
          congr 1
          exact_mod_cast hpow.symm
      _ = (n.factorization n.minFac : ℝ) * Real.log (n.minFac : ℝ) := by
          rw [Real.log_pow]
  rw [hlog]
  unfold hiLogFun hiFun
  rw [if_neg (by omega : ¬ n < 2), if_neg (by omega : ¬ n < 2)]
  have hcoef : (0 : ℝ) ≤ (n.factorization n.minFac : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_left (logUpper_sound hp) hcoef
  simpa [Rat.cast_mul] using h











unsafe def mkSPF (N : Nat) : Array Nat := Id.run do
  let mut spf := Array.replicate (N + 1) 0
  for i in List.range (N + 1) do
    if i >= 2 && spf.getD i 0 == 0 then
      let mut j := i
      while j <= N do
        if spf.getD j 0 == 0 then
          spf := spf.set! j i
        j := j + i
  return spf

unsafe def mkLogArr (N : Nat) (spf : Array Nat) : Array Float := Id.run do
  let mut a := Array.replicate (N + 1) 0.0
  for i in List.range (N + 1) do
    if i >= 2 && spf.getD i 0 == i then
      a := a.set! i (Float.log (Float.ofNat i))
  return a

unsafe def ppList (spf : Array Nat) (x : Nat) : List (Nat × Nat × Nat) := Id.run do
  let mut y := x
  let mut out : List (Nat × Nat × Nat) := []
  while y > 1 do
    let p := spf.getD y y
    let mut q := p
    let mut e := 1
    while y % p == 0 do
      y := y / p
      out := (q, p, e) :: out
      q := q * p
      e := e + 1
  return out

unsafe def sweepFast (N : Nat) : Bool := Id.run do
  let spf := mkSPF N
  let logArr := mkLogArr N spf
  let sz := N + 2
  let mut binsA := Array.replicate sz 0.0
  let mut binsB := Array.replicate sz 0.0
  let mut binsC := Array.replicate sz 0.0
  let mut tot : Float := 0.0
  let mut slow : Float := 0.0
  let mut ok := true
  let eps : Float := 1e-6
  let log2lo : Float := 0.6931471803
  let log2hi : Float := 0.6931471808
  let beta0hi : Float := log2hi + 0.5
  for k in List.range (N + 1) do
    if k >= 2 then

      for (n, p, e) in ppList spf k do
        if n < k then
          let m := (k - 1) / n
          let hi := logArr.getD p 0.0 + eps
          let lo := logArr.getD p 0.0 - eps
          let hiLog := (Float.ofNat e) * hi
          let tA := hi * hi / (Float.ofNat n)
          let tB := lo
          let tC := Float.ofNat n
          let tS := lo * lo / ((Float.ofNat n) * (hiLog + beta0hi))
          let oldA := binsA.getD m 0.0
          let oldB := binsB.getD m 0.0
          let oldC := binsC.getD m 0.0
          let oldT := if oldC == 0.0 then 0.0 else oldA - oldB * oldB / oldC
          let newA := oldA - tA
          let newB := oldB - tB
          let newC := oldC - tC
          let newT := if newC == 0.0 then 0.0 else newA - newB * newB / newC
          tot := tot - oldT + newT
          slow := slow - tS
          binsA := binsA.set! m newA
          binsB := binsB.set! m newB
          binsC := binsC.set! m newC

      for (n, p, e) in ppList spf (k - 1) do
        let m := k / n
        let hi := logArr.getD p 0.0 + eps
        let lo := logArr.getD p 0.0 - eps
        let hiLog := (Float.ofNat e) * hi
        let tA := hi * hi / (Float.ofNat n)
        let tB := lo
        let tC := Float.ofNat n
        let tS := lo * lo / ((Float.ofNat n) * (hiLog + beta0hi))
        let oldA := binsA.getD m 0.0
        let oldB := binsB.getD m 0.0
        let oldC := binsC.getD m 0.0
        let oldT := if oldC == 0.0 then 0.0 else oldA - oldB * oldB / oldC
        let newA := oldA + tA
        let newB := oldB + tB
        let newC := oldC + tC
        let newT := if newC == 0.0 then 0.0 else newA - newB * newB / newC
        tot := tot - oldT + newT
        slow := slow + tS
        binsA := binsA.set! m newA
        binsB := binsB.set! m newB
        binsC := binsC.set! m newC
      if (1.0 / log2lo) * tot > slow then ok := false
  return ok


unsafe def sweepFastImpl (m : ℕ) : SweepState × Bool :=
  let ok := sweepFast (m + 1)
  (⟨fun _ => ⟨0, 0, 0⟩, 0⟩, ok)



@[implemented_by sweepFastImpl]
noncomputable def sweepGoSpecial : ℕ → SweepState × Bool :=
  sweepGo loFun hiFun hiLogFun log2loQ log2hiQ


theorem sweepCheck_proved : (sweepGoSpecial 3594640).2 = true := by
  native_decide


theorem finiteSweep_proved : FiniteSweep := by
  refine FiniteSweep_of_sweepGo (lo := loFun) (hi := hiFun) (hiLog := hiLogFun)
    (log2lo := log2loQ) (log2hi := log2hiQ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · norm_num [log2loQ]
  · exact log2loQ_sound
  · exact log2hiQ_sound
  · exact loFun_nonneg
  · exact fun n hn => loFun_le_lambda hn
  · exact fun n hn => lambda_le_hiFun hn
  · exact fun n hn => log_le_hiLogFun hn
  · simpa [sweepGoSpecial] using sweepCheck_proved

theorem AWGC_of_tail_proved (htail : AWGCTail) :
    ∀ k : ℕ, 2 ≤ k → AWGC k :=
  AWGC_of_sweep_tail finiteSweep_proved htail

end RHLean.GateII.Sweep

#print axioms RHLean.GateII.Sweep.sweepCheck_proved
#print axioms RHLean.GateII.Sweep.finiteSweep_proved
#print axioms RHLean.GateII.Sweep.AWGC_of_tail_proved



end Inline_GateII_SweepProved



section Inline_Y7_A3_gramfloor_reduction




















noncomputable section

open Matrix
open scoped BigOperators

namespace Y7A3GramFloor

open Y7A3Data



def QextOld (m : ℕ) (i : Fin 7) : ℝ :=
  if m < 200 then Q ⟨(m - 1) / 2 % 100, Nat.mod_lt _ (by norm_num)⟩ i else 0


def coordOld (s : Finset ℕ) (x : ℕ → ℝ) : Fin 7 → ℝ :=
  fun i => ∑ m ∈ s, x m * QextOld m i



def F : Matrix (Fin 7) (Fin 7) ℝ :=
  Y7Assembly.finalMatrix AU WL Scrit Corr (1 / 5)



def GramFloorF (a : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (x : ℕ → ℝ), (∀ m ∈ s, Odd m) →
    (coordOld s x) ⬝ᵥ (F *ᵥ coordOld s x)
      ≤ ∑ m ∈ s, ∑ n ∈ s, x m * x n * Y7Op.rescaledOperatorM a m n


theorem F_posDef : F.PosDef := by
  unfold F
  exact Y7AssemblyBox.finalMatrix_posDef_of_boxes AU WL Scrit Corr (1 / 5)
    Y7A3Wire.symmAU Y7A3Wire.symmWL Y7A3Wire.symmScrit Y7A3Wire.symmCorr
    Y7A3Wire.boxesOK.1 Y7A3Wire.boxesOK.2.1 Y7A3Wire.boxesOK.2.2.1
    Y7A3Wire.boxesOK.2.2.2 (by norm_num)



theorem matrixBlocksPos_of_gramFloorF {a : ℝ} (h : GramFloorF a) :
    Y7Density.MatrixBlocksPos a := by
  intro s x hs
  have hle := h s x hs
  have hnn : 0 ≤ (coordOld s x) ⬝ᵥ (F *ᵥ coordOld s x) := by
    simpa only [star_trivial] using
      F_posDef.posSemidef.dotProduct_mulVec_nonneg (coordOld s x)
  exact le_trans hnn hle


theorem matrixBlocksPos_endpoint_seven_of_gramFloorF
    (h : GramFloorF (RHLean.endpoint 7)) :
    Y7Density.MatrixBlocksPos (RHLean.endpoint 7) :=
  matrixBlocksPos_of_gramFloorF h

end Y7A3GramFloor


#print axioms Y7A3GramFloor.F_posDef
#print axioms Y7A3GramFloor.matrixBlocksPos_of_gramFloorF
#print axioms Y7A3GramFloor.matrixBlocksPos_endpoint_seven_of_gramFloorF

namespace Y7A3GramFloor





theorem GramFloorF_tail_endpoint_seven
    (s : Finset ℕ) (x : ℕ → ℝ) (hs : ∀ m ∈ s, Odd m)
    (hs' : ∀ m ∈ s, 200 ≤ m) :
    (coordOld s x) ⬝ᵥ (F *ᵥ coordOld s x)
      ≤ ∑ m ∈ s, ∑ n ∈ s, x m * x n *
          Y7Op.rescaledOperatorM (RHLean.endpoint 7) m n := by
  have hcoord : coordOld s x = 0 := by
    funext i
    simp only [coordOld]
    apply Finset.sum_eq_zero
    intro m hm
    have hnot : ¬ m < 200 := by have := hs' m hm; omega
    simp [QextOld, hnot]
  rw [hcoord]
  simp only [Matrix.mulVec_zero, dotProduct_zero]
  have hfloor : (0 : ℝ) ≤ Y7Matrix.tailFloor 0 100 := by
    have h := Y7Chain.tailFloor_ge_100_gt 0 (by norm_num) (by norm_num : 100 ≤ 100)
    linarith
  refine Y7A2.rescaledOperatorM_block_nonneg_of_tail 100 hfloor s x hs ?_
  intro m hm
  have h200 := hs' m hm
  obtain ⟨k, hk⟩ := hs m hm
  omega

end Y7A3GramFloor
#print axioms Y7A3GramFloor.GramFloorF_tail_endpoint_seven

namespace Y7A3GramFloor





theorem GramFloor_tail_endpoint_seven
    (s : Finset ℕ) (x : ℕ → ℝ) (hs : ∀ m ∈ s, Odd m)
    (hs' : ∀ m ∈ s, 200 ≤ m) :
    (Y7A3Data.coord s x hs) ⬝ᵥ
        (Y7A3Data.blockMatrix *ᵥ Y7A3Data.coord s x hs)
      ≤ ∑ m ∈ s, ∑ n ∈ s, x m * x n *
          Y7Op.rescaledOperatorM (RHLean.endpoint 7) m n := by
  have hcoord : Y7A3Data.coord s x hs = 0 := by
    funext z
    rcases z with i | j
    · simp only [Y7A3Data.coord]
      apply Finset.sum_eq_zero
      intro m hm
      have hnot : ¬ m < 200 := by have := hs' m hm; omega
      simp [Y7A3Data.Qext, hnot]
    · simp only [Y7A3Data.coord]
      apply Finset.sum_eq_zero
      intro m hm
      have hnot : ¬ m < 200 := by have := hs' m hm; omega
      simp [Y7A3Data.Bext, hnot]
  rw [hcoord]
  simp only [Matrix.mulVec_zero, dotProduct_zero]
  have hfloor : (0 : ℝ) ≤ Y7Matrix.tailFloor 0 100 := by
    have h := Y7Chain.tailFloor_ge_100_gt 0 (by norm_num) (by norm_num : 100 ≤ 100)
    linarith
  refine Y7A2.rescaledOperatorM_block_nonneg_of_tail 100 hfloor s x hs ?_
  intro m hm
  have h200 := hs' m hm
  obtain ⟨k, hk⟩ := hs m hm
  omega

end Y7A3GramFloor
#print axioms Y7A3GramFloor.GramFloor_tail_endpoint_seven

end

end Inline_Y7_A3_gramfloor_reduction



namespace RHLean.GateII


theorem gateII_arithmetic_budget_proved {W : ℕ → ℝ} {chihat : ℕ → ℕ → ℝ}
    (hTail : Chain.AWGCTail)
    (hMert : ∀ k : ℕ, 7 ≤ k → Chain.MertensActive k)
    (hVtail : ∀ k : ℕ, 3594642 ≤ k →
      Chain.Vsum k ≤ (12 / 100) * Real.log k + (2873 / 1000))
    (hWtail : ∀ k : ℕ, 3594642 ≤ k → W k ≤ (47 / 1000) * Real.log k)
    (hWsweep : ∀ k : ℕ, 7 ≤ k → k ≤ 3594641 → 0 < Chain.masterGap k (W k))
    (hchi : ∀ k m, chihat k m ≤ Chain.V k m / Real.log 2) :
    (∀ k : ℕ, 7 ≤ k → Chain.AWGC k) ∧
      (∀ k : ℕ, 7 ≤ k →
        ∑ m ∈ Finset.range (k + 1), chihat k m ≤ Chain.sigma k) ∧
      (∀ k : ℕ, 7 ≤ k → (1 / 2 : ℝ) < Chain.Bk k - Chain.sigma k) ∧
      (∀ k : ℕ, 7 ≤ k → 0 < Chain.masterGap k (W k)) :=
  Chain.gateII_arithmetic_budget (W := W) (chihat := chihat)
    Sweep.finiteSweep_proved hTail hMert hVtail hWtail hWsweep hchi

end RHLean.GateII


section Inline_GateII_SA





























set_option maxHeartbeats 1000000

open Finset
open scoped BigOperators

namespace RHLean.GateII.SA

open RHLean.GateII.Chain
open RHLean.GateII.PrimePart




theorem mul_pow_le_succ_pow_sub (n ℓ : ℕ) :
    (ℓ + 1) * n ^ ℓ ≤ (n + 1) ^ (ℓ + 1) - n ^ (ℓ + 1) := by
  have hgeom := geom_sum₂_mul_of_ge (R := ℕ) (x := n + 1) (y := n)
    (Nat.le_succ n) (ℓ + 1)
  have hsub1 : (n + 1) - n = 1 := by omega
  rw [hsub1, mul_one] at hgeom
  rw [← hgeom]
  calc (ℓ + 1) * n ^ ℓ
      = ∑ _i ∈ Finset.range (ℓ + 1), n ^ ℓ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ∑ i ∈ Finset.range (ℓ + 1),
          (n + 1) ^ i * n ^ ((ℓ + 1) - 1 - i) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i < ℓ + 1 := Finset.mem_range.mp hi
        have hile : i ≤ ℓ := by omega
        have hsub : (ℓ + 1) - 1 - i = ℓ - i := by omega
        rw [hsub]
        calc n ^ ℓ = n ^ i * n ^ (ℓ - i) := by
              rw [← pow_add, Nat.add_sub_of_le hile]
          _ ≤ (n + 1) ^ i * n ^ (ℓ - i) :=
              Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ n) i)


theorem sum_range_pow_mul_le (N ℓ : ℕ) :
    (∑ n ∈ Finset.range N, n ^ ℓ) * (ℓ + 1) ≤ N ^ (ℓ + 1) := by
  have htel : ∀ M : ℕ,
      ∑ n ∈ Finset.range M, ((n + 1) ^ (ℓ + 1) - n ^ (ℓ + 1)) = M ^ (ℓ + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        exact Nat.add_sub_cancel' (Nat.pow_le_pow_left (Nat.le_succ M) (ℓ + 1))
  calc (∑ n ∈ Finset.range N, n ^ ℓ) * (ℓ + 1)
      = ∑ n ∈ Finset.range N, n ^ ℓ * (ℓ + 1) := Finset.sum_mul ..
    _ = ∑ n ∈ Finset.range N, (ℓ + 1) * n ^ ℓ := by
        apply Finset.sum_congr rfl
        intro n _
        rw [mul_comm]
    _ ≤ ∑ n ∈ Finset.range N, ((n + 1) ^ (ℓ + 1) - n ^ (ℓ + 1)) :=
        Finset.sum_le_sum fun n _ => mul_pow_le_succ_pow_sub n ℓ
    _ = N ^ (ℓ + 1) := htel N


theorem sum_range_pow_le_real (N ℓ : ℕ) :
    (∑ n ∈ Finset.range N, (n : ℝ) ^ ℓ) ≤ (N : ℝ) ^ (ℓ + 1) / (ℓ + 1) := by
  have hnat := sum_range_pow_mul_le N ℓ
  have hcast : ((↑(∑ n ∈ Finset.range N, n ^ ℓ) : ℝ)) * ((ℓ : ℝ) + 1)
      ≤ (N : ℝ) ^ (ℓ + 1) := by
    exact_mod_cast hnat
  have hstep : (∑ n ∈ Finset.range N, (n : ℝ) ^ ℓ) * ((ℓ : ℝ) + 1)
      ≤ (N : ℝ) ^ (ℓ + 1) := by
    simpa only [Nat.cast_sum, Nat.cast_pow] using hcast
  have hpos : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
  calc (∑ n ∈ Finset.range N, (n : ℝ) ^ ℓ)
      = (∑ n ∈ Finset.range N, (n : ℝ) ^ ℓ) * ((ℓ : ℝ) + 1) * ((ℓ : ℝ) + 1)⁻¹ := by
        field_simp
      _ ≤ (N : ℝ) ^ (ℓ + 1) * ((ℓ : ℝ) + 1)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (N : ℝ) ^ (ℓ + 1) / (ℓ + 1) := by
        rw [div_eq_mul_inv]




noncomputable def powMax (k ℓ : ℕ) : ℕ := Nat.findGreatest (fun n => n ^ ℓ ≤ k) k

theorem powMax_spec (k ℓ : ℕ) (hℓ : 1 ≤ ℓ) : (powMax k ℓ) ^ ℓ ≤ k :=
  Nat.findGreatest_spec (P := fun n => n ^ ℓ ≤ k) (Nat.zero_le k) (by
    rw [zero_pow (by omega : ℓ ≠ 0)]
    exact Nat.zero_le k)

theorem le_powMax {k ℓ n : ℕ} (hnk : n ≤ k) (hn : n ^ ℓ ≤ k) : n ≤ powMax k ℓ :=
  Nat.le_findGreatest hnk hn



theorem powMax_le_of_le_exp {k ℓ ℓ' : ℕ} (h : ℓ' ≤ ℓ) (hℓ : 1 ≤ ℓ) :
    powMax k ℓ ≤ powMax k ℓ' := by
  have hNk : powMax k ℓ ≤ k := Nat.findGreatest_le k
  have hspec : (powMax k ℓ) ^ ℓ ≤ k := powMax_spec k ℓ hℓ
  by_cases hN : powMax k ℓ = 0
  · rw [hN]
    exact Nat.zero_le _
  · have hpos : 0 < powMax k ℓ := Nat.pos_of_ne_zero hN
    have hpow : (powMax k ℓ) ^ ℓ' ≤ (powMax k ℓ) ^ ℓ := by
      calc (powMax k ℓ) ^ ℓ' = (powMax k ℓ) ^ ℓ' * 1 := by rw [mul_one]
        _ ≤ (powMax k ℓ) ^ ℓ' * (powMax k ℓ) ^ (ℓ - ℓ') :=
            Nat.mul_le_mul_left _ (Nat.one_le_pow (ℓ - ℓ') (powMax k ℓ) hpos)
        _ = (powMax k ℓ) ^ ℓ := by
            rw [← pow_add, Nat.add_sub_of_le h]
    exact le_powMax hNk (le_trans hpow hspec)


noncomputable def innerSum (k ℓ : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range (k + 1)).filter (fun n => 2 ≤ n ∧ n ^ ℓ ≤ k),
    ((n : ℝ) ^ ℓ) * (((ℓ : ℝ) * Real.log (n : ℝ)) ^ 2)



theorem innerSum_le (k ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    innerSum k ℓ
      ≤ (Real.log (k : ℝ)) ^ 2
        * ((k : ℝ) + (k : ℝ) * (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1)) := by
  unfold innerSum
  have hpoint : ∀ n ∈ (Finset.range (k + 1)).filter (fun n => 2 ≤ n ∧ n ^ ℓ ≤ k),
      ((n : ℝ) ^ ℓ) * (((ℓ : ℝ) * Real.log (n : ℝ)) ^ 2)
        ≤ (Real.log (k : ℝ)) ^ 2 * ((n : ℝ) ^ ℓ) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hn2 : 2 ≤ n := hn'.2.1
    have hnk : n ^ ℓ ≤ k := hn'.2.2
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn2)
    have hlogeq : (ℓ : ℝ) * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ ℓ) := by
      rw [Real.log_pow]
    have hlog_nonneg : 0 ≤ (ℓ : ℝ) * Real.log (n : ℝ) := by
      rw [hlogeq]
      exact Real.log_nonneg (by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
        exact one_le_pow₀ this)
    have hlog_le : (ℓ : ℝ) * Real.log (n : ℝ) ≤ Real.log (k : ℝ) := by
      rw [hlogeq]
      exact Real.log_le_log (pow_pos hn0 ℓ) (by exact_mod_cast hnk)
    have hL_nonneg : 0 ≤ Real.log (k : ℝ) := le_trans hlog_nonneg hlog_le
    have hsq : (((ℓ : ℝ) * Real.log (n : ℝ)) ^ 2) ≤ (Real.log (k : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlog_nonneg hlog_le 2
    have hnpow_nonneg : 0 ≤ (n : ℝ) ^ ℓ := pow_nonneg hn0.le ℓ
    calc ((n : ℝ) ^ ℓ) * (((ℓ : ℝ) * Real.log (n : ℝ)) ^ 2)
        ≤ ((n : ℝ) ^ ℓ) * (Real.log (k : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hnpow_nonneg
      _ = (Real.log (k : ℝ)) ^ 2 * ((n : ℝ) ^ ℓ) := by ring
  have hsub : (Finset.range (k + 1)).filter (fun n => 2 ≤ n ∧ n ^ ℓ ≤ k)
      ⊆ Finset.range (powMax k ℓ + 1) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnk : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn'.1)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (le_powMax hnk hn'.2.2))
  have hstep1 : (∑ n ∈ (Finset.range (k + 1)).filter (fun n => 2 ≤ n ∧ n ^ ℓ ≤ k),
        ((n : ℝ) ^ ℓ) * (((ℓ : ℝ) * Real.log (n : ℝ)) ^ 2))
      ≤ (Real.log (k : ℝ)) ^ 2
        * ∑ n ∈ (Finset.range (k + 1)).filter (fun n => 2 ≤ n ∧ n ^ ℓ ≤ k),
            (n : ℝ) ^ ℓ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpoint
  have hstep2 : (∑ n ∈ (Finset.range (k + 1)).filter (fun n => 2 ≤ n ∧ n ^ ℓ ≤ k),
        (n : ℝ) ^ ℓ) ≤ ∑ n ∈ Finset.range (powMax k ℓ + 1), (n : ℝ) ^ ℓ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => pow_nonneg (Nat.cast_nonneg n) ℓ)
  have hstep3 : (∑ n ∈ Finset.range (powMax k ℓ + 1), (n : ℝ) ^ ℓ)
      ≤ (powMax k ℓ : ℝ) ^ ℓ + (powMax k ℓ : ℝ) ^ (ℓ + 1) / ((ℓ : ℝ) + 1) := by
    rw [Finset.sum_range_succ]
    have htail := sum_range_pow_le_real (powMax k ℓ) ℓ
    linarith
  have hstep4 : (powMax k ℓ : ℝ) ^ ℓ + (powMax k ℓ : ℝ) ^ (ℓ + 1) / ((ℓ : ℝ) + 1)
      ≤ (k : ℝ) + (k : ℝ) * (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1) := by
    have hNl : (powMax k ℓ : ℝ) ^ ℓ ≤ (k : ℝ) := by exact_mod_cast powMax_spec k ℓ (by omega)
    have hNp : (powMax k ℓ : ℝ) ^ (ℓ + 1) ≤ (k : ℝ) * (powMax k ℓ : ℝ) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right hNl (Nat.cast_nonneg _)
    have hpos : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
    have hfrac : (powMax k ℓ : ℝ) ^ (ℓ + 1) / ((ℓ : ℝ) + 1)
        ≤ (k : ℝ) * (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1) :=
      div_le_div_of_nonneg_right hNp hpos.le
    linarith
  calc (∑ n ∈ (Finset.range (k + 1)).filter (fun n => 2 ≤ n ∧ n ^ ℓ ≤ k),
        ((n : ℝ) ^ ℓ) * (((ℓ : ℝ) * Real.log (n : ℝ)) ^ 2))
      ≤ (Real.log (k : ℝ)) ^ 2
        * ∑ n ∈ (Finset.range (k + 1)).filter (fun n => 2 ≤ n ∧ n ^ ℓ ≤ k),
            (n : ℝ) ^ ℓ := hstep1
    _ ≤ (Real.log (k : ℝ)) ^ 2 * ∑ n ∈ Finset.range (powMax k ℓ + 1), (n : ℝ) ^ ℓ := by
        exact mul_le_mul_of_nonneg_left hstep2 (sq_nonneg _)
    _ ≤ (Real.log (k : ℝ)) ^ 2
          * ((powMax k ℓ : ℝ) ^ ℓ + (powMax k ℓ : ℝ) ^ (ℓ + 1) / ((ℓ : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left hstep3 (sq_nonneg _)
    _ ≤ (Real.log (k : ℝ)) ^ 2
          * ((k : ℝ) + (k : ℝ) * (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left hstep4 (sq_nonneg _)










noncomputable def surcharge (k : ℕ) : ℝ :=
  (∑ ℓ ∈ Finset.Icc 2 (Nat.log 2 k), innerSum k ℓ) / (k : ℝ) ^ 2




theorem SA_sum_le (k : ℕ) (hk : X0 ≤ k) :
    surcharge k ≤ (Real.log (k : ℝ)) ^ 2 / (k : ℝ)
      * (((Nat.log 2 k : ℝ) - 1)
        + (powMax k 2 : ℝ) / 3
        + (powMax k 3 : ℝ) * (7 / 4)
        + (powMax k 10 : ℝ) * (Nat.log 2 k : ℝ) / 10) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have hX0pos : 0 < X0 := by norm_num [X0]
    exact_mod_cast (lt_of_lt_of_le hX0pos hk)
  have hM2 : 2 ≤ Nat.log 2 k := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    have : (4 : ℕ) ≤ X0 := by norm_num [X0]
    omega
  have hM10 : 10 ≤ Nat.log 2 k := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    have : (1024 : ℕ) ≤ X0 := by norm_num [X0]
    omega
  have hcard : ((Nat.log 2 k + 1 - 2 : ℕ) : ℝ) = (Nat.log 2 k : ℝ) - 1 := by
    rw [show Nat.log 2 k + 1 - 2 = Nat.log 2 k - 1 by omega]
    rw [Nat.cast_sub (show 1 ≤ Nat.log 2 k by omega)]
    norm_num
  have hinner : (∑ ℓ ∈ Finset.Icc 2 (Nat.log 2 k), innerSum k ℓ)
      ≤ (Real.log (k : ℝ)) ^ 2 * ((k : ℝ)
          * (((Nat.log 2 k : ℝ) - 1)
            + ∑ ℓ ∈ Finset.Icc 2 (Nat.log 2 k), (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1))) := by
    have h1 : ∀ ℓ ∈ Finset.Icc 2 (Nat.log 2 k),
        innerSum k ℓ ≤ (Real.log (k : ℝ)) ^ 2
          * ((k : ℝ) + (k : ℝ) * (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1)) :=
      fun ℓ hℓ => innerSum_le k ℓ (Finset.mem_Icc.mp hℓ).1
    calc (∑ ℓ ∈ Finset.Icc 2 (Nat.log 2 k), innerSum k ℓ)
        ≤ ∑ ℓ ∈ Finset.Icc 2 (Nat.log 2 k), (Real.log (k : ℝ)) ^ 2
            * ((k : ℝ) + (k : ℝ) * (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1)) :=
          Finset.sum_le_sum h1
      _ = ∑ ℓ ∈ Finset.Icc 2 (Nat.log 2 k),
            (Real.log (k : ℝ)) ^ 2 * (k : ℝ)
              * (1 + (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1)) := by
          apply Finset.sum_congr rfl
          intro ℓ _
          ring
      _ = (Real.log (k : ℝ)) ^ 2 * (k : ℝ)
            * ∑ ℓ ∈ Finset.Icc 2 (Nat.log 2 k),
                (1 + (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1)) :=
          (Finset.mul_sum _ _ _).symm
      _ = (Real.log (k : ℝ)) ^ 2 * (k : ℝ)
            * (((Nat.log 2 k : ℝ) - 1)
              + ∑ ℓ ∈ Finset.Icc 2 (Nat.log 2 k), (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1)) := by
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hcard]
          ring
      _ = (Real.log (k : ℝ)) ^ 2 * ((k : ℝ)
            * (((Nat.log 2 k : ℝ) - 1)
              + ∑ ℓ ∈ Finset.Icc 2 (Nat.log 2 k), (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1))) := by
          ring
  have hsumN : (∑ ℓ ∈ Finset.Icc 2 (Nat.log 2 k), (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1))
      ≤ (powMax k 2 : ℝ) / 3 + (powMax k 3 : ℝ) * (7 / 4)
          + (powMax k 10 : ℝ) * (Nat.log 2 k : ℝ) / 10 := by
    have hsplit : Finset.Icc 2 (Nat.log 2 k)
        = Finset.Icc 2 9 ∪ Finset.Icc 10 (Nat.log 2 k) := by
      ext ℓ
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have hdisj : Disjoint (Finset.Icc 2 9) (Finset.Icc 10 (Nat.log 2 k)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_Icc] at hx hx'
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hsplit2 : Finset.Icc 2 9 = ({2} : Finset ℕ) ∪ Finset.Icc 3 9 := by
      ext ℓ
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
      omega
    have hdisj2 : Disjoint ({2} : Finset ℕ) (Finset.Icc 3 9) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc] at hx'
      omega
    rw [hsplit2, Finset.sum_union hdisj2, Finset.sum_singleton]
    have h39 : (∑ ℓ ∈ Finset.Icc 3 9, (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1))
        ≤ (powMax k 3 : ℝ) * (7 / 4) := by
      calc (∑ ℓ ∈ Finset.Icc 3 9, (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1))
          ≤ ∑ ℓ ∈ Finset.Icc 3 9, (powMax k 3 : ℝ) * (1 / 4) := by
            apply Finset.sum_le_sum
            intro ℓ hℓ
            have hℓ3 : 3 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
            have hN3 : powMax k ℓ ≤ powMax k 3 := powMax_le_of_le_exp hℓ3 (by omega)
            have hN3' : (powMax k ℓ : ℝ) ≤ (powMax k 3 : ℝ) := by exact_mod_cast hN3
            have hden4 : (4 : ℝ) ≤ (ℓ : ℝ) + 1 := by
              have : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ3
              linarith
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < (ℓ : ℝ) + 1)]
            have h4 : (powMax k 3 : ℝ) * 4 ≤ (powMax k 3 : ℝ) * ((ℓ : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left hden4 (Nat.cast_nonneg _)
            nlinarith [hN3', h4]
        _ = (powMax k 3 : ℝ) * (7 / 4) := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            norm_num
            ring
    have h10M : (∑ ℓ ∈ Finset.Icc 10 (Nat.log 2 k), (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1))
        ≤ (powMax k 10 : ℝ) * (Nat.log 2 k : ℝ) / 10 := by
      calc (∑ ℓ ∈ Finset.Icc 10 (Nat.log 2 k), (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1))
          ≤ ∑ ℓ ∈ Finset.Icc 10 (Nat.log 2 k), (powMax k 10 : ℝ) * (1 / 10) := by
            apply Finset.sum_le_sum
            intro ℓ hℓ
            have hℓ10 : 10 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
            have hN10 : powMax k ℓ ≤ powMax k 10 := powMax_le_of_le_exp hℓ10 (by omega)
            have hN10' : (powMax k ℓ : ℝ) ≤ (powMax k 10 : ℝ) := by exact_mod_cast hN10
            have hden10 : (10 : ℝ) ≤ (ℓ : ℝ) + 1 := by
              have : (10 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ10
              linarith
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < (ℓ : ℝ) + 1)]
            have h10 : (powMax k 10 : ℝ) * 10 ≤ (powMax k 10 : ℝ) * ((ℓ : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left hden10 (Nat.cast_nonneg _)
            nlinarith [hN10', h10]
        _ ≤ (powMax k 10 : ℝ) * (Nat.log 2 k : ℝ) / 10 := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            have hcard10 : ((Nat.log 2 k + 1 - 10 : ℕ) : ℝ) = (Nat.log 2 k : ℝ) - 9 := by
              rw [show Nat.log 2 k + 1 - 10 = Nat.log 2 k - 9 by omega]
              rw [Nat.cast_sub (show 9 ≤ Nat.log 2 k by omega)]
              norm_num
            rw [hcard10]
            have hcard_le : (Nat.log 2 k : ℝ) - 9 ≤ (Nat.log 2 k : ℝ) := by linarith
            have hnonneg : (0 : ℝ) ≤ (powMax k 10 : ℝ) * (1 / 10) := by positivity
            calc ((Nat.log 2 k : ℝ) - 9) * ((powMax k 10 : ℝ) * (1 / 10))
                ≤ (Nat.log 2 k : ℝ) * ((powMax k 10 : ℝ) * (1 / 10)) :=
                  mul_le_mul_of_nonneg_right hcard_le hnonneg
              _ = (powMax k 10 : ℝ) * (Nat.log 2 k : ℝ) / 10 := by ring
    linarith [h39, h10M]
  calc surcharge k = (∑ ℓ ∈ Finset.Icc 2 (Nat.log 2 k), innerSum k ℓ) / (k : ℝ) ^ 2 := rfl
    _ ≤ ((Real.log (k : ℝ)) ^ 2 * ((k : ℝ)
          * (((Nat.log 2 k : ℝ) - 1)
            + ∑ ℓ ∈ Finset.Icc 2 (Nat.log 2 k), (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1)))) / (k : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hinner (sq_nonneg _)
    _ = (Real.log (k : ℝ)) ^ 2 / (k : ℝ)
          * (((Nat.log 2 k : ℝ) - 1)
            + ∑ ℓ ∈ Finset.Icc 2 (Nat.log 2 k), (powMax k ℓ : ℝ) / ((ℓ : ℝ) + 1)) := by
        field_simp
        try ring
    _ ≤ (Real.log (k : ℝ)) ^ 2 / (k : ℝ)
          * (((Nat.log 2 k : ℝ) - 1)
            + ((powMax k 2 : ℝ) / 3 + (powMax k 3 : ℝ) * (7 / 4)
                + (powMax k 10 : ℝ) * (Nat.log 2 k : ℝ) / 10)) := by
        gcongr
    _ = (Real.log (k : ℝ)) ^ 2 / (k : ℝ)
          * (((Nat.log 2 k : ℝ) - 1)
            + (powMax k 2 : ℝ) / 3
            + (powMax k 3 : ℝ) * (7 / 4)
            + (powMax k 10 : ℝ) * (Nat.log 2 k : ℝ) / 10) := by ring








theorem antitoneOn_pow_mul_exp_neg (p : ℕ) (hp : 1 ≤ p) {β : ℝ} (hβ : 0 < β) :
    AntitoneOn (fun u : ℝ => u ^ p * Real.exp (-(β * u)))
      (Set.Ici ((p : ℝ) / β)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · fun_prop
  · intro x _
    fun_prop
  · intro x hx
    rw [interior_Ici] at hx
    have hxβ : (p : ℝ) < β * x := by
      change (p : ℝ) / β < x at hx
      rw [div_lt_iff₀ hβ] at hx
      linarith
    have hx0 : 0 ≤ x :=
      le_of_lt (lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ (p : ℝ) / β) hx)
    have hderiv : HasDerivAt (fun u : ℝ => u ^ p * Real.exp (-(β * u)))
        (Real.exp (-(β * x)) * ((p : ℝ) * x ^ (p - 1) + x ^ p * (-β))) x := by
      have h1 : HasDerivAt (fun u : ℝ => (-β) * u) (-β) x := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (-β)
      have h2 : HasDerivAt (fun u : ℝ => Real.exp ((-β) * u))
          (Real.exp ((-β) * x) * (-β)) x :=
        show HasDerivAt (Real.exp ∘ fun u : ℝ => (-β) * u) _ x from
          (Real.hasDerivAt_exp ((-β) * x)).comp x h1
      have h3 : HasDerivAt ((fun u : ℝ => u ^ p) * fun u : ℝ => Real.exp ((-β) * u))
          ((p : ℝ) * x ^ (p - 1) * Real.exp ((-β) * x)
            + x ^ p * (Real.exp ((-β) * x) * (-β))) x :=
        (hasDerivAt_pow p x).mul h2
      convert h3 using 1
      · ext u
        simp only [Pi.mul_apply, neg_mul]
      · ring
    rw [hderiv.deriv]
    have hup : 0 ≤ x ^ (p - 1) := pow_nonneg hx0 _
    have hfac : (p : ℝ) * x ^ (p - 1) + x ^ p * (-β)
        = x ^ (p - 1) * ((p : ℝ) - β * x) := by
      rw [show x ^ p = x ^ (p - 1) * x by
        rw [← pow_succ, Nat.sub_add_cancel hp]]
      ring
    rw [hfac]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (mul_nonpos_of_nonneg_of_nonpos hup (by linarith))



theorem log_pow_div_rpow_le {X0 k : ℕ} (hX0 : 0 < (X0 : ℝ)) (hXk : X0 ≤ k)
    {p : ℕ} (hp : 1 ≤ p) {β : ℝ} (hβ : 0 < β)
    (hlog : (p : ℝ) / β ≤ Real.log (X0 : ℝ)) :
    (Real.log (k : ℝ)) ^ p / (k : ℝ) ^ β
      ≤ (Real.log (X0 : ℝ)) ^ p / (X0 : ℝ) ^ β := by
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le hX0 (by exact_mod_cast hXk)
  have hkx : (p : ℝ) / β ≤ Real.log (k : ℝ) :=
    le_trans hlog (Real.log_le_log hX0 (by exact_mod_cast hXk))
  have hxy : Real.log (X0 : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log hX0 (by exact_mod_cast hXk)
  have hanti := antitoneOn_pow_mul_exp_neg p hp hβ hlog hkx hxy
  rw [Real.rpow_def_of_pos hk0, Real.rpow_def_of_pos hX0]
  simpa only [Real.exp_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using hanti


theorem le_rpow_one_div_of_pow_le {a b : ℝ} {n : ℕ} (hn : 0 < n)
    (ha : 0 ≤ a) (h : a ^ n ≤ b) : a ≤ b ^ ((n : ℝ)⁻¹) := by
  have h := Real.rpow_le_rpow (pow_nonneg ha n) h
    (by positivity : (0 : ℝ) ≤ ((n : ℝ)⁻¹))
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha] at h
  have hmul : (n : ℝ) * (n : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')
  rw [hmul, Real.rpow_one] at h
  exact h






theorem surcharge_lt (k : ℕ) (hk : X0 ≤ k) : surcharge k < 0.07268 := by
  have hsum := SA_sum_le k hk
  have hX0pos : 0 < X0 := by norm_num [X0]
  have hX0R : (0 : ℝ) < (X0 : ℝ) := by exact_mod_cast hX0pos
  have hk0 : (0 : ℝ) < (k : ℝ) :=
    lt_of_lt_of_le hX0R (by exact_mod_cast hk)
  have hkge : (X0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hLnn : 0 ≤ Real.log (k : ℝ) := by
    apply Real.log_nonneg
    have h1X : (1 : ℕ) ≤ X0 := by norm_num [X0]
    exact_mod_cast (le_trans h1X hk)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2pos : 0 < Real.log 2 := lt_trans (by norm_num) hlog2
  have hinvlog2 : 1 / Real.log 2 ≤ 2 := by
    rw [div_le_iff₀ hlog2pos]
    linarith

  have hexp151 : (3594641 : ℝ) < Real.exp 15.1 := by
    have h01 : (1.1 : ℝ) ≤ Real.exp 0.1 := by
      have h := Real.sum_le_exp_of_nonneg (x := (0.1 : ℝ)) (by norm_num) 2
      have h2 : (∑ i ∈ Finset.range 2, (0.1 : ℝ) ^ i / (Nat.factorial i : ℝ)) = 1.1 := by
        norm_num [Finset.sum_range_succ]
      rw [h2] at h
      exact h
    have he1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_d9
    have h15 : (2.7182818283 : ℝ) ^ 15 ≤ Real.exp 15 := by
      have hexp15 : Real.exp 15 = (Real.exp 1) ^ 15 := by
        have := Real.exp_nat_mul (x := (1 : ℝ)) 15
        simpa using this
      rw [hexp15]
      exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) he1 15
    have hmul : Real.exp 15.1 = Real.exp 15 * Real.exp 0.1 := by
      rw [show (15.1 : ℝ) = 15 + 0.1 by norm_num, Real.exp_add]
    rw [hmul]
    have hprod : (2.7182818283 : ℝ) ^ 15 * 1.1 ≤ Real.exp 15 * Real.exp 0.1 :=
      mul_le_mul h15 h01 (by norm_num) (Real.exp_pos 15).le
    have hnum : (3594641 : ℝ) < (2.7182818283 : ℝ) ^ 15 * 1.1 := by norm_num
    linarith
  have hlogX0lt : Real.log (X0 : ℝ) < 15.1 := by
    have h : Real.log (3594641 : ℝ) < 15.1 :=
      (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3594641)).mpr hexp151
    simpa [X0] using h
  have hlogX0ge : (15 : ℝ) ≤ Real.log (X0 : ℝ) := by
    apply (Real.le_log_iff_exp_le hX0R).mpr
    have hexp15 : Real.exp 15 = (Real.exp 1) ^ 15 := by
      have := Real.exp_nat_mul (x := (1 : ℝ)) 15
      simpa using this
    rw [hexp15]
    have he1 : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
    have h15 : (Real.exp 1) ^ 15 < (2.7182818286 : ℝ) ^ 15 :=
      pow_lt_pow_left₀ he1 (Real.exp_pos 1).le (by norm_num)
    have hnum : (2.7182818286 : ℝ) ^ 15 < (X0 : ℝ) := by norm_num [X0]
    linarith
  have hL0nn : 0 ≤ Real.log (X0 : ℝ) := le_trans (by norm_num) hlogX0ge

  have hMle : (Nat.log 2 k : ℝ) ≤ Real.log (k : ℝ) / Real.log 2 := by
    have hkne : k ≠ 0 := by omega
    have h2M : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 hkne
    have hlog : Real.log ((2 : ℝ) ^ Nat.log 2 k) ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast h2M)
    rw [Real.log_pow] at hlog
    rw [le_div_iff₀ hlog2pos]
    linarith [hlog]

  have hdec1 : (Real.log (k : ℝ)) ^ 3 / (k : ℝ)
      ≤ (Real.log (X0 : ℝ)) ^ 3 / (X0 : ℝ) := by
    simpa only [Real.rpow_one] using
      (log_pow_div_rpow_le hX0R hk (p := 3) (by norm_num) (β := 1) (by norm_num)
        (by norm_num; linarith [hlogX0ge]))
  have hdec2 : (Real.log (k : ℝ)) ^ 2 / (k : ℝ) ^ (1 / 2 : ℝ)
      ≤ (Real.log (X0 : ℝ)) ^ 2 / (X0 : ℝ) ^ (1 / 2 : ℝ) :=
    log_pow_div_rpow_le hX0R hk (p := 2) (by norm_num) (β := 1 / 2) (by norm_num)
      (by norm_num; linarith [hlogX0ge])
  have hdec3 : (Real.log (k : ℝ)) ^ 2 / (k : ℝ) ^ (2 / 3 : ℝ)
      ≤ (Real.log (X0 : ℝ)) ^ 2 / (X0 : ℝ) ^ (2 / 3 : ℝ) :=
    log_pow_div_rpow_le hX0R hk (p := 2) (by norm_num) (β := 2 / 3) (by norm_num)
      (by norm_num; linarith [hlogX0ge])
  have hdec4 : (Real.log (k : ℝ)) ^ 3 / (k : ℝ) ^ (9 / 10 : ℝ)
      ≤ (Real.log (X0 : ℝ)) ^ 3 / (X0 : ℝ) ^ (9 / 10 : ℝ) :=
    log_pow_div_rpow_le hX0R hk (p := 3) (by norm_num) (β := 9 / 10) (by norm_num)
      (by norm_num; linarith [hlogX0ge])

  have hV1 : (Real.log (X0 : ℝ)) ^ 3 / (X0 : ℝ) ≤ 15.1 ^ 3 / (X0 : ℝ) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hL0nn hlogX0lt.le 3) hX0R.le
  have hV2 : (Real.log (X0 : ℝ)) ^ 2 / Real.sqrt (X0 : ℝ) ≤ 15.1 ^ 2 / 1895 := by
    have hsq : (1895 : ℝ) ≤ Real.sqrt (X0 : ℝ) := by
      rw [Real.le_sqrt (by norm_num) hX0R.le]
      norm_num [X0]
    calc (Real.log (X0 : ℝ)) ^ 2 / Real.sqrt (X0 : ℝ)
        ≤ 15.1 ^ 2 / Real.sqrt (X0 : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hL0nn hlogX0lt.le 2)
            (Real.sqrt_nonneg _)
      _ ≤ 15.1 ^ 2 / 1895 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq
  have hV3 : (Real.log (X0 : ℝ)) ^ 2 / (X0 : ℝ) ^ (2 / 3 : ℝ) ≤ 15.1 ^ 2 / 153 ^ 2 := by
    have hcube : (153 : ℝ) ≤ (X0 : ℝ) ^ (1 / 3 : ℝ) := by
      have h := le_rpow_one_div_of_pow_le (a := (153 : ℝ)) (b := (X0 : ℝ))
        (n := 3) (by norm_num) (by norm_num) (by norm_num [X0])
      simpa using h
    have hpow : (153 : ℝ) ^ 2 ≤ (X0 : ℝ) ^ (2 / 3 : ℝ) := by
      have hsq : ((X0 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 = (X0 : ℝ) ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0R.le]
        norm_num
      calc (153 : ℝ) ^ 2 ≤ ((X0 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := by
            exact pow_le_pow_left₀ (by norm_num) hcube 2
        _ = (X0 : ℝ) ^ (2 / 3 : ℝ) := hsq
    calc (Real.log (X0 : ℝ)) ^ 2 / (X0 : ℝ) ^ (2 / 3 : ℝ)
        ≤ 15.1 ^ 2 / (X0 : ℝ) ^ (2 / 3 : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hL0nn hlogX0lt.le 2)
            (Real.rpow_nonneg hX0R.le _)
      _ ≤ 15.1 ^ 2 / 153 ^ 2 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpow
  have hV4 : (Real.log (X0 : ℝ)) ^ 3 / (X0 : ℝ) ^ (9 / 10 : ℝ) ≤ 15.1 ^ 3 / 4 ^ 9 := by
    have hroot : (4 : ℝ) ≤ (X0 : ℝ) ^ (1 / 10 : ℝ) := by
      have h := le_rpow_one_div_of_pow_le (a := (4 : ℝ)) (b := (X0 : ℝ))
        (n := 10) (by norm_num) (by norm_num) (by norm_num [X0])
      simpa using h
    have hpow : (4 : ℝ) ^ 9 ≤ (X0 : ℝ) ^ (9 / 10 : ℝ) := by
      have hpow9 : ((X0 : ℝ) ^ (1 / 10 : ℝ)) ^ 9 = (X0 : ℝ) ^ (9 / 10 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0R.le]
        norm_num
      calc (4 : ℝ) ^ 9 ≤ ((X0 : ℝ) ^ (1 / 10 : ℝ)) ^ 9 :=
            pow_le_pow_left₀ (by norm_num) hroot 9
        _ = (X0 : ℝ) ^ (9 / 10 : ℝ) := hpow9
    calc (Real.log (X0 : ℝ)) ^ 3 / (X0 : ℝ) ^ (9 / 10 : ℝ)
        ≤ 15.1 ^ 3 / (X0 : ℝ) ^ (9 / 10 : ℝ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ hL0nn hlogX0lt.le 3)
            (Real.rpow_nonneg hX0R.le _)
      _ ≤ 15.1 ^ 3 / 4 ^ 9 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpow

  have hN2le : (powMax k 2 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    rw [Real.le_sqrt (by positivity) hk0.le]
    exact_mod_cast powMax_spec k 2 (by norm_num)
  have hN3le : (powMax k 3 : ℝ) ≤ (k : ℝ) ^ (1 / 3 : ℝ) := by
    have h := le_rpow_one_div_of_pow_le (a := (powMax k 3 : ℝ)) (b := (k : ℝ))
      (n := 3) (by norm_num) (by positivity)
      (by exact_mod_cast powMax_spec k 3 (by norm_num))
    simpa using h
  have hN10le : (powMax k 10 : ℝ) ≤ (k : ℝ) ^ (1 / 10 : ℝ) := by
    have h := le_rpow_one_div_of_pow_le (a := (powMax k 10 : ℝ)) (b := (k : ℝ))
      (n := 10) (by norm_num) (by positivity)
      (by exact_mod_cast powMax_spec k 10 (by norm_num))
    simpa using h
  have hN2ratio : (powMax k 2 : ℝ) / (k : ℝ) ≤ 1 / Real.sqrt (k : ℝ) := by
    have hk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
    rw [div_le_div_iff₀ hk0 (by positivity)]
    have hsq : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) :=
      by simpa only [sq] using Real.sq_sqrt hk0.le
    nlinarith [hN2le]
  have hN3ratio : (powMax k 3 : ℝ) / (k : ℝ) ≤ (k : ℝ) ^ (-(2 / 3) : ℝ) := by
    calc (powMax k 3 : ℝ) / (k : ℝ) ≤ (k : ℝ) ^ (1 / 3 : ℝ) / (k : ℝ) :=
          div_le_div_of_nonneg_right hN3le hk0.le
      _ = (k : ℝ) ^ (-(2 / 3) : ℝ) := by
          have h1 : (k : ℝ) ^ (1 / 3 : ℝ) / (k : ℝ)
              = (k : ℝ) ^ (1 / 3 : ℝ) / (k : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          rw [h1, ← Real.rpow_sub hk0]
          norm_num
  have hN10ratio : (powMax k 10 : ℝ) / (k : ℝ) ≤ (k : ℝ) ^ (-(9 / 10) : ℝ) := by
    calc (powMax k 10 : ℝ) / (k : ℝ) ≤ (k : ℝ) ^ (1 / 10 : ℝ) / (k : ℝ) :=
          div_le_div_of_nonneg_right hN10le hk0.le
      _ = (k : ℝ) ^ (-(9 / 10) : ℝ) := by
          have h1 : (k : ℝ) ^ (1 / 10 : ℝ) / (k : ℝ)
              = (k : ℝ) ^ (1 / 10 : ℝ) / (k : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          rw [h1, ← Real.rpow_sub hk0]
          norm_num

  have hT1 : (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * ((Nat.log 2 k : ℝ) - 1)
      ≤ 2 * 15.1 ^ 3 / (X0 : ℝ) := by
    calc (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * ((Nat.log 2 k : ℝ) - 1)
        ≤ (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * (Nat.log 2 k : ℝ) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * (Real.log (k : ℝ) / Real.log 2) := by
          apply mul_le_mul_of_nonneg_left hMle (by positivity)
      _ = (Real.log (k : ℝ)) ^ 3 / (k : ℝ) / Real.log 2 := by ring
      _ = ((Real.log (k : ℝ)) ^ 3 / (k : ℝ)) * (1 / Real.log 2) := by ring
      _ ≤ (15.1 ^ 3 / (X0 : ℝ)) * 2 := by
          apply mul_le_mul _ hinvlog2 (by positivity) (by positivity)
          exact le_trans hdec1 hV1
      _ = 2 * 15.1 ^ 3 / (X0 : ℝ) := by ring
  have hT2 : (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * ((powMax k 2 : ℝ) / 3)
      ≤ 15.1 ^ 2 / (3 * 1895) := by
    have heq : (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * ((powMax k 2 : ℝ) / 3)
        = ((Real.log (k : ℝ)) ^ 2 / 3) * ((powMax k 2 : ℝ) / (k : ℝ)) := by ring
    rw [heq]
    have hstep : ((Real.log (k : ℝ)) ^ 2 / 3) * ((powMax k 2 : ℝ) / (k : ℝ))
        ≤ ((Real.log (k : ℝ)) ^ 2 / 3) * (1 / Real.sqrt (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hN2ratio (by positivity)
    have hstep2 : ((Real.log (k : ℝ)) ^ 2 / 3) * (1 / Real.sqrt (k : ℝ))
        = (Real.log (k : ℝ)) ^ 2 / Real.sqrt (k : ℝ) / 3 := by ring
    rw [hstep2] at hstep
    have hdec2sqrt : (Real.log (k : ℝ)) ^ 2 / Real.sqrt (k : ℝ)
        ≤ (Real.log (X0 : ℝ)) ^ 2 / Real.sqrt (X0 : ℝ) :=
      by simpa only [Real.sqrt_eq_rpow] using hdec2
    calc ((Real.log (k : ℝ)) ^ 2 / 3) * ((powMax k 2 : ℝ) / (k : ℝ))
        ≤ (Real.log (k : ℝ)) ^ 2 / Real.sqrt (k : ℝ) / 3 := hstep
      _ ≤ (15.1 ^ 2 / 1895) / 3 :=
          div_le_div_of_nonneg_right (le_trans hdec2sqrt hV2) (by norm_num)
      _ = 15.1 ^ 2 / (3 * 1895) := by ring
  have hT3 : (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * ((powMax k 3 : ℝ) * (7 / 4))
      ≤ 7 * 15.1 ^ 2 / (4 * 153 ^ 2) := by
    have heq : (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * ((powMax k 3 : ℝ) * (7 / 4))
        = (7 / 4) * ((Real.log (k : ℝ)) ^ 2 * ((powMax k 3 : ℝ) / (k : ℝ))) := by ring
    rw [heq]
    have hstep : (7 / 4) * ((Real.log (k : ℝ)) ^ 2 * ((powMax k 3 : ℝ) / (k : ℝ)))
        ≤ (7 / 4) * ((Real.log (k : ℝ)) ^ 2 * (k : ℝ) ^ (-(2 / 3) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hN3ratio (sq_nonneg _)
    have hstep2 : (7 / 4) * ((Real.log (k : ℝ)) ^ 2 * (k : ℝ) ^ (-(2 / 3) : ℝ))
        = (7 / 4) * ((Real.log (k : ℝ)) ^ 2 / (k : ℝ) ^ (2 / 3 : ℝ)) := by
      rw [Real.rpow_neg hk0.le, div_eq_mul_inv]
      ring
    rw [hstep2] at hstep
    calc (7 / 4) * ((Real.log (k : ℝ)) ^ 2 * ((powMax k 3 : ℝ) / (k : ℝ)))
        ≤ (7 / 4) * ((Real.log (k : ℝ)) ^ 2 / (k : ℝ) ^ (2 / 3 : ℝ)) := hstep
      _ ≤ (7 / 4) * (15.1 ^ 2 / 153 ^ 2) :=
          mul_le_mul_of_nonneg_left (le_trans hdec3 hV3) (by norm_num)
      _ = 7 * 15.1 ^ 2 / (4 * 153 ^ 2) := by ring
  have hT4 : (Real.log (k : ℝ)) ^ 2 / (k : ℝ)
        * ((powMax k 10 : ℝ) * (Nat.log 2 k : ℝ) / 10)
      ≤ 2 * 15.1 ^ 3 / (10 * 4 ^ 9) := by
    have heq : (Real.log (k : ℝ)) ^ 2 / (k : ℝ)
          * ((powMax k 10 : ℝ) * (Nat.log 2 k : ℝ) / 10)
        = ((Real.log (k : ℝ)) ^ 2 * (Nat.log 2 k : ℝ) / 10)
            * ((powMax k 10 : ℝ) / (k : ℝ)) := by ring
    rw [heq]
    have hstep : ((Real.log (k : ℝ)) ^ 2 * (Nat.log 2 k : ℝ) / 10)
          * ((powMax k 10 : ℝ) / (k : ℝ))
        ≤ ((Real.log (k : ℝ)) ^ 2 * (Real.log (k : ℝ) / Real.log 2) / 10)
            * (k : ℝ) ^ (-(9 / 10) : ℝ) := by
      apply mul_le_mul _ hN10ratio (by positivity) (by positivity)
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hMle (sq_nonneg _)
    have hstep2 : ((Real.log (k : ℝ)) ^ 2 * (Real.log (k : ℝ) / Real.log 2) / 10)
          * (k : ℝ) ^ (-(9 / 10) : ℝ)
        = (Real.log (k : ℝ)) ^ 3 / (k : ℝ) ^ (9 / 10 : ℝ) / (10 * Real.log 2) := by
      rw [Real.rpow_neg hk0.le, div_eq_mul_inv]
      ring
    rw [hstep2] at hstep
    calc ((Real.log (k : ℝ)) ^ 2 * (Nat.log 2 k : ℝ) / 10)
          * ((powMax k 10 : ℝ) / (k : ℝ))
        ≤ (Real.log (k : ℝ)) ^ 3 / (k : ℝ) ^ (9 / 10 : ℝ) / (10 * Real.log 2) := hstep
      _ ≤ (15.1 ^ 3 / 4 ^ 9) / (10 * 0.6931471803) := by
          apply div_le_div₀ (by positivity) (le_trans hdec4 hV4) (by norm_num) (by nlinarith [hlog2])
      _ ≤ 2 * 15.1 ^ 3 / (10 * 4 ^ 9) := by
          rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 10 * 0.6931471803)
            (by norm_num : (0 : ℝ) < 10 * 4 ^ 9)]
          nlinarith

  have hcomb : (Real.log (k : ℝ)) ^ 2 / (k : ℝ)
        * (((Nat.log 2 k : ℝ) - 1)
          + (powMax k 2 : ℝ) / 3
          + (powMax k 3 : ℝ) * (7 / 4)
          + (powMax k 10 : ℝ) * (Nat.log 2 k : ℝ) / 10)
      = (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * ((Nat.log 2 k : ℝ) - 1)
        + (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * ((powMax k 2 : ℝ) / 3)
        + (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * ((powMax k 3 : ℝ) * (7 / 4))
        + (Real.log (k : ℝ)) ^ 2 / (k : ℝ)
            * ((powMax k 10 : ℝ) * (Nat.log 2 k : ℝ) / 10) := by ring
  calc surcharge k
      ≤ (Real.log (k : ℝ)) ^ 2 / (k : ℝ)
          * (((Nat.log 2 k : ℝ) - 1)
            + (powMax k 2 : ℝ) / 3
            + (powMax k 3 : ℝ) * (7 / 4)
            + (powMax k 10 : ℝ) * (Nat.log 2 k : ℝ) / 10) := hsum
    _ = (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * ((Nat.log 2 k : ℝ) - 1)
        + (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * ((powMax k 2 : ℝ) / 3)
        + (Real.log (k : ℝ)) ^ 2 / (k : ℝ) * ((powMax k 3 : ℝ) * (7 / 4))
        + (Real.log (k : ℝ)) ^ 2 / (k : ℝ)
            * ((powMax k 10 : ℝ) * (Nat.log 2 k : ℝ) / 10) := hcomb
    _ ≤ 2 * 15.1 ^ 3 / (X0 : ℝ) + 15.1 ^ 2 / (3 * 1895)
        + 7 * 15.1 ^ 2 / (4 * 153 ^ 2) + 2 * 15.1 ^ 3 / (10 * 4 ^ 9) := by
      linarith [hT1, hT2, hT3, hT4]
    _ < 0.07268 := by norm_num [X0]








theorem activeN_Apart_le {k n : ℕ} (hn : n ∈ activeN k) (hn4 : 4 ≤ n) :
    (Real.log (n : ℝ) - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ)
      ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ 2 / (k : ℝ) ^ 2 := by
  have hn' := Finset.mem_filter.mp hn
  have hnk : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn'.1)
  have hn0 : 0 < n := by omega
  have hk0 : 0 < k := lt_of_lt_of_le (by omega) hnk
  have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hk0R : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  set m : ℕ := k / n with hm
  have hm1 : 1 ≤ m := Nat.div_pos hnk hn0
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  set b : ℝ := (k : ℝ) / (m : ℝ) with hb
  have hbpos : 0 < b := by rw [hb]; positivity
  have hdiv := (Nat.div_eq_iff hn0).mp hm.symm
  have hnle_b : (n : ℝ) ≤ b := by
    rw [hb, le_div_iff₀ hmpos]
    exact_mod_cast (by simpa [mul_comm] using hdiv.1 : n * m ≤ k)
  have hkle : (k : ℝ) < (n : ℝ) * ((m : ℝ) + 1) := by
    have h2 : k ≤ m * n + n - 1 := hdiv.2
    have h3 : k < m * n + n := by omega
    have h4 : ((m * n + n : ℕ) : ℝ) = ((m : ℝ) * n + n) := by push_cast; ring
    have h5 : (k : ℝ) < ((m * n + n : ℕ) : ℝ) := by exact_mod_cast h3
    rw [h4] at h5
    nlinarith
  have hc : cBin k m = Real.log b / b := by
    simp only [cBin, RHLean.GateII.AWGC.Lb, hb]
  have he1 : Real.exp 1 ≤ (n : ℝ) := by
    have h := Real.exp_one_lt_d9
    norm_num at h
    have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    linarith
  have he1b : Real.exp 1 ≤ b := le_trans he1 hnle_b
  have hlogdiv : Real.log b / b ≤ Real.log (n : ℝ) / (n : ℝ) :=
    Real.log_div_self_antitoneOn he1 he1b hnle_b
  have hA_nonneg : 0 ≤ Real.log (n : ℝ) - cBin k m * (n : ℝ) := by
    rw [hc]
    have hrew : Real.log (n : ℝ) - Real.log b / b * (n : ℝ)
        = (n : ℝ) * (Real.log (n : ℝ) / (n : ℝ) - Real.log b / b) := by
      field_simp
    rw [hrew]
    exact mul_nonneg hn0R.le (sub_nonneg.mpr hlogdiv)
  have hlogbn : Real.log (n : ℝ) ≤ Real.log b := Real.log_le_log hn0R hnle_b
  have hA_le : Real.log (n : ℝ) - cBin k m * (n : ℝ)
      ≤ (1 - (n : ℝ) / b) * Real.log (n : ℝ) := by
    rw [hc]
    have hrew : Real.log (n : ℝ) - Real.log b / b * (n : ℝ)
        = (1 - (n : ℝ) / b) * Real.log (n : ℝ)
          + ((n : ℝ) / b) * (Real.log (n : ℝ) - Real.log b) := by
      field_simp
      ring
    rw [hrew]
    have h2 : ((n : ℝ) / b) * (Real.log (n : ℝ) - Real.log b) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  have hfactor_lt : (1 - (n : ℝ) / b) < (n : ℝ) / (k : ℝ) := by
    have h1 : b - (n : ℝ) < (n : ℝ) / (m : ℝ) := by
      rw [hb]
      have hnum : (k : ℝ) / (m : ℝ) - (n : ℝ) = ((k : ℝ) - (m : ℝ) * (n : ℝ)) / (m : ℝ) :=
        by field_simp
      rw [hnum]
      apply div_lt_div_of_pos_right _ hmpos
      nlinarith [hkle]
    have h2 : (b - (n : ℝ)) / b < ((n : ℝ) / (m : ℝ)) / b := by
      apply div_lt_div_of_pos_right h1 hbpos
    have h3 : ((n : ℝ) / (m : ℝ)) / b = (n : ℝ) / (k : ℝ) := by
      rw [hb]
      field_simp
    have h4 : (b - (n : ℝ)) / b = 1 - (n : ℝ) / b := by
      field_simp
    linarith [h2, h3]
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hA_lt : Real.log (n : ℝ) - cBin k m * (n : ℝ)
      < (n : ℝ) * Real.log (n : ℝ) / (k : ℝ) := by
    calc Real.log (n : ℝ) - cBin k m * (n : ℝ)
        ≤ (1 - (n : ℝ) / b) * Real.log (n : ℝ) := hA_le
      _ < ((n : ℝ) / (k : ℝ)) * Real.log (n : ℝ) := by
          exact mul_lt_mul_of_pos_right hfactor_lt hlogpos
      _ = (n : ℝ) * Real.log (n : ℝ) / (k : ℝ) := by ring
  have hcbin : cBin k (k / n) = cBin k m := by rw [← hm]
  rw [hcbin]
  have hsq := pow_le_pow_left₀ hA_nonneg hA_lt.le 2
  calc (Real.log (n : ℝ) - cBin k m * (n : ℝ)) ^ 2 / (n : ℝ)
      ≤ ((n : ℝ) * Real.log (n : ℝ) / (k : ℝ)) ^ 2 / (n : ℝ) :=
        div_le_div_of_nonneg_right hsq hn0R.le
    _ = (n : ℝ) * (Real.log (n : ℝ)) ^ 2 / (k : ℝ) ^ 2 := by
        field_simp




noncomputable def primePowerWitness (n : ℕ) (h : IsPrimePow n) : Σ _ : ℕ, ℕ :=
  let p := Classical.choose h
  let e := Classical.choose (Classical.choose_spec h)
  ⟨e, p⟩

theorem primePowerWitness_spec {n : ℕ} (h : IsPrimePow n) :
    ((primePowerWitness n h).2).Prime ∧ 0 < (primePowerWitness n h).1 ∧
      (primePowerWitness n h).2 ^ (primePowerWitness n h).1 = n := by
  simpa only [primePowerWitness, Nat.prime_iff] using
    Classical.choose_spec (Classical.choose_spec h)


noncomputable def ppPair (n : ℕ) : Σ _ : ℕ, ℕ :=
  if h : IsPrimePow n then primePowerWitness n h else ⟨0, 0⟩

theorem ppPair_eq_witness {n : ℕ} (h : IsPrimePow n) :
    ppPair n = primePowerWitness n h := by
  simp only [ppPair, dif_pos h]

theorem ppPair_spec {n : ℕ} (h : IsPrimePow n) :
    ((ppPair n).2).Prime ∧ 0 < (ppPair n).1 ∧ (ppPair n).2 ^ (ppPair n).1 = n := by
  rw [ppPair_eq_witness h]
  exact primePowerWitness_spec h



noncomputable def primePairs (k : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 2 (Nat.log 2 k)).sigma (fun e =>
    (Finset.range (k + 1)).filter (fun p => Nat.Prime p ∧ p ^ e ≤ k))




theorem activeN_Apart_sum_le (k : ℕ) (hk : 4 ≤ k) :
    (∑ n ∈ (activeN k).filter (fun n => ¬ Nat.Prime n),
        (Real.log (n : ℝ) - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ))
      ≤ surcharge k := by
  classical
  set s : Finset ℕ := (activeN k).filter (fun n => ¬ Nat.Prime n) with hs
  have ipp_of_mem : ∀ {n : ℕ}, n ∈ s → IsPrimePow n := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hΛ : Lambda n ≠ 0 := (Finset.mem_filter.mp hn'.1).2.1
    exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (by simpa [Lambda] using hΛ)
  have hk0 : 0 < k := by omega
  have hk0R : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0

  have hpoint : ∀ n ∈ s,
      (Real.log (n : ℝ) - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ)
        ≤ (ppPair n).2 ^ (ppPair n).1
            * ((ppPair n).1 * Real.log (ppPair n).2) ^ 2 / (k : ℝ) ^ 2 := by
    intro n hn
    have hmem : n ∈ activeN k := (Finset.mem_filter.mp hn).1
    have hnp : ¬ Nat.Prime n := (Finset.mem_filter.mp hn).2
    have hpp : IsPrimePow n := ipp_of_mem hn
    obtain ⟨hp, he0, hpe⟩ := ppPair_spec hpp
    have he_ne_one : (ppPair n).1 ≠ 1 := by
      intro h1
      apply hnp
      have this : n = (ppPair n).2 := by simpa only [h1, pow_one] using hpe.symm
      rw [this]
      exact hp
    have he2 : 2 ≤ (ppPair n).1 := by omega
    have hn4 : 4 ≤ n := by
      rw [← hpe]
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ (ppPair n).2 ^ 2 := Nat.pow_le_pow_left hp.two_le 2
        _ ≤ (ppPair n).2 ^ (ppPair n).1 := by
            apply Nat.pow_le_pow_right hp.one_le he2
    have hlog : Real.log (n : ℝ)
        = ((ppPair n).1 : ℝ) * Real.log ((ppPair n).2 : ℝ) := by
      nth_rw 1 [← hpe]
      rw [Nat.cast_pow, Real.log_pow]
    have hpeR : ((ppPair n).2 : ℝ) ^ (ppPair n).1 = (n : ℝ) :=
      by exact_mod_cast hpe
    refine le_trans (activeN_Apart_le hmem hn4) ?_
    rw [hpeR, hlog]

  have hinj : ∀ n1 ∈ s, ∀ n2 ∈ s, ppPair n1 = ppPair n2 → n1 = n2 := by
    intro n1 h1 n2 h2 heq
    have hpp1 := ipp_of_mem h1
    have hpp2 := ipp_of_mem h2
    have s1 := ppPair_spec hpp1
    have s2 := ppPair_spec hpp2
    calc n1 = (ppPair n1).2 ^ (ppPair n1).1 := s1.2.2.symm
      _ = (ppPair n2).2 ^ (ppPair n2).1 := by rw [heq]
      _ = n2 := s2.2.2

  have hsub : s.image ppPair ⊆ primePairs k := by
    intro q hq
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
    have hmem : n ∈ activeN k := (Finset.mem_filter.mp hn).1
    have hnk : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hmem).1)
    have hpp := ipp_of_mem hn
    obtain ⟨hp, he0, hpe⟩ := ppPair_spec hpp
    have he2 : 2 ≤ (ppPair n).1 := by
      by_contra h
      have h1 : (ppPair n).1 ≤ 1 := by omega
      have h2 : (ppPair n).1 = 1 := by omega
      have this : n = (ppPair n).2 := by simpa only [h2, pow_one] using hpe.symm
      have hp' : Nat.Prime n := by rw [this]; exact hp
      exact (Finset.mem_filter.mp hn).2 hp'
    have heM : (ppPair n).1 ≤ Nat.log 2 k := by
      apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
      calc 2 ^ (ppPair n).1 ≤ (ppPair n).2 ^ (ppPair n).1 :=
            Nat.pow_le_pow_left hp.two_le _
        _ = n := hpe
        _ ≤ k := hnk
    have hple : (ppPair n).2 ≤ k := by
      have he1 : 1 ≤ (ppPair n).1 := Nat.one_le_iff_ne_zero.mpr he0.ne'
      calc (ppPair n).2 = (ppPair n).2 ^ 1 := (pow_one _).symm
        _ ≤ (ppPair n).2 ^ (ppPair n).1 := Nat.pow_le_pow_right hp.one_le he1
        _ = n := hpe
        _ ≤ k := hnk
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨he2, heM⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hple),
        hp, by rw [hpe]; exact hnk⟩

  have hsum_le : (∑ q ∈ primePairs k,
        (q.2 : ℝ) ^ q.1 * ((q.1 : ℝ) * Real.log (q.2 : ℝ)) ^ 2)
      ≤ ∑ e ∈ Finset.Icc 2 (Nat.log 2 k), innerSum k e := by
    rw [primePairs, Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro e _
    rw [innerSum]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hp'.1, hp'.2.1.two_le, hp'.2.2⟩
    · intro p hp _
      exact mul_nonneg (pow_nonneg (Nat.cast_nonneg p) e) (sq_nonneg _)

  calc (∑ n ∈ (activeN k).filter (fun n => ¬ Nat.Prime n),
        (Real.log (n : ℝ) - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ))
      = ∑ n ∈ s, (Real.log (n : ℝ) - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ) := by
        rw [hs]
    _ ≤ ∑ n ∈ s, (ppPair n).2 ^ (ppPair n).1
            * ((ppPair n).1 * Real.log (ppPair n).2) ^ 2 / (k : ℝ) ^ 2 :=
        Finset.sum_le_sum hpoint
    _ = ∑ q ∈ s.image ppPair,
          (q.2 : ℝ) ^ q.1 * ((q.1 : ℝ) * Real.log (q.2 : ℝ)) ^ 2 / (k : ℝ) ^ 2 := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ q ∈ primePairs k,
          (q.2 : ℝ) ^ q.1 * ((q.1 : ℝ) * Real.log (q.2 : ℝ)) ^ 2 / (k : ℝ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro q _ _
        exact div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg q.2) q.1)
          (sq_nonneg _)) (sq_nonneg _)
    _ = (∑ q ∈ primePairs k,
          (q.2 : ℝ) ^ q.1 * ((q.1 : ℝ) * Real.log (q.2 : ℝ)) ^ 2) / (k : ℝ) ^ 2 := by
        rw [← Finset.sum_div]
    _ ≤ surcharge k := by
        unfold surcharge
        exact div_le_div_of_nonneg_right hsum_le (sq_nonneg _)




theorem hppTerm_nonneg (n : ℕ) : 0 ≤ hppTerm n := by
  rw [hppTerm]
  split_ifs with hp
  · apply mul_nonneg (sq_nonneg _)
    apply div_nonneg (by positivity)
    have h1 : (1 : ℕ) < n := hp.one_lt
    have : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h1
      linarith
    positivity
  · rfl


theorem summable_hppTerm : Summable hppTerm := by
  have hbase : Summable (fun n : ℕ => (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ 2) :=
    (summable_nat_add_iff 5).mp
      (summable_log_sq_div_sq_tail 4
        (le_of_lt (lt_trans Real.exp_one_lt_d9
          (by norm_num : (2.7182818286 : ℝ) < 4))))
  have hshift : Summable (fun i : ℕ => hppTerm (i + 5)) :=
    Summable.of_nonneg_of_le (fun i => hppTerm_nonneg (i + 5))
      (fun i => hppTerm_le_ratio_mul 4 (by norm_num) (by omega))
      ((summable_nat_add_iff 5).mpr (hbase.mul_left (hppRatio (1 / 4))))
  exact (summable_nat_add_iff 5).mp hshift






theorem activeN_A_nonneg {k n : ℕ} (hn : n ∈ activeN k) (hn4 : 4 ≤ n) :
    0 ≤ Real.log (n : ℝ) - cBin k (k / n) * (n : ℝ) := by
  have hn' := Finset.mem_filter.mp hn
  have hnk : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn'.1)
  have hn0 : 0 < n := by omega
  have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  set m : ℕ := k / n with hm
  have hm1 : 1 ≤ m := Nat.div_pos hnk hn0
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  set b : ℝ := (k : ℝ) / (m : ℝ) with hb
  have hdiv := (Nat.div_eq_iff hn0).mp hm.symm
  have hnle_b : (n : ℝ) ≤ b := by
    rw [hb, le_div_iff₀ hmpos]
    exact_mod_cast (by simpa [mul_comm] using hdiv.1 : n * m ≤ k)
  have hc : cBin k m = Real.log b / b := by
    simp only [cBin, RHLean.GateII.AWGC.Lb, hb]
  have he1 : Real.exp 1 ≤ (n : ℝ) := by
    have h := Real.exp_one_lt_d9
    norm_num at h
    have hn4R : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    linarith
  have he1b : Real.exp 1 ≤ b := le_trans he1 hnle_b
  have hlogdiv : Real.log b / b ≤ Real.log (n : ℝ) / (n : ℝ) :=
    Real.log_div_self_antitoneOn he1 he1b hnle_b
  have hA : 0 ≤ Real.log (n : ℝ) - cBin k m * (n : ℝ) := by
    rw [hc]
    have hrew : Real.log (n : ℝ) - Real.log b / b * (n : ℝ)
        = (n : ℝ) * (Real.log (n : ℝ) / (n : ℝ) - Real.log b / b) := by
      field_simp
    rw [hrew]
    exact mul_nonneg hn0R.le (sub_nonneg.mpr hlogdiv)
  have hcbin : cBin k (k / n) = cBin k m := by rw [← hm]
  rwa [hcbin]




theorem hpp_split_term {k n : ℕ} (hn : n ∈ activeN k) (hnp : ¬ Nat.Prime n) :
    (Lambda n - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ)
      ≤ (Real.log (n : ℝ) - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ)
        + ((((ppPair n).1 : ℝ) - 1) * Real.log ((ppPair n).2 : ℝ)) ^ 2
            / (((ppPair n).2 ^ (ppPair n).1 : ℕ) : ℝ) := by
  have hΛ : Lambda n ≠ 0 := (Finset.mem_filter.mp hn).2.1
  have hpp : IsPrimePow n :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (by simpa [Lambda] using hΛ)
  obtain ⟨hp, he0, hpe⟩ := ppPair_spec hpp
  have hn0R : (0 : ℝ) < (n : ℝ) := by
    have hn2 : 2 ≤ n := IsPrimePow.two_le hpp
    exact_mod_cast (by omega : 0 < n)
  have he2 : 2 ≤ (ppPair n).1 := by
    by_contra h
    have h1 : (ppPair n).1 = 1 := by omega
    have : n = (ppPair n).2 := by simpa only [h1, pow_one] using hpe.symm
    exact hnp (by rw [this]; exact hp)
  have hn4 : 4 ≤ n := by
    rw [← hpe]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ (ppPair n).2 ^ 2 := Nat.pow_le_pow_left hp.two_le 2
      _ ≤ (ppPair n).2 ^ (ppPair n).1 := Nat.pow_le_pow_right hp.one_le he2
  have hA := activeN_A_nonneg hn hn4
  have hD : 0 ≤ (((ppPair n).1 : ℝ) - 1) * Real.log ((ppPair n).2 : ℝ) := by
    apply mul_nonneg
    · have : (2 : ℝ) ≤ ((ppPair n).1 : ℝ) := by exact_mod_cast he2
      linarith
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hpeN : (((ppPair n).2 ^ (ppPair n).1 : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast hpe
  have hpeLog : Real.log (((ppPair n).2 ^ (ppPair n).1 : ℕ) : ℝ) = Real.log (n : ℝ) := by
    rw [hpeN]
  have hsplit := vonMangoldt_sub_sq_le hp he0.ne' (cBin k (k / n)) (by
    rw [hpeLog, hpeN]
    exact mul_nonneg hA hD)
  rw [hpe] at hsplit
  have hsplit' : (Lambda n - cBin k (k / n) * (n : ℝ)) ^ 2
      ≤ (Real.log (n : ℝ) - cBin k (k / n) * (n : ℝ)) ^ 2
        + ((((ppPair n).1 : ℝ) - 1) * Real.log ((ppPair n).2 : ℝ)) ^ 2 := by
    simpa only [Lambda] using hsplit
  rw [hpeN]
  calc (Lambda n - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ)
      ≤ ((Real.log (n : ℝ) - cBin k (k / n) * (n : ℝ)) ^ 2
          + ((((ppPair n).1 : ℝ) - 1) * Real.log ((ppPair n).2 : ℝ)) ^ 2) / (n : ℝ) :=
        div_le_div_of_nonneg_right hsplit' hn0R.le
    _ = (Real.log (n : ℝ) - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ)
        + ((((ppPair n).1 : ℝ) - 1) * Real.log ((ppPair n).2 : ℝ)) ^ 2 / (n : ℝ) := by
        ring






theorem hppHalf_le_surcharge_add_D (k : ℕ) (hk : 4 ≤ k) :
    (∑ n ∈ (activeN k).filter (fun n => ¬ Nat.Prime n),
        (Lambda n - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ))
      ≤ surcharge k
        + ∑ n ∈ (activeN k).filter (fun n => ¬ Nat.Prime n),
            ((((ppPair n).1 : ℝ) - 1) * Real.log ((ppPair n).2 : ℝ)) ^ 2
              / (((ppPair n).2 ^ (ppPair n).1 : ℕ) : ℝ) := by
  have h1 : (∑ n ∈ (activeN k).filter (fun n => ¬ Nat.Prime n),
        (Lambda n - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ))
      ≤ ∑ n ∈ (activeN k).filter (fun n => ¬ Nat.Prime n),
          ((Real.log (n : ℝ) - cBin k (k / n) * (n : ℝ)) ^ 2 / (n : ℝ)
            + ((((ppPair n).1 : ℝ) - 1) * Real.log ((ppPair n).2 : ℝ)) ^ 2
              / (((ppPair n).2 ^ (ppPair n).1 : ℕ) : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    exact hpp_split_term (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
  rw [Finset.sum_add_distrib] at h1
  exact le_trans h1 (add_le_add_left (activeN_Apart_sum_le k hk) _)

end RHLean.GateII.SA



end Inline_GateII_SA

section Inline_GateII_SA_Dpart











open Finset
open scoped BigOperators

namespace RHLean.GateII.SA

open RHLean.GateII.Chain

set_option maxHeartbeats 1000000





theorem hppTerm_sum_range_le {p M : ℕ} (hp : Nat.Prime p) :
    (∑ j ∈ Finset.range M,
        (((j : ℝ) + 1) * Real.log (p : ℝ)) ^ 2 / (p : ℝ) ^ (j + 2))
      ≤ hppTerm p := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hHN := (hpp_prime_series hp1).mul_left ((Real.log (p : ℝ)) ^ 2)
  have hle := hHN.summable.sum_le_tsum (Finset.range M) (fun j _ => by
    apply mul_nonneg (sq_nonneg _)
    apply div_nonneg (sq_nonneg _)
    positivity)
  have hleft : (∑ j ∈ Finset.range M,
        (((j : ℝ) + 1) * Real.log (p : ℝ)) ^ 2 / (p : ℝ) ^ (j + 2))
      = ∑ j ∈ Finset.range M, (Real.log (p : ℝ)) ^ 2
          * (((j : ℝ) + 1) ^ 2 / (p : ℝ) ^ (j + 2)) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hleft, hppTerm, if_pos hp, ← hHN.tsum_eq]
  exact hle




theorem ppPair_exp_range {k n : ℕ} (hn : n ∈ activeN k) (hnp : ¬ Nat.Prime n) :
    2 ≤ (ppPair n).1 ∧ (ppPair n).1 ≤ Nat.log 2 k := by
  have hΛ : Lambda n ≠ 0 := (Finset.mem_filter.mp hn).2.1
  have hpp : IsPrimePow n :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (by simpa [Lambda] using hΛ)
  obtain ⟨hp, _he0, hpe⟩ := ppPair_spec hpp
  have hnk : n ≤ k :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)
  have he2 : 2 ≤ (ppPair n).1 := by
    by_contra h
    have h1 : (ppPair n).1 = 1 := by omega
    have : n = (ppPair n).2 := by simpa only [h1, pow_one] using hpe.symm
    exact hnp (by rw [this]; exact hp)
  have heM : (ppPair n).1 ≤ Nat.log 2 k := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    calc 2 ^ (ppPair n).1 ≤ (ppPair n).2 ^ (ppPair n).1 :=
          Nat.pow_le_pow_left hp.two_le _
      _ = n := hpe
      _ ≤ k := hnk
  exact ⟨he2, heM⟩





noncomputable def Dterm (n : ℕ) : ℝ :=
  ((((ppPair n).1 : ℝ) - 1) * Real.log ((ppPair n).2 : ℝ)) ^ 2
    / (((ppPair n).2 ^ (ppPair n).1 : ℕ) : ℝ)


noncomputable def hppN (k : ℕ) : Finset ℕ :=
  (activeN k).filter (fun n => ¬ Nat.Prime n)


noncomputable def Dsum (k : ℕ) : ℝ := ∑ n ∈ hppN k, Dterm n

theorem hppN_subset {k : ℕ} : hppN k ⊆ activeN k :=
  fun _ hn => (Finset.mem_filter.mp hn).1

theorem hppN_nonprime {k n : ℕ} (hn : n ∈ hppN k) : ¬ Nat.Prime n :=
  (Finset.mem_filter.mp hn).2

theorem hppN_isPrimePow {k n : ℕ} (hn : n ∈ hppN k) : IsPrimePow n := by
  have hΛ : Lambda n ≠ 0 := (Finset.mem_filter.mp (hppN_subset hn)).2.1
  exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (by simpa [Lambda] using hΛ)




theorem Dterm_eq_shift {k n p : ℕ} (hn : n ∈ hppN k) (hp : (ppPair n).2 = p) :
    Dterm n
      = (((((ppPair n).1 - 2 : ℕ) : ℝ) + 1) * Real.log (p : ℝ)) ^ 2
          / (p : ℝ) ^ ((ppPair n).1 - 2 + 2) := by
  have hpp := hppN_isPrimePow hn
  obtain ⟨_hpPr, _he0, _hpe⟩ := ppPair_spec hpp
  have he2 : 2 ≤ (ppPair n).1 :=
    (ppPair_exp_range (hppN_subset hn) (hppN_nonprime hn)).1
  have hcast : (((ppPair n).2 ^ (ppPair n).1 : ℕ) : ℝ)
      = ((ppPair n).2 : ℝ) ^ (ppPair n).1 := by
    push_cast
    ring
  have hexp : ((ppPair n).2 : ℝ) ^ (ppPair n).1
      = (p : ℝ) ^ ((ppPair n).1 - 2 + 2) := by
    rw [Nat.sub_add_cancel he2, hp]
  have hcoef : ((ppPair n).1 : ℝ) - 1
      = (((ppPair n).1 - 2 : ℕ) : ℝ) + 1 := by
    have h1 : (((ppPair n).1 - 2 : ℕ) : ℝ) = ((ppPair n).1 : ℝ) - 2 := by
      rw [Nat.cast_sub he2]
      norm_num
    rw [h1]
    ring
  have hlog : Real.log ((ppPair n).2 : ℝ) = Real.log (p : ℝ) := by rw [hp]
  unfold Dterm
  rw [hcast, hexp, hcoef, hlog]



theorem fiber_injOn {k p : ℕ} :
    Set.InjOn (fun n : ℕ => (ppPair n).1 - 2)
      ((hppN k).filter (fun n => (ppPair n).2 = p)) := by
  intro n1 h1 n2 h2 heq
  have hn1 := Finset.mem_filter.mp h1
  have hn2 := Finset.mem_filter.mp h2
  have he1 : 2 ≤ (ppPair n1).1 :=
    (ppPair_exp_range (hppN_subset hn1.1) (hppN_nonprime hn1.1)).1
  have he2 : 2 ≤ (ppPair n2).1 :=
    (ppPair_exp_range (hppN_subset hn2.1) (hppN_nonprime hn2.1)).1
  have heq' : (ppPair n1).1 - 2 = (ppPair n2).1 - 2 := heq
  have heqexp : (ppPair n1).1 = (ppPair n2).1 := by omega
  have s1 : (ppPair n1).2 ^ (ppPair n1).1 = n1 :=
    (ppPair_spec (hppN_isPrimePow hn1.1)).2.2
  have s2 : (ppPair n2).2 ^ (ppPair n2).1 = n2 :=
    (ppPair_spec (hppN_isPrimePow hn2.1)).2.2
  have hq : (ppPair n1).2 = (ppPair n2).2 := by rw [hn1.2, hn2.2]
  rw [← s1, ← s2, hq, heqexp]



theorem fiber_image_subset {k p : ℕ} :
    (((hppN k).filter (fun n => (ppPair n).2 = p)).image
        (fun n => (ppPair n).1 - 2))
      ⊆ Finset.range (Nat.log 2 k) := by
  intro j hj
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
  have hn' := Finset.mem_filter.mp hn
  obtain ⟨he2, heM⟩ := ppPair_exp_range (hppN_subset hn'.1) (hppN_nonprime hn'.1)
  rw [Finset.mem_range]
  omega




theorem fiber_sum_le_hppTerm {k p : ℕ} (hp : Nat.Prime p) :
    (∑ n ∈ (hppN k).filter (fun n => (ppPair n).2 = p), Dterm n)
      ≤ hppTerm p := by
  have hstep :
      (∑ n ∈ (hppN k).filter (fun n => (ppPair n).2 = p), Dterm n)
        = ∑ n ∈ (hppN k).filter (fun n => (ppPair n).2 = p),
            (((((ppPair n).1 - 2 : ℕ) : ℝ) + 1) * Real.log (p : ℝ)) ^ 2
              / (p : ℝ) ^ ((ppPair n).1 - 2 + 2) := by
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hn
    exact Dterm_eq_shift h1 h2
  rw [hstep,
    ← Finset.sum_image (s := (hppN k).filter (fun n => (ppPair n).2 = p))
      (g := fun n : ℕ => (ppPair n).1 - 2)
      (f := fun j : ℕ =>
        ((((j : ℝ) + 1) * Real.log (p : ℝ)) ^ 2 / (p : ℝ) ^ (j + 2)))
      (fiber_injOn (k := k) (p := p))]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg fiber_image_subset ?_)
    (hppTerm_sum_range_le hp)
  intro j _ _
  exact div_nonneg (sq_nonneg _) (by positivity)



theorem Dsum_le_Hpp (k : ℕ) : Dsum k ≤ Hpp := by
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := hppN k) (t := (hppN k).image (fun n => (ppPair n).2))
    (g := fun n : ℕ => (ppPair n).2) (f := Dterm)
    (fun n hn => Finset.mem_image_of_mem _ hn)
  rw [Dsum, ← hfiber]
  refine le_trans (Finset.sum_le_sum ?_)
    (summable_hppTerm.sum_le_tsum _ (fun p _ => hppTerm_nonneg p))
  intro p hp
  obtain ⟨n, hn, hpn⟩ := Finset.mem_image.mp hp
  have hpPr : Nat.Prime p := by
    rw [← hpn]
    exact (ppPair_spec (hppN_isPrimePow hn)).1
  exact fiber_sum_le_hppTerm hpPr



theorem hppHalf_D_le_Hpp (k : ℕ) :
    (∑ n ∈ (activeN k).filter (fun n => ¬ Nat.Prime n),
        ((((ppPair n).1 : ℝ) - 1) * Real.log ((ppPair n).2 : ℝ)) ^ 2
          / (((ppPair n).2 ^ (ppPair n).1 : ℕ) : ℝ)) ≤ Hpp :=
  Dsum_le_Hpp k

end RHLean.GateII.SA



end Inline_GateII_SA_Dpart

section Inline_GateII_HBoxBase
















open Finset
open scoped Topology

namespace RHLean.GateII.HBoxBase

open RHLean.GateII.Chain





theorem hpp_cert_term_le {p k v : ℕ} (hp : 1 < p)
    (hv : 100 * k ^ 2 * (p + 1) ≤ v * (p - 1) ^ 3) :
    (((k : ℝ) / 10 ^ 5) ^ 2) * (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 3)
      ≤ (v : ℝ) / 10 ^ 12 := by
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp
    linarith
  have h12 : (0 : ℝ) < 10 ^ 12 := by norm_num
  have hvR : (100 : ℝ) * (k : ℝ) ^ 2 * ((p : ℝ) + 1)
      ≤ (v : ℝ) * ((p : ℝ) - 1) ^ 3 := by
    have hp1 : (1 : ℕ) ≤ p := le_of_lt hp
    have hcast1 : ((100 * k ^ 2 * (p + 1) : ℕ) : ℝ)
        = (100 : ℝ) * (k : ℝ) ^ 2 * ((p : ℝ) + 1) := by
      push_cast
      ring
    have hcast2 : ((v * (p - 1) ^ 3 : ℕ) : ℝ)
        = (v : ℝ) * ((p : ℝ) - 1) ^ 3 := by
      push_cast [Nat.cast_sub hp1]
      ring
    calc (100 : ℝ) * (k : ℝ) ^ 2 * ((p : ℝ) + 1)
        = ((100 * k ^ 2 * (p + 1) : ℕ) : ℝ) := hcast1.symm
      _ ≤ ((v * (p - 1) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hv
      _ = (v : ℝ) * ((p : ℝ) - 1) ^ 3 := hcast2
  rw [le_div_iff₀ h12]
  have hA : (((k : ℝ) / 10 ^ 5) ^ 2) * (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 3) * 10 ^ 12
      = (100 * (k : ℝ) ^ 2 * ((p : ℝ) + 1)) / ((p : ℝ) - 1) ^ 3 := by
    field_simp [hden.ne']
    ring
  rw [hA, div_le_iff₀ (pow_pos hden 3)]
  exact hvR





structure HBox where
  p : ℕ
  k : ℕ
  v : ℕ
  N : ℕ
  hp : 0 < p
  hk : 0 ≤ k
  hv : Nat.Prime p → 100 * k ^ 2 * (p + 1) ≤ v * (p - 1) ^ 3
  htaylor : Nat.Prime p →
    (p : ℚ) ≤ ∑ j ∈ Finset.range N, ((k : ℚ) / 10 ^ 5) ^ j / (Nat.factorial j : ℚ)


theorem HBox.sound (b : HBox) (hp : Nat.Prime b.p) :
    Real.log (b.p : ℝ) ≤ (b.k : ℝ) / 10 ^ 5 := by
  have hk : (0 : ℚ) ≤ (b.k : ℚ) / 10 ^ 5 :=
    div_nonneg (by exact_mod_cast b.hk) (by norm_num)
  have h := log_le_of_taylor b.hp hk (b.htaylor hp)
  simpa using h


theorem HBox.term_le (b : HBox) (hp : Nat.Prime b.p) :
    (((b.k : ℝ) / 10 ^ 5) ^ 2) * (((b.p : ℝ) + 1) / ((b.p : ℝ) - 1) ^ 3)
      ≤ (b.v : ℝ) / 10 ^ 12 :=
  hpp_cert_term_le (Nat.Prime.one_lt hp) (b.hv hp)



theorem list_toFinset_sum_le_sum {α : Type*} [DecidableEq α] (l : List α) (f : α → ℝ)
    (hf : ∀ x ∈ l, 0 ≤ f x) : l.toFinset.sum f ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons]
    by_cases ha : a ∈ t
    · have hts : (a :: t).toFinset = t.toFinset := by
        ext x
        simp only [List.mem_toFinset, List.mem_cons]
        constructor
        · rintro (rfl | hx)
          · exact ha
          · exact hx
        · exact Or.inr
      rw [hts]
      exact le_trans (ih (fun x hx => hf x (List.mem_cons_of_mem a hx)))
        (le_add_of_nonneg_left (hf a (by simp)))
    · have hts : (a :: t).toFinset = insert a t.toFinset := by
        ext x
        simp only [List.mem_toFinset, List.mem_cons, Finset.mem_insert]
      rw [hts, Finset.sum_insert (by simpa [List.mem_toFinset] using ha)]
      linarith [ih (fun x hx => hf x (List.mem_cons_of_mem a hx))]


theorem list_sum_map_HBoxV_div (l : List HBox) (D : ℝ) :
    (l.map (fun b => (b.v : ℝ) / D)).sum
      = (((l.map (fun b => b.v)).sum : ℕ) : ℝ) / D := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
    push_cast
    ring





theorem Hpp_lt_of_boxdata
    (P : ℕ) (hP : 4 ≤ P)
    (boxes : List HBox) (vList : List ℕ) (Vtotal : ℕ) (uP : ℚ) (bound : ℝ)
    (hboxes_v : boxes.map (fun b => b.v) = vList)
    (hV : vList.sum ≤ Vtotal)
    (hcover : ∀ p, Nat.Prime p → p ≤ P → ∃ b ∈ boxes, b.p = p)
    (huP : Real.log (P : ℝ) ≤ (uP : ℝ))
    (hfinal : (Vtotal : ℝ) / 10 ^ 12
        + hppRatio (1 / (P : ℝ))
            * ((((uP : ℝ)) ^ 2 + 2 * (uP : ℝ) + 2) / (P : ℝ)) < bound) :
    Hpp < bound := by
  classical
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hPexp : Real.exp 1 ≤ (P : ℝ) := by
    have h3P : (3 : ℝ) ≤ P := by exact_mod_cast (by omega : 3 ≤ P)
    linarith [Real.exp_one_lt_three]
  set C : ℝ := hppRatio (1 / (P : ℝ)) with hCdef
  have hCnonneg : 0 ≤ C := by
    rw [hCdef]
    exact hppRatio_nonneg (by positivity) (by
      rw [div_le_iff₀ hP0]
      have hP4 : (4 : ℝ) ≤ P := by exact_mod_cast hP
      linarith)
  set B : ℝ := ((Real.log (P : ℝ)) ^ 2 + 2 * Real.log (P : ℝ) + 2) / (P : ℝ) with hBdef
  set Bu : ℝ := (((uP : ℝ)) ^ 2 + 2 * (uP : ℝ) + 2) / (P : ℝ) with hBudef
  have hlogP0 : 0 ≤ Real.log (P : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ P))
  have hBle : B ≤ Bu := by
    rw [hBdef, hBudef]
    apply div_le_div_of_nonneg_right _ hP0.le
    have hsq : (Real.log (P : ℝ)) ^ 2 ≤ (uP : ℝ) ^ 2 :=
      pow_le_pow_left₀ hlogP0 huP 2
    linarith
  have hpartial' : ∀ M : ℕ,
      ∑ k ∈ Finset.range M, hppTerm (k + P + 1) ≤ C * Bu := by
    intro M
    calc
      ∑ k ∈ Finset.range M, hppTerm (k + P + 1)
          ≤ ∑ k ∈ Finset.range M,
              C * ((Real.log ((k + P + 1 : ℕ) : ℝ)) ^ 2
                    / ((k + P + 1 : ℕ) : ℝ) ^ 2) := by
            apply Finset.sum_le_sum
            intro k _
            rw [hCdef]
            exact hppTerm_le_ratio_mul P hP (by omega)
      _ = C * ∑ k ∈ Finset.range M,
              (Real.log ((k + P + 1 : ℕ) : ℝ)) ^ 2
                / ((k + P + 1 : ℕ) : ℝ) ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ C * B := by
            exact mul_le_mul_of_nonneg_left (log_sq_div_sq_partial_le P hPexp M) hCnonneg
      _ ≤ C * Bu := mul_le_mul_of_nonneg_left hBle hCnonneg
  have hpartial : ∀ M : ℕ,
      ∑ k ∈ Finset.range M, hppTerm (k + (P + 1)) ≤ C * Bu := by
    intro M
    simpa only [Nat.add_assoc] using hpartial' M
  have hnonneg : ∀ k : ℕ, 0 ≤ hppTerm (k + (P + 1)) := by
    intro k
    rw [hppTerm]
    split_ifs with hk
    · apply mul_nonneg (sq_nonneg _)
      apply div_nonneg
      · positivity
      · have : (1 : ℝ) < (k + (P + 1) : ℕ) := by
          exact_mod_cast (by omega : 1 < k + (P + 1))
        positivity
    · rfl
  have hshift_summ : Summable (fun k : ℕ => hppTerm (k + (P + 1))) :=
    summable_of_sum_range_le hnonneg hpartial
  have hshift_bound : ∑' k : ℕ, hppTerm (k + (P + 1)) ≤ C * Bu :=
    Real.tsum_le_of_sum_range_le hnonneg hpartial
  have hsumm : Summable hppTerm := (summable_nat_add_iff (P + 1)).mp hshift_summ
  have hsplit := hsumm.sum_add_tsum_nat_add (P + 1)
  set S : Finset ℕ := (Finset.range (P + 1)).filter Nat.Prime with hS
  have hcover'
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    exact hcover p hp.2 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp.1))
  have hfiniteS : ∑ p ∈ S,
        (Real.log (p : ℝ)) ^ 2 * (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 3)
      ≤ (Vtotal : ℝ) / 10 ^ 12 := by
    let pickSub : ↥S → HBox := fun p => Classical.choose (hcover' p.1 p.2)
    have hpick_mem : ∀ p : ↥S, pickSub p ∈ boxes :=
      fun p => (Classical.choose_spec (hcover' p.1 p.2)).1
    have hpick_p : ∀ p : ↥S, (pickSub p).p = p.1 :=
      fun p => (Classical.choose_spec (hcover' p.1 p.2)).2
    have hpick_inj : Function.Injective pickSub := by
      intro p q hpq
      apply Subtype.ext
      rw [← hpick_p p, ← hpick_p q, hpq]
    calc
      ∑ p ∈ S, (Real.log (p : ℝ)) ^ 2 * (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 3)
          = ∑ p ∈ S.attach,
              (Real.log (p.1 : ℝ)) ^ 2 * (((p.1 : ℝ) + 1) / ((p.1 : ℝ) - 1) ^ 3) := by
            exact (Finset.sum_attach S (fun p : ℕ =>
              (Real.log (p : ℝ)) ^ 2
                * (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 3))).symm
      _ ≤ ∑ p ∈ S.attach, ((pickSub p).v : ℝ) / 10 ^ 12 := by
            apply Finset.sum_le_sum
            intro p _
            have hpprime : Nat.Prime p.1 := (Finset.mem_filter.1 p.2).2
            have hsnd : Real.log ((pickSub p).p : ℝ) ≤ ((pickSub p).k : ℝ) / 10 ^ 5 := by
              apply HBox.sound
              rwa [hpick_p p]
            rw [hpick_p p] at hsnd
            have hlog0 : 0 ≤ Real.log (p.1 : ℝ) :=
              Real.log_nonneg (by exact_mod_cast hpprime.one_le)
            have hsq : (Real.log (p.1 : ℝ)) ^ 2
                ≤ (((pickSub p).k : ℝ) / 10 ^ 5) ^ 2 :=
              pow_le_pow_left₀ hlog0 hsnd 2
            have hc : 0 ≤ ((p.1 : ℝ) + 1) / ((p.1 : ℝ) - 1) ^ 3 := by
              apply div_nonneg
              · positivity
              · have : (1 : ℝ) < p.1 := by exact_mod_cast hpprime.one_lt
                positivity
            have hterm : ((((pickSub p).k : ℝ) / 10 ^ 5) ^ 2)
                * ((((pickSub p).p : ℝ) + 1) / (((pickSub p).p : ℝ) - 1) ^ 3)
                ≤ ((pickSub p).v : ℝ) / 10 ^ 12 := by
              apply HBox.term_le
              rwa [hpick_p p]
            rw [hpick_p p] at hterm
            exact le_trans (mul_le_mul_of_nonneg_right hsq hc) hterm
      _ = ∑ b ∈ S.attach.image pickSub, (b.v : ℝ) / 10 ^ 12 := by
            rw [Finset.sum_image]
            intro x _ y _ hxy
            exact hpick_inj hxy
      _ ≤ ∑ b ∈ boxes.toFinset, (b.v : ℝ) / 10 ^ 12 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro b hb
              rw [Finset.mem_image] at hb
              obtain ⟨p, _, rfl⟩ := hb
              exact List.mem_toFinset.2 (hpick_mem p)
            · intro b _ _
              positivity
      _ ≤ ((vList.sum : ℕ) : ℝ) / 10 ^ 12 := by
            have h1 := list_toFinset_sum_le_sum boxes
              (fun b => (b.v : ℝ) / 10 ^ 12) (fun b _ => by positivity)
            rw [list_sum_map_HBoxV_div] at h1
            have h2 : ((boxes.map (fun b => b.v)).sum : ℕ) = vList.sum := by rw [hboxes_v]
            rw [h2] at h1
            exact h1
      _ ≤ (Vtotal : ℝ) / 10 ^ 12 := by
            exact div_le_div_of_nonneg_right (by exact_mod_cast hV) (by norm_num)
  have hfinite_range : ∑ p ∈ Finset.range (P + 1), hppTerm p
      ≤ (Vtotal : ℝ) / 10 ^ 12 := by
    have hfin_eq : (∑ p ∈ Finset.range (P + 1), hppTerm p)
        = ∑ p ∈ S,
            (Real.log (p : ℝ)) ^ 2 * (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 3) := by
      rw [hS, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      rw [hppTerm]
    rw [hfin_eq]
    exact hfiniteS
  rw [Hpp, ← hsplit]
  linarith [hfinite_range, hshift_bound, hfinal]

end RHLean.GateII.HBoxBase



end Inline_GateII_HBoxBase

section Inline_GateII_HBoxData_0



set_option maxRecDepth 10000

namespace RHLean.GateII.HBoxDataChunk

open RHLean.GateII.HBoxBase

set_option maxHeartbeats 2000000 in
private def hbox_0_0__GateII_HBoxData_0 : HBox :=
  { p := 1, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp Nat.not_prime_one, htaylor := fun hp => absurd hp Nat.not_prime_one }

set_option maxHeartbeats 2000000 in
private def hbox_0_1__GateII_HBoxData_0 : HBox :=
  { p := 2, k := 69316, v := 1441412356800, N := 9, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_2__GateII_HBoxData_0 : HBox :=
  { p := 3, k := 109863, v := 603493938450, N := 11, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_3__GateII_HBoxData_0 : HBox :=
  { p := 4, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 4 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 4 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_4__GateII_HBoxData_0 : HBox :=
  { p := 5, k := 160945, v := 242843372110, N := 12, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_5__GateII_HBoxData_0 : HBox :=
  { p := 6, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 6 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 6 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_6__GateII_HBoxData_0 : HBox :=
  { p := 7, k := 194593, v := 140246057960, N := 13, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_7__GateII_HBoxData_0 : HBox :=
  { p := 8, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 8 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 8 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_8__GateII_HBoxData_0 : HBox :=
  { p := 9, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 9 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 9 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_9__GateII_HBoxData_0 : HBox :=
  { p := 10, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 10 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 10 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_10__GateII_HBoxData_0 : HBox :=
  { p := 11, k := 239791, v := 68999668418, N := 14, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_11__GateII_HBoxData_0 : HBox :=
  { p := 12, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 12 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 12 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_12__GateII_HBoxData_0 : HBox :=
  { p := 13, k := 256496, v := 53302243763, N := 15, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_13__GateII_HBoxData_0 : HBox :=
  { p := 14, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 14 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 14 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_14__GateII_HBoxData_0 : HBox :=
  { p := 15, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 15 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 15 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_15__GateII_HBoxData_0 : HBox :=
  { p := 16, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 16 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 16 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_16__GateII_HBoxData_0 : HBox :=
  { p := 17, k := 283323, v := 35275747118, N := 15, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_17__GateII_HBoxData_0 : HBox :=
  { p := 18, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 18 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 18 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_18__GateII_HBoxData_0 : HBox :=
  { p := 19, k := 294445, v := 29731775729, N := 16, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_19__GateII_HBoxData_0 : HBox :=
  { p := 20, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 20 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 20 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_20__GateII_HBoxData_0 : HBox :=
  { p := 21, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 21 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 21 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_21__GateII_HBoxData_0 : HBox :=
  { p := 22, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 22 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 22 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_22__GateII_HBoxData_0 : HBox :=
  { p := 23, k := 313551, v := 22159480752, N := 16, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_23__GateII_HBoxData_0 : HBox :=
  { p := 24, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 24 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 24 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_24__GateII_HBoxData_0 : HBox :=
  { p := 25, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 5 ∣ 25 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 5 ∣ 25 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_25__GateII_HBoxData_0 : HBox :=
  { p := 26, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 26 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 26 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_26__GateII_HBoxData_0 : HBox :=
  { p := 27, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 27 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 27 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_27__GateII_HBoxData_0 : HBox :=
  { p := 28, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 28 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 28 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_28__GateII_HBoxData_0 : HBox :=
  { p := 29, k := 336731, v := 15495777109, N := 16, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_29__GateII_HBoxData_0 : HBox :=
  { p := 30, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 30 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 30 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_30__GateII_HBoxData_0 : HBox :=
  { p := 31, k := 343400, v := 13976125630, N := 17, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_31__GateII_HBoxData_0 : HBox :=
  { p := 32, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 32 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 32 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_32__GateII_HBoxData_0 : HBox :=
  { p := 33, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 33 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 33 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_33__GateII_HBoxData_0 : HBox :=
  { p := 34, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 34 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 34 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_34__GateII_HBoxData_0 : HBox :=
  { p := 35, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 5 ∣ 35 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 5 ∣ 35 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_35__GateII_HBoxData_0 : HBox :=
  { p := 36, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 36 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 36 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_36__GateII_HBoxData_0 : HBox :=
  { p := 37, k := 361093, v := 10619748536, N := 17, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_37__GateII_HBoxData_0 : HBox :=
  { p := 38, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 38 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 38 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_38__GateII_HBoxData_0 : HBox :=
  { p := 39, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 39 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 39 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_39__GateII_HBoxData_0 : HBox :=
  { p := 40, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 40 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 40 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_40__GateII_HBoxData_0 : HBox :=
  { p := 41, k := 371359, v := 9050180140, N := 17, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_41__GateII_HBoxData_0 : HBox :=
  { p := 42, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 42 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 42 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_42__GateII_HBoxData_0 : HBox :=
  { p := 43, k := 376122, v := 8401605376, N := 17, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_43__GateII_HBoxData_0 : HBox :=
  { p := 44, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 44 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 44 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_44__GateII_HBoxData_0 : HBox :=
  { p := 45, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 45 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 45 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_45__GateII_HBoxData_0 : HBox :=
  { p := 46, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 46 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 46 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_46__GateII_HBoxData_0 : HBox :=
  { p := 47, k := 385016, v := 7310133325, N := 18, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_47__GateII_HBoxData_0 : HBox :=
  { p := 48, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 48 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 48 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_48__GateII_HBoxData_0 : HBox :=
  { p := 49, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 7 ∣ 49 := by decide
      rcases hp.eq_one_or_self_of_dvd 7 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 7 ∣ 49 := by decide
      rcases hp.eq_one_or_self_of_dvd 7 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_49__GateII_HBoxData_0 : HBox :=
  { p := 50, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 50 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 50 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_50__GateII_HBoxData_0 : HBox :=
  { p := 51, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 51 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 51 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_51__GateII_HBoxData_0 : HBox :=
  { p := 52, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 52 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 52 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_52__GateII_HBoxData_0 : HBox :=
  { p := 53, k := 397031, v := 6053862660, N := 18, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_53__GateII_HBoxData_0 : HBox :=
  { p := 54, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 54 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 54 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_54__GateII_HBoxData_0 : HBox :=
  { p := 55, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 5 ∣ 55 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 5 ∣ 55 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_55__GateII_HBoxData_0 : HBox :=
  { p := 56, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 56 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 56 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_56__GateII_HBoxData_0 : HBox :=
  { p := 57, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 57 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 57 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_57__GateII_HBoxData_0 : HBox :=
  { p := 58, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 58 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 58 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_58__GateII_HBoxData_0 : HBox :=
  { p := 59, k := 407755, v := 5112883063, N := 18, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_59__GateII_HBoxData_0 : HBox :=
  { p := 60, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 60 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 60 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_60__GateII_HBoxData_0 : HBox :=
  { p := 61, k := 411089, v := 4850758467, N := 18, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_61__GateII_HBoxData_0 : HBox :=
  { p := 62, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 62 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 62 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_62__GateII_HBoxData_0 : HBox :=
  { p := 63, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 63 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 63 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_63__GateII_HBoxData_0 : HBox :=
  { p := 64, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 64 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 64 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_64__GateII_HBoxData_0 : HBox :=
  { p := 65, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 5 ∣ 65 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 5 ∣ 65 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_65__GateII_HBoxData_0 : HBox :=
  { p := 66, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 66 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 66 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_66__GateII_HBoxData_0 : HBox :=
  { p := 67, k := 420471, v := 4181664652, N := 18, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_67__GateII_HBoxData_0 : HBox :=
  { p := 68, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 68 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 68 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_68__GateII_HBoxData_0 : HBox :=
  { p := 69, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 69 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 69 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_69__GateII_HBoxData_0 : HBox :=
  { p := 70, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 70 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 70 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_70__GateII_HBoxData_0 : HBox :=
  { p := 71, k := 426269, v := 3814221209, N := 19, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_71__GateII_HBoxData_0 : HBox :=
  { p := 72, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 72 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 72 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_72__GateII_HBoxData_0 : HBox :=
  { p := 73, k := 429047, v := 3649589091, N := 19, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_73__GateII_HBoxData_0 : HBox :=
  { p := 74, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 74 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 74 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_74__GateII_HBoxData_0 : HBox :=
  { p := 75, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 75 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 75 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_75__GateII_HBoxData_0 : HBox :=
  { p := 76, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 76 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 76 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_76__GateII_HBoxData_0 : HBox :=
  { p := 77, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 7 ∣ 77 := by decide
      rcases hp.eq_one_or_self_of_dvd 7 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 7 ∣ 77 := by decide
      rcases hp.eq_one_or_self_of_dvd 7 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_77__GateII_HBoxData_0 : HBox :=
  { p := 78, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 78 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 78 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_78__GateII_HBoxData_0 : HBox :=
  { p := 79, k := 436946, v := 3218560781, N := 19, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_79__GateII_HBoxData_0 : HBox :=
  { p := 80, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 80 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 80 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_80__GateII_HBoxData_0 : HBox :=
  { p := 81, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 81 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 81 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_81__GateII_HBoxData_0 : HBox :=
  { p := 82, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 82 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 82 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_82__GateII_HBoxData_0 : HBox :=
  { p := 83, k := 441886, v := 2974803019, N := 18, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_83__GateII_HBoxData_0 : HBox :=
  { p := 84, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 84 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 84 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_84__GateII_HBoxData_0 : HBox :=
  { p := 85, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 5 ∣ 85 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 5 ∣ 85 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_85__GateII_HBoxData_0 : HBox :=
  { p := 86, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 86 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 86 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_86__GateII_HBoxData_0 : HBox :=
  { p := 87, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 87 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 87 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_87__GateII_HBoxData_0 : HBox :=
  { p := 88, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 88 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 88 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_88__GateII_HBoxData_0 : HBox :=
  { p := 89, k := 448865, v := 2660884225, N := 19, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_89__GateII_HBoxData_0 : HBox :=
  { p := 90, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 90 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 90 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_90__GateII_HBoxData_0 : HBox :=
  { p := 91, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 7 ∣ 91 := by decide
      rcases hp.eq_one_or_self_of_dvd 7 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 7 ∣ 91 := by decide
      rcases hp.eq_one_or_self_of_dvd 7 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_91__GateII_HBoxData_0 : HBox :=
  { p := 92, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 92 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 92 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_92__GateII_HBoxData_0 : HBox :=
  { p := 93, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 93 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 93 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_93__GateII_HBoxData_0 : HBox :=
  { p := 94, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 94 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 94 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_94__GateII_HBoxData_0 : HBox :=
  { p := 95, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 5 ∣ 95 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 5 ∣ 95 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_95__GateII_HBoxData_0 : HBox :=
  { p := 96, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 96 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 96 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_96__GateII_HBoxData_0 : HBox :=
  { p := 97, k := 457473, v := 2318159483, N := 19, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_97__GateII_HBoxData_0 : HBox :=
  { p := 98, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 98 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 98 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_98__GateII_HBoxData_0 : HBox :=
  { p := 99, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 99 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 99 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_99__GateII_HBoxData_0 : HBox :=
  { p := 100, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 100 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 100 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_100__GateII_HBoxData_0 : HBox :=
  { p := 101, k := 461514, v := 2172550757, N := 19, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_101__GateII_HBoxData_0 : HBox :=
  { p := 102, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 102 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 102 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_102__GateII_HBoxData_0 : HBox :=
  { p := 103, k := 463474, v := 2105152568, N := 19, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_103__GateII_HBoxData_0 : HBox :=
  { p := 104, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 104 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 104 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_104__GateII_HBoxData_0 : HBox :=
  { p := 105, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 105 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 105 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_105__GateII_HBoxData_0 : HBox :=
  { p := 106, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 106 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 106 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_106__GateII_HBoxData_0 : HBox :=
  { p := 107, k := 467284, v := 1980012726, N := 19, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_107__GateII_HBoxData_0 : HBox :=
  { p := 108, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 108 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 108 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_108__GateII_HBoxData_0 : HBox :=
  { p := 109, k := 469136, v := 1921847575, N := 19, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_109__GateII_HBoxData_0 : HBox :=
  { p := 110, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 110 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 110 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_110__GateII_HBoxData_0 : HBox :=
  { p := 111, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 111 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 111 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_111__GateII_HBoxData_0 : HBox :=
  { p := 112, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 112 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 112 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_112__GateII_HBoxData_0 : HBox :=
  { p := 113, k := 472740, v := 1813407824, N := 19, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_113__GateII_HBoxData_0 : HBox :=
  { p := 114, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 114 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 114 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_114__GateII_HBoxData_0 : HBox :=
  { p := 115, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 5 ∣ 115 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 5 ∣ 115 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_115__GateII_HBoxData_0 : HBox :=
  { p := 116, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 116 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 116 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_116__GateII_HBoxData_0 : HBox :=
  { p := 117, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 117 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 117 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_117__GateII_HBoxData_0 : HBox :=
  { p := 118, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 118 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 118 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_118__GateII_HBoxData_0 : HBox :=
  { p := 119, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 7 ∣ 119 := by decide
      rcases hp.eq_one_or_self_of_dvd 7 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 7 ∣ 119 := by decide
      rcases hp.eq_one_or_self_of_dvd 7 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_119__GateII_HBoxData_0 : HBox :=
  { p := 120, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 120 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 120 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_120__GateII_HBoxData_0 : HBox :=
  { p := 121, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 11 ∣ 121 := by decide
      rcases hp.eq_one_or_self_of_dvd 11 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 11 ∣ 121 := by decide
      rcases hp.eq_one_or_self_of_dvd 11 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_121__GateII_HBoxData_0 : HBox :=
  { p := 122, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 122 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 122 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_122__GateII_HBoxData_0 : HBox :=
  { p := 123, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 123 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 123 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_123__GateII_HBoxData_0 : HBox :=
  { p := 124, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 124 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 124 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_124__GateII_HBoxData_0 : HBox :=
  { p := 125, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 5 ∣ 125 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 5 ∣ 125 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_125__GateII_HBoxData_0 : HBox :=
  { p := 126, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 126 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 126 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_126__GateII_HBoxData_0 : HBox :=
  { p := 127, k := 484420, v := 1501559220, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_127__GateII_HBoxData_0 : HBox :=
  { p := 128, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 128 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 128 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_128__GateII_HBoxData_0 : HBox :=
  { p := 129, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 129 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 129 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_129__GateII_HBoxData_0 : HBox :=
  { p := 130, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 130 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 130 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_130__GateII_HBoxData_0 : HBox :=
  { p := 131, k := 487521, v := 1428007636, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_131__GateII_HBoxData_0 : HBox :=
  { p := 132, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 132 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 132 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_132__GateII_HBoxData_0 : HBox :=
  { p := 133, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 7 ∣ 133 := by decide
      rcases hp.eq_one_or_self_of_dvd 7 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 7 ∣ 133 := by decide
      rcases hp.eq_one_or_self_of_dvd 7 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_133__GateII_HBoxData_0 : HBox :=
  { p := 134, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 134 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 134 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_134__GateII_HBoxData_0 : HBox :=
  { p := 135, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 135 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 135 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_135__GateII_HBoxData_0 : HBox :=
  { p := 136, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 136 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 136 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_136__GateII_HBoxData_0 : HBox :=
  { p := 137, k := 492000, v := 1327983157, N := 19, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_137__GateII_HBoxData_0 : HBox :=
  { p := 138, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 138 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 138 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_138__GateII_HBoxData_0 : HBox :=
  { p := 139, k := 493449, v := 1297105566, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_139__GateII_HBoxData_0 : HBox :=
  { p := 140, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 140 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 140 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_140__GateII_HBoxData_0 : HBox :=
  { p := 141, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 141 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 141 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_141__GateII_HBoxData_0 : HBox :=
  { p := 142, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 142 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 142 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_142__GateII_HBoxData_0 : HBox :=
  { p := 143, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 11 ∣ 143 := by decide
      rcases hp.eq_one_or_self_of_dvd 11 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 11 ∣ 143 := by decide
      rcases hp.eq_one_or_self_of_dvd 11 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_143__GateII_HBoxData_0 : HBox :=
  { p := 144, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 144 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 144 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_144__GateII_HBoxData_0 : HBox :=
  { p := 145, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 5 ∣ 145 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 5 ∣ 145 := by decide
      rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_145__GateII_HBoxData_0 : HBox :=
  { p := 146, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 146 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 146 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_146__GateII_HBoxData_0 : HBox :=
  { p := 147, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 3 ∣ 147 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 3 ∣ 147 := by decide
      rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_147__GateII_HBoxData_0 : HBox :=
  { p := 148, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 148 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 148 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_148__GateII_HBoxData_0 : HBox :=
  { p := 149, k := 500396, v := 1158600661, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_149__GateII_HBoxData_0 : HBox :=
  { p := 150, k := 0, v := 0, N := 0, hp := by norm_num, hk := by norm_num, hv := fun hp => absurd hp (by
      have hd : 2 ∣ 150 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega), htaylor := fun hp => absurd hp (by
      have hd : 2 ∣ 150 := by decide
      rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega) }

set_option maxHeartbeats 2000000 in
private def hbox_0_150__GateII_HBoxData_0 : HBox :=
  { p := 151, k := 501729, v := 1133726294, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_151__GateII_HBoxData_0 : HBox :=
  { p := 157, k := 505626, v := 1064001127, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_152__GateII_HBoxData_0 : HBox :=
  { p := 163, k := 509377, v := 1000869528, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_153__GateII_HBoxData_0 : HBox :=
  { p := 167, k := 511801, v := 962027038, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_154__GateII_HBoxData_0 : HBox :=
  { p := 173, k := 515331, v := 908105790, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_155__GateII_HBoxData_0 : HBox :=
  { p := 179, k := 518740, v := 858839428, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_156__GateII_HBoxData_0 : HBox :=
  { p := 181, k := 519851, v := 843357362, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_157__GateII_HBoxData_0 : HBox :=
  { p := 191, k := 525229, v := 772214266, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_158__GateII_HBoxData_0 : HBox :=
  { p := 193, k := 526271, v := 759131342, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_159__GateII_HBoxData_0 : HBox :=
  { p := 197, k := 528322, v := 733997140, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_160__GateII_HBoxData_0 : HBox :=
  { p := 199, k := 529332, v := 721922743, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_161__GateII_HBoxData_0 : HBox :=
  { p := 211, k := 535187, v := 655675700, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_162__GateII_HBoxData_0 : HBox :=
  { p := 223, k := 540719, v := 598593995, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_163__GateII_HBoxData_0 : HBox :=
  { p := 227, k := 542497, v := 581305205, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_164__GateII_HBoxData_0 : HBox :=
  { p := 229, k := 543374, v := 572955646, N := 20, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_165__GateII_HBoxData_0 : HBox :=
  { p := 233, k := 545105, v := 556816677, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_166__GateII_HBoxData_0 : HBox :=
  { p := 239, k := 547648, v := 533928844, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_167__GateII_HBoxData_0 : HBox :=
  { p := 241, k := 548481, v := 526629056, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_168__GateII_HBoxData_0 : HBox :=
  { p := 251, k := 552547, v := 492401045, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_169__GateII_HBoxData_0 : HBox :=
  { p := 257, k := 554909, v := 473525474, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_170__GateII_HBoxData_0 : HBox :=
  { p := 263, k := 557217, v := 455773184, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_171__GateII_HBoxData_0 : HBox :=
  { p := 269, k := 559473, v := 439053706, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_172__GateII_HBoxData_0 : HBox :=
  { p := 271, k := 560213, v := 433694563, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_173__GateII_HBoxData_0 : HBox :=
  { p := 277, k := 562403, v := 418227713, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_174__GateII_HBoxData_0 : HBox :=
  { p := 281, k := 563837, v := 408396638, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_175__GateII_HBoxData_0 : HBox :=
  { p := 283, k := 564546, v := 403617218, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_176__GateII_HBoxData_0 : HBox :=
  { p := 293, k := 568019, v := 380999585, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_177__GateII_HBoxData_0 : HBox :=
  { p := 307, k := 572686, v := 352549068, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_178__GateII_HBoxData_0 : HBox :=
  { p := 311, k := 573981, v := 345036108, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_179__GateII_HBoxData_0 : HBox :=
  { p := 313, k := 574622, v := 341373941, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_180__GateII_HBoxData_0 : HBox :=
  { p := 317, k := 575892, v := 334231951, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_181__GateII_HBoxData_0 : HBox :=
  { p := 331, k := 580213, v := 311007724, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_182__GateII_HBoxData_0 : HBox :=
  { p := 337, k := 582010, v := 301828164, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_183__GateII_HBoxData_0 : HBox :=
  { p := 347, k := 584934, v := 287451567, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_184__GateII_HBoxData_0 : HBox :=
  { p := 349, k := 585509, v := 284706553, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_185__GateII_HBoxData_0 : HBox :=
  { p := 353, k := 586648, v := 279338284, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_186__GateII_HBoxData_0 : HBox :=
  { p := 359, k := 588334, v := 271582209, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_187__GateII_HBoxData_0 : HBox :=
  { p := 367, k := 590538, v := 261758179, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_188__GateII_HBoxData_0 : HBox :=
  { p := 373, k := 592159, v := 254753085, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_189__GateII_HBoxData_0 : HBox :=
  { p := 379, k := 593755, v := 248040591, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_190__GateII_HBoxData_0 : HBox :=
  { p := 383, k := 594805, v := 243719544, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_191__GateII_HBoxData_0 : HBox :=
  { p := 389, k := 596359, v := 237457006, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_192__GateII_HBoxData_0 : HBox :=
  { p := 397, k := 598395, v := 229495105, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_193__GateII_HBoxData_0 : HBox :=
  { p := 401, k := 599398, v := 225671471, N := 21, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_194__GateII_HBoxData_0 : HBox :=
  { p := 409, k := 601373, v := 218318842, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_195__GateII_HBoxData_0 : HBox :=
  { p := 419, k := 603789, v := 209648056, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_196__GateII_HBoxData_0 : HBox :=
  { p := 421, k := 604265, v := 207978988, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_197__GateII_HBoxData_0 : HBox :=
  { p := 431, k := 606612, v := 199940317, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_198__GateII_HBoxData_0 : HBox :=
  { p := 433, k := 607075, v := 198391558, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_199__GateII_HBoxData_0 : HBox :=
  { p := 439, k := 608451, v := 193857034, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_200__GateII_HBoxData_0 : HBox :=
  { p := 443, k := 609358, v := 190924296, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_201__GateII_HBoxData_0 : HBox :=
  { p := 449, k := 610704, v := 186655161, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_202__GateII_HBoxData_0 : HBox :=
  { p := 457, k := 612470, v := 181192657, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_203__GateII_HBoxData_0 : HBox :=
  { p := 461, k := 613341, v := 178555189, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_204__GateII_HBoxData_0 : HBox :=
  { p := 463, k := 613774, v := 177259300, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_205__GateII_HBoxData_0 : HBox :=
  { p := 467, k := 614634, v := 174711409, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_206__GateII_HBoxData_0 : HBox :=
  { p := 479, k := 617172, v := 167405599, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_207__GateII_HBoxData_0 : HBox :=
  { p := 487, k := 618828, v := 162798698, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_208__GateII_HBoxData_0 : HBox :=
  { p := 491, k := 619646, v := 160569910, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_209__GateII_HBoxData_0 : HBox :=
  { p := 499, k := 621262, v := 156254149, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_210__GateII_HBoxData_0 : HBox :=
  { p := 503, k := 622061, v := 154164839, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_211__GateII_HBoxData_0 : HBox :=
  { p := 509, k := 623246, v := 151111682, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_212__GateII_HBoxData_0 : HBox :=
  { p := 521, k := 625577, v := 145285415, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_213__GateII_HBoxData_0 : HBox :=
  { p := 523, k := 625960, v := 144348722, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_214__GateII_HBoxData_0 : HBox :=
  { p := 541, k := 629343, v := 136330435, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_215__GateII_HBoxData_0 : HBox :=
  { p := 547, k := 630446, v := 133813034, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_216__GateII_HBoxData_0 : HBox :=
  { p := 557, k := 632258, v := 129777228, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_217__GateII_HBoxData_0 : HBox :=
  { p := 563, k := 633329, v := 127446792, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_218__GateII_HBoxData_0 : HBox :=
  { p := 569, k := 634390, v := 125182179, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_219__GateII_HBoxData_0 : HBox :=
  { p := 571, k := 634740, v := 124440916, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_220__GateII_HBoxData_0 : HBox :=
  { p := 577, k := 635786, v := 122259414, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_221__GateII_HBoxData_0 : HBox :=
  { p := 587, k := 637504, v := 118754564, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_222__GateII_HBoxData_0 : HBox :=
  { p := 593, k := 638521, v := 116727100, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_223__GateII_HBoxData_0 : HBox :=
  { p := 599, k := 639528, v := 114753734, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_224__GateII_HBoxData_0 : HBox :=
  { p := 601, k := 639861, v := 114107456, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_225__GateII_HBoxData_0 : HBox :=
  { p := 607, k := 640854, v := 112202855, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_226__GateII_HBoxData_0 : HBox :=
  { p := 613, k := 641838, v := 110348125, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_227__GateII_HBoxData_0 : HBox :=
  { p := 617, k := 642488, v := 109138098, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_228__GateII_HBoxData_0 : HBox :=
  { p := 619, k := 642812, v := 108541100, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_229__GateII_HBoxData_0 : HBox :=
  { p := 631, k := 644732, v := 105063989, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_230__GateII_HBoxData_0 : HBox :=
  { p := 641, k := 646304, v := 102298389, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_231__GateII_HBoxData_0 : HBox :=
  { p := 643, k := 646616, v := 101759199, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_232__GateII_HBoxData_0 : HBox :=
  { p := 647, k := 647236, v := 100693812, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_233__GateII_HBoxData_0 : HBox :=
  { p := 653, k := 648159, v := 99128395, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_234__GateII_HBoxData_0 : HBox :=
  { p := 659, k := 649074, v := 97601093, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_235__GateII_HBoxData_0 : HBox :=
  { p := 661, k := 649377, v := 97100170, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_236__GateII_HBoxData_0 : HBox :=
  { p := 673, k := 651176, v := 94177867, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_237__GateII_HBoxData_0 : HBox :=
  { p := 677, k := 651769, v := 93234578, N := 22, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_238__GateII_HBoxData_0 : HBox :=
  { p := 683, k := 652651, v := 91847004, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_239__GateII_HBoxData_0 : HBox :=
  { p := 691, k := 653815, v := 90046862, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_240__GateII_HBoxData_0 : HBox :=
  { p := 701, k := 655252, v := 87873860, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_241__GateII_HBoxData_0 : HBox :=
  { p := 709, k := 656387, v := 86194295, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_242__GateII_HBoxData_0 : HBox :=
  { p := 719, k := 657788, v := 84164909, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_243__GateII_HBoxData_0 : HBox :=
  { p := 727, k := 658894, v := 82594785, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_244__GateII_HBoxData_0 : HBox :=
  { p := 733, k := 659716, v := 81447330, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_245__GateII_HBoxData_0 : HBox :=
  { p := 739, k := 660531, v := 80324688, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_246__GateII_HBoxData_0 : HBox :=
  { p := 743, k := 661071, v := 79589804, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_247__GateII_HBoxData_0 : HBox :=
  { p := 751, k := 662142, v := 78151321, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_248__GateII_HBoxData_0 : HBox :=
  { p := 757, k := 662938, v := 77099161, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_249__GateII_HBoxData_0 : HBox :=
  { p := 761, k := 663465, v := 76410006, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_250__GateII_HBoxData_0 : HBox :=
  { p := 769, k := 664511, v := 75060494, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_251__GateII_HBoxData_0 : HBox :=
  { p := 773, k := 665029, v := 74399537, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_252__GateII_HBoxData_0 : HBox :=
  { p := 787, k := 666824, v := 72157425, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_253__GateII_HBoxData_0 : HBox :=
  { p := 797, k := 668087, v := 70620328, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_254__GateII_HBoxData_0 : HBox :=
  { p := 809, k := 669581, v := 68842587, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_255__GateII_HBoxData_0 : HBox :=
  { p := 811, k := 669828, v := 68553175, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_256__GateII_HBoxData_0 : HBox :=
  { p := 821, k := 671054, v := 67134414, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_257__GateII_HBoxData_0 : HBox :=
  { p := 823, k := 671297, v := 66856121, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_258__GateII_HBoxData_0 : HBox :=
  { p := 827, k := 671782, v := 66305098, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_259__GateII_HBoxData_0 : HBox :=
  { p := 829, k := 672024, v := 66032335, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_260__GateII_HBoxData_0 : HBox :=
  { p := 839, k := 673223, v := 64694167, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_261__GateII_HBoxData_0 : HBox :=
  { p := 853, k := 674877, v := 62890977, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_262__GateII_HBoxData_0 : HBox :=
  { p := 857, k := 675345, v := 62390343, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_263__GateII_HBoxData_0 : HBox :=
  { p := 859, k := 675578, v := 62142338, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_264__GateII_HBoxData_0 : HBox :=
  { p := 863, k := 676043, v := 61651066, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_265__GateII_HBoxData_0 : HBox :=
  { p := 877, k := 677652, v := 59978507, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_266__GateII_HBoxData_0 : HBox :=
  { p := 881, k := 678107, v := 59513710, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_267__GateII_HBoxData_0 : HBox :=
  { p := 883, k := 678334, v := 59283479, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_268__GateII_HBoxData_0 : HBox :=
  { p := 887, k := 678786, v := 58827116, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_269__GateII_HBoxData_0 : HBox :=
  { p := 907, k := 681016, v := 56626001, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_270__GateII_HBoxData_0 : HBox :=
  { p := 911, k := 681456, v := 56201293, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_271__GateII_HBoxData_0 : HBox :=
  { p := 919, k := 682330, v := 55366710, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_272__GateII_HBoxData_0 : HBox :=
  { p := 929, k := 683412, v := 54350585, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_273__GateII_HBoxData_0 : HBox :=
  { p := 937, k := 684270, v := 53558733, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_274__GateII_HBoxData_0 : HBox :=
  { p := 941, k := 684696, v := 53169543, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_275__GateII_HBoxData_0 : HBox :=
  { p := 947, k := 685331, v := 52593938, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_276__GateII_HBoxData_0 : HBox :=
  { p := 953, k := 685963, v := 52028214, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_277__GateII_HBoxData_0 : HBox :=
  { p := 967, k := 687421, v := 50744570, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_278__GateII_HBoxData_0 : HBox :=
  { p := 971, k := 687834, v := 50386982, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_279__GateII_HBoxData_0 : HBox :=
  { p := 977, k := 688450, v := 49857927, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_280__GateII_HBoxData_0 : HBox :=
  { p := 983, k := 689062, v := 49337511, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_281__GateII_HBoxData_0 : HBox :=
  { p := 991, k := 689873, v := 48656895, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_282__GateII_HBoxData_0 : HBox :=
  { p := 997, k := 690477, v := 48156062, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_283__GateII_HBoxData_0 : HBox :=
  { p := 1009, k := 691673, v := 47178207, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_284__GateII_HBoxData_0 : HBox :=
  { p := 1013, k := 692069, v := 46859237, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_285__GateII_HBoxData_0 : HBox :=
  { p := 1019, k := 692659, v := 46386949, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_286__GateII_HBoxData_0 : HBox :=
  { p := 1021, k := 692855, v := 46231193, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_287__GateII_HBoxData_0 : HBox :=
  { p := 1031, k := 693830, v := 45464684, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_288__GateII_HBoxData_0 : HBox :=
  { p := 1033, k := 694024, v := 45313794, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_289__GateII_HBoxData_0 : HBox :=
  { p := 1039, k := 694603, v := 44865715, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_290__GateII_HBoxData_0 : HBox :=
  { p := 1049, k := 695561, v := 44134265, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_291__GateII_HBoxData_0 : HBox :=
  { p := 1051, k := 695751, v := 43990158, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_292__GateII_HBoxData_0 : HBox :=
  { p := 1061, k := 696698, v := 43280877, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_293__GateII_HBoxData_0 : HBox :=
  { p := 1063, k := 696887, v := 43141258, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_294__GateII_HBoxData_0 : HBox :=
  { p := 1069, k := 697449, v := 42726266, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_295__GateII_HBoxData_0 : HBox :=
  { p := 1087, k := 699119, v := 41518498, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_296__GateII_HBoxData_0 : HBox :=
  { p := 1091, k := 699486, v := 41257338, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_297__GateII_HBoxData_0 : HBox :=
  { p := 1093, k := 699670, v := 41127842, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_298__GateII_HBoxData_0 : HBox :=
  { p := 1097, k := 700035, v := 40870523, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_299__GateII_HBoxData_0 : HBox :=
  { p := 1103, k := 700580, v := 40489253, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_300__GateII_HBoxData_0 : HBox :=
  { p := 1109, k := 701123, v := 40113645, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_301__GateII_HBoxData_0 : HBox :=
  { p := 1117, k := 701842, v := 39621228, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_302__GateII_HBoxData_0 : HBox :=
  { p := 1123, k := 702377, v := 39258013, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_303__GateII_HBoxData_0 : HBox :=
  { p := 1129, k := 702910, v := 38900089, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_304__GateII_HBoxData_0 : HBox :=
  { p := 1151, k := 704840, v := 37630505, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_305__GateII_HBoxData_0 : HBox :=
  { p := 1153, k := 705014, v := 37518361, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_306__GateII_HBoxData_0 : HBox :=
  { p := 1163, k := 705877, v := 36965166, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_307__GateII_HBoxData_0 : HBox :=
  { p := 1171, k := 706563, v := 36531863, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_308__GateII_HBoxData_0 : HBox :=
  { p := 1181, k := 707413, v := 36001246, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_309__GateII_HBoxData_0 : HBox :=
  { p := 1187, k := 707920, v := 35688701, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_310__GateII_HBoxData_0 : HBox :=
  { p := 1193, k := 708424, v := 35380348, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_311__GateII_HBoxData_0 : HBox :=
  { p := 1201, k := 709092, v := 34975659, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_312__GateII_HBoxData_0 : HBox :=
  { p := 1213, k := 710087, v := 34382223, N := 23, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_313__GateII_HBoxData_0 : HBox :=
  { p := 1217, k := 710416, v := 34187870, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_314__GateII_HBoxData_0 : HBox :=
  { p := 1223, k := 710908, v := 33899603, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_315__GateII_HBoxData_0 : HBox :=
  { p := 1229, k := 711397, v := 33615074, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_316__GateII_HBoxData_0 : HBox :=
  { p := 1231, k := 711560, v := 33521113, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_317__GateII_HBoxData_0 : HBox :=
  { p := 1237, k := 712046, v := 33241556, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_318__GateII_HBoxData_0 : HBox :=
  { p := 1249, k := 713011, v := 32693297, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_319__GateII_HBoxData_0 : HBox :=
  { p := 1259, k := 713809, v := 32247249, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_320__GateII_HBoxData_0 : HBox :=
  { p := 1277, k := 715228, v := 31467907, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_321__GateII_HBoxData_0 : HBox :=
  { p := 1279, k := 715385, v := 31383189, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_322__GateII_HBoxData_0 : HBox :=
  { p := 1283, k := 715697, v := 31214713, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_323__GateII_HBoxData_0 : HBox :=
  { p := 1289, k := 716164, v := 30964716, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_324__GateII_HBoxData_0 : HBox :=
  { p := 1291, k := 716319, v := 30882065, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_325__GateII_HBoxData_0 : HBox :=
  { p := 1297, k := 716782, v := 30636128, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_326__GateII_HBoxData_0 : HBox :=
  { p := 1301, k := 717090, v := 30473916, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_327__GateII_HBoxData_0 : HBox :=
  { p := 1303, k := 717244, v := 30393345, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_328__GateII_HBoxData_0 : HBox :=
  { p := 1307, k := 717550, v := 30233091, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_329__GateII_HBoxData_0 : HBox :=
  { p := 1319, k := 718464, v := 29760329, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_330__GateII_HBoxData_0 : HBox :=
  { p := 1321, k := 718616, v := 29682702, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_331__GateII_HBoxData_0 : HBox :=
  { p := 1327, k := 719069, v := 29451583, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_332__GateII_HBoxData_0 : HBox :=
  { p := 1361, k := 721599, v := 28193710, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_333__GateII_HBoxData_0 : HBox :=
  { p := 1367, k := 722039, v := 27980490, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_334__GateII_HBoxData_0 : HBox :=
  { p := 1373, k := 722477, v := 27769781, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_335__GateII_HBoxData_0 : HBox :=
  { p := 1381, k := 723058, v := 27492679, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_336__GateII_HBoxData_0 : HBox :=
  { p := 1399, k := 724353, v := 26884815, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_337__GateII_HBoxData_0 : HBox :=
  { p := 1409, k := 725065, v := 26556146, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_338__GateII_HBoxData_0 : HBox :=
  { p := 1423, k := 726054, v := 26106524, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_339__GateII_HBoxData_0 : HBox :=
  { p := 1427, k := 726334, v := 25980194, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_340__GateII_HBoxData_0 : HBox :=
  { p := 1429, k := 726475, v := 25917480, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_341__GateII_HBoxData_0 : HBox :=
  { p := 1433, k := 726754, v := 25792591, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_342__GateII_HBoxData_0 : HBox :=
  { p := 1439, k := 727172, v := 25607085, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_343__GateII_HBoxData_0 : HBox :=
  { p := 1447, k := 727726, v := 25362933, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_344__GateII_HBoxData_0 : HBox :=
  { p := 1451, k := 728002, v := 25242233, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_345__GateII_HBoxData_0 : HBox :=
  { p := 1453, k := 728140, v := 25182239, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_346__GateII_HBoxData_0 : HBox :=
  { p := 1459, k := 728552, v := 25003534, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_347__GateII_HBoxData_0 : HBox :=
  { p := 1471, k := 729371, v := 24652036, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_348__GateII_HBoxData_0 : HBox :=
  { p := 1481, k := 730049, v := 24365038, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_349__GateII_HBoxData_0 : HBox :=
  { p := 1483, k := 730184, v := 24308263, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_350__GateII_HBoxData_0 : HBox :=
  { p := 1487, k := 730453, v := 24195303, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_351__GateII_HBoxData_0 : HBox :=
  { p := 1489, k := 730588, v := 24139182, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_352__GateII_HBoxData_0 : HBox :=
  { p := 1493, k := 730856, v := 24027455, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_353__GateII_HBoxData_0 : HBox :=
  { p := 1499, k := 731257, v := 23861399, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_354__GateII_HBoxData_0 : HBox :=
  { p := 1511, k := 732054, v := 23534620, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_355__GateII_HBoxData_0 : HBox :=
  { p := 1523, k := 732845, v := 23214818, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_356__GateII_HBoxData_0 : HBox :=
  { p := 1531, k := 733369, v := 23005389, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_357__GateII_HBoxData_0 : HBox :=
  { p := 1543, k := 734150, v := 22696756, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_358__GateII_HBoxData_0 : HBox :=
  { p := 1549, k := 734538, v := 22544851, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_359__GateII_HBoxData_0 : HBox :=
  { p := 1553, k := 734796, v := 22444474, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_360__GateII_HBoxData_0 : HBox :=
  { p := 1559, k := 735181, v := 22295170, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_361__GateII_HBoxData_0 : HBox :=
  { p := 1567, k := 735693, v := 22098563, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_362__GateII_HBoxData_0 : HBox :=
  { p := 1571, k := 735948, v := 22001275, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_363__GateII_HBoxData_0 : HBox :=
  { p := 1579, k := 736456, v := 21808697, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_364__GateII_HBoxData_0 : HBox :=
  { p := 1583, k := 736709, v := 21713393, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_365__GateII_HBoxData_0 : HBox :=
  { p := 1597, k := 737590, v := 21384946, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_366__GateII_HBoxData_0 : HBox :=
  { p := 1601, k := 737840, v := 21292515, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_367__GateII_HBoxData_0 : HBox :=
  { p := 1607, k := 738214, v := 21155047, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_368__GateII_HBoxData_0 : HBox :=
  { p := 1609, k := 738338, v := 21109512, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_369__GateII_HBoxData_0 : HBox :=
  { p := 1613, k := 738587, v := 21018985, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_370__GateII_HBoxData_0 : HBox :=
  { p := 1619, k := 738958, v := 20884255, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_371__GateII_HBoxData_0 : HBox :=
  { p := 1621, k := 739081, v := 20839625, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_372__GateII_HBoxData_0 : HBox :=
  { p := 1627, k := 739451, v := 20706733, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_373__GateII_HBoxData_0 : HBox :=
  { p := 1637, k := 740064, v := 20488142, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_374__GateII_HBoxData_0 : HBox :=
  { p := 1657, k := 741278, v := 20061609, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_375__GateII_HBoxData_0 : HBox :=
  { p := 1663, k := 741639, v := 19936338, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_376__GateII_HBoxData_0 : HBox :=
  { p := 1667, k := 741880, v := 19853560, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_377__GateII_HBoxData_0 : HBox :=
  { p := 1669, k := 741999, v := 19812304, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_378__GateII_HBoxData_0 : HBox :=
  { p := 1693, k := 743427, v := 19328093, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_379__GateII_HBoxData_0 : HBox :=
  { p := 1697, k := 743663, v := 19249192, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_380__GateII_HBoxData_0 : HBox :=
  { p := 1699, k := 743781, v := 19209941, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_381__GateII_HBoxData_0 : HBox :=
  { p := 1709, k := 744368, v := 19015507, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_382__GateII_HBoxData_0 : HBox :=
  { p := 1721, k := 745068, v := 18786230, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_383__GateII_HBoxData_0 : HBox :=
  { p := 1723, k := 745184, v := 18748429, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_384__GateII_HBoxData_0 : HBox :=
  { p := 1733, k := 745762, v := 18561195, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_385__GateII_HBoxData_0 : HBox :=
  { p := 1741, k := 746223, v := 18413557, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_386__GateII_HBoxData_0 : HBox :=
  { p := 1747, k := 746567, v := 18304012, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_387__GateII_HBoxData_0 : HBox :=
  { p := 1753, k := 746910, v := 18195494, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_388__GateII_HBoxData_0 : HBox :=
  { p := 1759, k := 747252, v := 18087987, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_389__GateII_HBoxData_0 : HBox :=
  { p := 1777, k := 748270, v := 17771314, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_390__GateII_HBoxData_0 : HBox :=
  { p := 1783, k := 748607, v := 17667680, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_391__GateII_HBoxData_0 : HBox :=
  { p := 1787, k := 748831, v := 17599114, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_392__GateII_HBoxData_0 : HBox :=
  { p := 1789, k := 748943, v := 17564995, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_393__GateII_HBoxData_0 : HBox :=
  { p := 1801, k := 749611, v := 17362377, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_394__GateII_HBoxData_0 : HBox :=
  { p := 1811, k := 750165, v := 17196342, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_395__GateII_HBoxData_0 : HBox :=
  { p := 1823, k := 750825, v := 17000323, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_396__GateII_HBoxData_0 : HBox :=
  { p := 1831, k := 751263, v := 16871598, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_397__GateII_HBoxData_0 : HBox :=
  { p := 1847, k := 752133, v := 16618667, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_398__GateII_HBoxData_0 : HBox :=
  { p := 1861, k := 752888, v := 16402181, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_399__GateII_HBoxData_0 : HBox :=
  { p := 1867, k := 753210, v := 16310757, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_400__GateII_HBoxData_0 : HBox :=
  { p := 1871, k := 753424, v := 16250246, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_401__GateII_HBoxData_0 : HBox :=
  { p := 1873, k := 753531, v := 16220129, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_402__GateII_HBoxData_0 : HBox :=
  { p := 1877, k := 753745, v := 16160172, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_403__GateII_HBoxData_0 : HBox :=
  { p := 1879, k := 753851, v := 16130288, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_404__GateII_HBoxData_0 : HBox :=
  { p := 1889, k := 754382, v := 15982271, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_405__GateII_HBoxData_0 : HBox :=
  { p := 1901, k := 755015, v := 15807416, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_406__GateII_HBoxData_0 : HBox :=
  { p := 1907, k := 755330, v := 15721108, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_407__GateII_HBoxData_0 : HBox :=
  { p := 1913, k := 755644, v := 15635536, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_408__GateII_HBoxData_0 : HBox :=
  { p := 1931, k := 756581, v := 15383178, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_409__GateII_HBoxData_0 : HBox :=
  { p := 1933, k := 756684, v := 15355509, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_410__GateII_HBoxData_0 : HBox :=
  { p := 1949, k := 757509, v := 15137124, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_411__GateII_HBoxData_0 : HBox :=
  { p := 1951, k := 757611, v := 15110142, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_412__GateII_HBoxData_0 : HBox :=
  { p := 1973, k := 758733, v := 14818505, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_413__GateII_HBoxData_0 : HBox :=
  { p := 1979, k := 759036, v := 14740462, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_414__GateII_HBoxData_0 : HBox :=
  { p := 1987, k := 759440, v := 14637456, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_415__GateII_HBoxData_0 : HBox :=
  { p := 1993, k := 759741, v := 14560903, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_416__GateII_HBoxData_0 : HBox :=
  { p := 1997, k := 759942, v := 14510246, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_417__GateII_HBoxData_0 : HBox :=
  { p := 1999, k := 760042, v := 14485008, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_418__GateII_HBoxData_0 : HBox :=
  { p := 2003, k := 760242, v := 14434749, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_419__GateII_HBoxData_0 : HBox :=
  { p := 2011, k := 760640, v := 14335015, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_420__GateII_HBoxData_0 : HBox :=
  { p := 2017, k := 760938, v := 14260940, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_421__GateII_HBoxData_0 : HBox :=
  { p := 2027, k := 761433, v := 14138816, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_422__GateII_HBoxData_0 : HBox :=
  { p := 2029, k := 761531, v := 14114561, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_423__GateII_HBoxData_0 : HBox :=
  { p := 2039, k := 762023, v := 13994385, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_424__GateII_HBoxData_0 : HBox :=
  { p := 2053, k := 762707, v := 13828779, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_425__GateII_HBoxData_0 : HBox :=
  { p := 2063, k := 763193, v := 13712369, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_426__GateII_HBoxData_0 : HBox :=
  { p := 2069, k := 763484, v := 13643275, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_427__GateII_HBoxData_0 : HBox :=
  { p := 2081, k := 764062, v := 13506659, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_428__GateII_HBoxData_0 : HBox :=
  { p := 2083, k := 764158, v := 13484097, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_429__GateII_HBoxData_0 : HBox :=
  { p := 2087, k := 764350, v := 13439160, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_430__GateII_HBoxData_0 : HBox :=
  { p := 2089, k := 764446, v := 13416785, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_431__GateII_HBoxData_0 : HBox :=
  { p := 2099, k := 764923, v := 13305718, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_432__GateII_HBoxData_0 : HBox :=
  { p := 2111, k := 765493, v := 13174344, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_433__GateII_HBoxData_0 : HBox :=
  { p := 2113, k := 765588, v := 13152657, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_434__GateII_HBoxData_0 : HBox :=
  { p := 2129, k := 766342, v := 12981055, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_435__GateII_HBoxData_0 : HBox :=
  { p := 2131, k := 766436, v := 12959857, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_436__GateII_HBoxData_0 : HBox :=
  { p := 2137, k := 766717, v := 12896568, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_437__GateII_HBoxData_0 : HBox :=
  { p := 2141, k := 766904, v := 12854647, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_438__GateII_HBoxData_0 : HBox :=
  { p := 2143, k := 766998, v := 12833788, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_439__GateII_HBoxData_0 : HBox :=
  { p := 2153, k := 767463, v := 12730158, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_440__GateII_HBoxData_0 : HBox :=
  { p := 2161, k := 767834, v := 12648212, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_441__GateII_HBoxData_0 : HBox :=
  { p := 2179, k := 768664, v := 12466828, N := 24, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_442__GateII_HBoxData_0 : HBox :=
  { p := 2203, k := 769759, v := 12231204, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_443__GateII_HBoxData_0 : HBox :=
  { p := 2207, k := 769940, v := 12192600, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_444__GateII_HBoxData_0 : HBox :=
  { p := 2213, k := 770212, v := 12135085, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_445__GateII_HBoxData_0 : HBox :=
  { p := 2221, k := 770573, v := 12059040, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_446__GateII_HBoxData_0 : HBox :=
  { p := 2237, k := 771291, v := 11909163, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_447__GateII_HBoxData_0 : HBox :=
  { p := 2239, k := 771380, v := 11890621, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_448__GateII_HBoxData_0 : HBox :=
  { p := 2243, k := 771558, v := 11853680, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_449__GateII_HBoxData_0 : HBox :=
  { p := 2251, k := 771914, v := 11780363, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_450__GateII_HBoxData_0 : HBox :=
  { p := 2267, k := 772623, v := 11635863, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_451__GateII_HBoxData_0 : HBox :=
  { p := 2269, k := 772711, v := 11617988, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_452__GateII_HBoxData_0 : HBox :=
  { p := 2273, k := 772887, v := 11582372, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_453__GateII_HBoxData_0 : HBox :=
  { p := 2281, k := 773238, v := 11511648, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_454__GateII_HBoxData_0 : HBox :=
  { p := 2287, k := 773501, v := 11459063, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_455__GateII_HBoxData_0 : HBox :=
  { p := 2293, k := 773763, v := 11406844, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_456__GateII_HBoxData_0 : HBox :=
  { p := 2297, k := 773937, v := 11372229, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_457__GateII_HBoxData_0 : HBox :=
  { p := 2309, k := 774458, v := 11269388, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_458__GateII_HBoxData_0 : HBox :=
  { p := 2311, k := 774545, v := 11252401, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_459__GateII_HBoxData_0 : HBox :=
  { p := 2333, k := 775493, v := 11068047, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_460__GateII_HBoxData_0 : HBox :=
  { p := 2339, k := 775749, v := 11018559, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_461__GateII_HBoxData_0 : HBox :=
  { p := 2341, k := 775835, v := 11002163, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_462__GateII_HBoxData_0 : HBox :=
  { p := 2347, k := 776091, v := 10953159, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_463__GateII_HBoxData_0 : HBox :=
  { p := 2351, k := 776261, v := 10920670, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_464__GateII_HBoxData_0 : HBox :=
  { p := 2357, k := 776516, v := 10872234, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_465__GateII_HBoxData_0 : HBox :=
  { p := 2371, k := 777108, v := 10760499, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_466__GateII_HBoxData_0 : HBox :=
  { p := 2377, k := 777361, v := 10713172, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_467__GateII_HBoxData_0 : HBox :=
  { p := 2381, k := 777529, v := 10681792, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_468__GateII_HBoxData_0 : HBox :=
  { p := 2383, k := 777613, v := 10666158, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_469__GateII_HBoxData_0 : HBox :=
  { p := 2389, k := 777865, v := 10619484, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_470__GateII_HBoxData_0 : HBox :=
  { p := 2393, k := 778032, v := 10588527, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_471__GateII_HBoxData_0 : HBox :=
  { p := 2399, k := 778282, v := 10542357, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_472__GateII_HBoxData_0 : HBox :=
  { p := 2411, k := 778781, v := 10450977, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_473__GateII_HBoxData_0 : HBox :=
  { p := 2417, k := 779030, v := 10405762, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_474__GateII_HBoxData_0 : HBox :=
  { p := 2423, k := 779278, v := 10360842, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_475__GateII_HBoxData_0 : HBox :=
  { p := 2437, k := 779854, v := 10257192, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_476__GateII_HBoxData_0 : HBox :=
  { p := 2441, k := 780018, v := 10227876, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_477__GateII_HBoxData_0 : HBox :=
  { p := 2447, k := 780263, v := 10184134, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_478__GateII_HBoxData_0 : HBox :=
  { p := 2459, k := 780753, v := 10097569, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_479__GateII_HBoxData_0 : HBox :=
  { p := 2467, k := 781077, v := 10040461, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_480__GateII_HBoxData_0 : HBox :=
  { p := 2473, k := 781320, v := 9997979, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_481__GateII_HBoxData_0 : HBox :=
  { p := 2477, k := 781482, v := 9969821, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_482__GateII_HBoxData_0 : HBox :=
  { p := 2503, k := 782526, v := 9789714, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_483__GateII_HBoxData_0 : HBox :=
  { p := 2521, k := 783243, v := 9667997, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_484__GateII_HBoxData_0 : HBox :=
  { p := 2531, k := 783638, v := 9601368, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_485__GateII_HBoxData_0 : HBox :=
  { p := 2539, k := 783954, v := 9548608, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_486__GateII_HBoxData_0 : HBox :=
  { p := 2543, k := 784111, v := 9522382, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_487__GateII_HBoxData_0 : HBox :=
  { p := 2549, k := 784347, v := 9483276, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_488__GateII_HBoxData_0 : HBox :=
  { p := 2551, k := 784426, v := 9470308, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_489__GateII_HBoxData_0 : HBox :=
  { p := 2557, k := 784660, v := 9431506, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_490__GateII_HBoxData_0 : HBox :=
  { p := 2579, k := 785517, v := 9291422, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_491__GateII_HBoxData_0 : HBox :=
  { p := 2591, k := 785981, v := 9216368, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_492__GateII_HBoxData_0 : HBox :=
  { p := 2593, k := 786059, v := 9203972, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_493__GateII_HBoxData_0 : HBox :=
  { p := 2609, k := 786674, v := 9105575, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_494__GateII_HBoxData_0 : HBox :=
  { p := 2617, k := 786980, v := 9056989, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_495__GateII_HBoxData_0 : HBox :=
  { p := 2621, k := 787133, v := 9032856, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_496__GateII_HBoxData_0 : HBox :=
  { p := 2633, k := 787589, v := 8961020, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_497__GateII_HBoxData_0 : HBox :=
  { p := 2647, k := 788120, v := 8878369, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_498__GateII_HBoxData_0 : HBox :=
  { p := 2657, k := 788497, v := 8820047, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_499__GateII_HBoxData_0 : HBox :=
  { p := 2659, k := 788572, v := 8808449, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_500__GateII_HBoxData_0 : HBox :=
  { p := 2663, k := 788722, v := 8785328, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_501__GateII_HBoxData_0 : HBox :=
  { p := 2671, k := 789022, v := 8739386, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_502__GateII_HBoxData_0 : HBox :=
  { p := 2677, k := 789247, v := 8705188, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_503__GateII_HBoxData_0 : HBox :=
  { p := 2683, k := 789471, v := 8671188, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_504__GateII_HBoxData_0 : HBox :=
  { p := 2687, k := 789620, v := 8648635, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_505__GateII_HBoxData_0 : HBox :=
  { p := 2689, k := 789694, v := 8637383, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_506__GateII_HBoxData_0 : HBox :=
  { p := 2693, k := 789843, v := 8614975, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_507__GateII_HBoxData_0 : HBox :=
  { p := 2699, k := 790065, v := 8581508, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_508__GateII_HBoxData_0 : HBox :=
  { p := 2707, k := 790361, v := 8537217, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_509__GateII_HBoxData_0 : HBox :=
  { p := 2711, k := 790509, v := 8515212, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_510__GateII_HBoxData_0 : HBox :=
  { p := 2713, k := 790583, v := 8504245, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_511__GateII_HBoxData_0 : HBox :=
  { p := 2719, k := 790803, v := 8471439, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_512__GateII_HBoxData_0 : HBox :=
  { p := 2729, k := 791171, v := 8417251, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_513__GateII_HBoxData_0 : HBox :=
  { p := 2731, k := 791244, v := 8406469, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_514__GateII_HBoxData_0 : HBox :=
  { p := 2741, k := 791609, v := 8352899, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_515__GateII_HBoxData_0 : HBox :=
  { p := 2749, k := 791901, v := 8310446, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_516__GateII_HBoxData_0 : HBox :=
  { p := 2753, k := 792046, v := 8289331, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_517__GateII_HBoxData_0 : HBox :=
  { p := 2767, k := 792553, v := 8216109, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_518__GateII_HBoxData_0 : HBox :=
  { p := 2777, k := 792914, v := 8164433, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_519__GateII_HBoxData_0 : HBox :=
  { p := 2789, k := 793345, v := 8103079, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_520__GateII_HBoxData_0 : HBox :=
  { p := 2791, k := 793417, v := 8092931, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_521__GateII_HBoxData_0 : HBox :=
  { p := 2797, k := 793632, v := 8062590, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_522__GateII_HBoxData_0 : HBox :=
  { p := 2801, k := 793775, v := 8042460, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_523__GateII_HBoxData_0 : HBox :=
  { p := 2803, k := 793846, v := 8032415, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_524__GateII_HBoxData_0 : HBox :=
  { p := 2819, k := 794415, v := 7952818, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_525__GateII_HBoxData_0 : HBox :=
  { p := 2833, k := 794911, v := 7884191, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_526__GateII_HBoxData_0 : HBox :=
  { p := 2837, k := 795052, v := 7864748, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_527__GateII_HBoxData_0 : HBox :=
  { p := 2843, k := 795263, v := 7835721, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_528__GateII_HBoxData_0 : HBox :=
  { p := 2851, k := 795544, v := 7797284, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_529__GateII_HBoxData_0 : HBox :=
  { p := 2857, k := 795754, v := 7768645, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_530__GateII_HBoxData_0 : HBox :=
  { p := 2861, k := 795894, v := 7749649, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_531__GateII_HBoxData_0 : HBox :=
  { p := 2879, k := 796521, v := 7665043, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_532__GateII_HBoxData_0 : HBox :=
  { p := 2887, k := 796799, v := 7627914, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_533__GateII_HBoxData_0 : HBox :=
  { p := 2897, k := 797145, v := 7581888, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_534__GateII_HBoxData_0 : HBox :=
  { p := 2903, k := 797351, v := 7554461, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_535__GateII_HBoxData_0 : HBox :=
  { p := 2909, k := 797558, v := 7527216, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_536__GateII_HBoxData_0 : HBox :=
  { p := 2917, k := 797833, v := 7491120, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_537__GateII_HBoxData_0 : HBox :=
  { p := 2927, k := 798175, v := 7446366, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_538__GateII_HBoxData_0 : HBox :=
  { p := 2939, k := 798584, v := 7393213, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_539__GateII_HBoxData_0 : HBox :=
  { p := 2953, k := 799059, v := 7331944, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_540__GateII_HBoxData_0 : HBox :=
  { p := 2957, k := 799195, v := 7314597, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_541__GateII_HBoxData_0 : HBox :=
  { p := 2963, k := 799397, v := 7288667, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_542__GateII_HBoxData_0 : HBox :=
  { p := 2969, k := 799600, v := 7262905, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_543__GateII_HBoxData_0 : HBox :=
  { p := 2971, k := 799667, v := 7254339, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_544__GateII_HBoxData_0 : HBox :=
  { p := 2999, k := 800605, v := 7136134, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_545__GateII_HBoxData_0 : HBox :=
  { p := 3001, k := 800672, v := 7127812, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_546__GateII_HBoxData_0 : HBox :=
  { p := 3011, k := 801004, v := 7086387, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_547__GateII_HBoxData_0 : HBox :=
  { p := 3019, k := 801270, v := 7053538, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_548__GateII_HBoxData_0 : HBox :=
  { p := 3023, k := 801402, v := 7037190, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_549__GateII_HBoxData_0 : HBox :=
  { p := 3037, k := 801864, v := 6980458, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_550__GateII_HBoxData_0 : HBox :=
  { p := 3041, k := 801996, v := 6964387, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_551__GateII_HBoxData_0 : HBox :=
  { p := 3049, k := 802258, v := 6932392, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_552__GateII_HBoxData_0 : HBox :=
  { p := 3061, k := 802651, v := 6884849, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_553__GateII_HBoxData_0 : HBox :=
  { p := 3067, k := 802847, v := 6861270, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_554__GateII_HBoxData_0 : HBox :=
  { p := 3079, k := 803238, v := 6814491, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_555__GateII_HBoxData_0 : HBox :=
  { p := 3083, k := 803367, v := 6798991, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_556__GateII_HBoxData_0 : HBox :=
  { p := 3089, k := 803562, v := 6775876, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_557__GateII_HBoxData_0 : HBox :=
  { p := 3109, k := 804207, v := 6699665, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_558__GateII_HBoxData_0 : HBox :=
  { p := 3119, k := 804528, v := 6662061, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_559__GateII_HBoxData_0 : HBox :=
  { p := 3121, k := 804592, v := 6654579, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_560__GateII_HBoxData_0 : HBox :=
  { p := 3137, k := 805104, v := 6595212, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_561__GateII_HBoxData_0 : HBox :=
  { p := 3163, k := 805929, v := 6500466, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_562__GateII_HBoxData_0 : HBox :=
  { p := 3167, k := 806056, v := 6486089, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_563__GateII_HBoxData_0 : HBox :=
  { p := 3169, k := 806119, v := 6478912, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_564__GateII_HBoxData_0 : HBox :=
  { p := 3181, k := 806497, v := 6436123, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_565__GateII_HBoxData_0 : HBox :=
  { p := 3187, k := 806685, v := 6414887, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_566__GateII_HBoxData_0 : HBox :=
  { p := 3191, k := 806810, v := 6400788, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_567__GateII_HBoxData_0 : HBox :=
  { p := 3203, k := 807186, v := 6358809, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_568__GateII_HBoxData_0 : HBox :=
  { p := 3209, k := 807373, v := 6337974, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_569__GateII_HBoxData_0 : HBox :=
  { p := 3217, k := 807622, v := 6310361, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_570__GateII_HBoxData_0 : HBox :=
  { p := 3221, k := 807746, v := 6296621, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_571__GateII_HBoxData_0 : HBox :=
  { p := 3229, k := 807994, v := 6269288, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_572__GateII_HBoxData_0 : HBox :=
  { p := 3251, k := 808673, v := 6195072, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_573__GateII_HBoxData_0 : HBox :=
  { p := 3253, k := 808735, v := 6188401, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_574__GateII_HBoxData_0 : HBox :=
  { p := 3257, k := 808858, v := 6175079, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_575__GateII_HBoxData_0 : HBox :=
  { p := 3259, k := 808919, v := 6168428, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_576__GateII_HBoxData_0 : HBox :=
  { p := 3271, k := 809287, v := 6128796, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_577__GateII_HBoxData_0 : HBox :=
  { p := 3299, k := 810139, v := 6037833, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_578__GateII_HBoxData_0 : HBox :=
  { p := 3301, k := 810200, v := 6031423, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_579__GateII_HBoxData_0 : HBox :=
  { p := 3307, k := 810381, v := 6012229, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_580__GateII_HBoxData_0 : HBox :=
  { p := 3313, k := 810562, v := 5993135, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_581__GateII_HBoxData_0 : HBox :=
  { p := 3319, k := 810743, v := 5974140, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_582__GateII_HBoxData_0 : HBox :=
  { p := 3323, k := 810864, v := 5961536, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_583__GateII_HBoxData_0 : HBox :=
  { p := 3329, k := 811044, v := 5942691, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_584__GateII_HBoxData_0 : HBox :=
  { p := 3331, k := 811104, v := 5936431, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_585__GateII_HBoxData_0 : HBox :=
  { p := 3343, k := 811464, v := 5899096, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_586__GateII_HBoxData_0 : HBox :=
  { p := 3347, k := 811583, v := 5886722, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_587__GateII_HBoxData_0 : HBox :=
  { p := 3359, k := 811941, v := 5849870, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_588__GateII_HBoxData_0 : HBox :=
  { p := 3361, k := 812001, v := 5843769, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_589__GateII_HBoxData_0 : HBox :=
  { p := 3371, k := 812298, v := 5813379, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_590__GateII_HBoxData_0 : HBox :=
  { p := 3373, k := 812357, v := 5807327, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_591__GateII_HBoxData_0 : HBox :=
  { p := 3389, k := 812831, v := 5759305, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_592__GateII_HBoxData_0 : HBox :=
  { p := 3391, k := 812890, v := 5753344, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_593__GateII_HBoxData_0 : HBox :=
  { p := 3407, k := 813360, v := 5705994, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_594__GateII_HBoxData_0 : HBox :=
  { p := 3413, k := 813536, v := 5688399, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_595__GateII_HBoxData_0 : HBox :=
  { p := 3433, k := 814120, v := 5630349, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_596__GateII_HBoxData_0 : HBox :=
  { p := 3449, k := 814585, v := 5584576, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_597__GateII_HBoxData_0 : HBox :=
  { p := 3457, k := 814817, v := 5561910, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_598__GateII_HBoxData_0 : HBox :=
  { p := 3461, k := 814933, v := 5550634, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_599__GateII_HBoxData_0 : HBox :=
  { p := 3463, k := 814991, v := 5545010, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_600__GateII_HBoxData_0 : HBox :=
  { p := 3467, k := 815106, v := 5533777, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_601__GateII_HBoxData_0 : HBox :=
  { p := 3469, k := 815164, v := 5528181, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_602__GateII_HBoxData_0 : HBox :=
  { p := 3491, k := 815796, v := 5467152, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_603__GateII_HBoxData_0 : HBox :=
  { p := 3499, k := 816025, v := 5445222, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_604__GateII_HBoxData_0 : HBox :=
  { p := 3511, k := 816367, v := 5412577, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_605__GateII_HBoxData_0 : HBox :=
  { p := 3517, k := 816538, v := 5396374, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_606__GateII_HBoxData_0 : HBox :=
  { p := 3527, k := 816822, v := 5369533, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_607__GateII_HBoxData_0 : HBox :=
  { p := 3529, k := 816878, v := 5364181, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_608__GateII_HBoxData_0 : HBox :=
  { p := 3533, k := 816992, v := 5353528, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_609__GateII_HBoxData_0 : HBox :=
  { p := 3539, k := 817161, v := 5337588, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_610__GateII_HBoxData_0 : HBox :=
  { p := 3541, k := 817218, v := 5332301, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_611__GateII_HBoxData_0 : HBox :=
  { p := 3547, k := 817387, v := 5316464, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_612__GateII_HBoxData_0 : HBox :=
  { p := 3557, k := 817669, v := 5290245, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_613__GateII_HBoxData_0 : HBox :=
  { p := 3559, k := 817725, v := 5285022, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_614__GateII_HBoxData_0 : HBox :=
  { p := 3571, k := 818062, v := 5253870, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_615__GateII_HBoxData_0 : HBox :=
  { p := 3581, k := 818341, v := 5228115, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_616__GateII_HBoxData_0 : HBox :=
  { p := 3583, k := 818397, v := 5222992, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_617__GateII_HBoxData_0 : HBox :=
  { p := 3593, k := 818676, v := 5197485, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_618__GateII_HBoxData_0 : HBox :=
  { p := 3607, k := 819065, v := 5162097, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_619__GateII_HBoxData_0 : HBox :=
  { p := 3613, k := 819231, v := 5147042, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_620__GateII_HBoxData_0 : HBox :=
  { p := 3617, k := 819342, v := 5137050, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_621__GateII_HBoxData_0 : HBox :=
  { p := 3623, k := 819507, v := 5122102, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_622__GateII_HBoxData_0 : HBox :=
  { p := 3631, k := 819728, v := 5102295, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_623__GateII_HBoxData_0 : HBox :=
  { p := 3637, k := 819893, v := 5087512, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_624__GateII_HBoxData_0 : HBox :=
  { p := 3643, k := 820058, v := 5072800, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_625__GateII_HBoxData_0 : HBox :=
  { p := 3659, k := 820496, v := 5033881, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_626__GateII_HBoxData_0 : HBox :=
  { p := 3671, k := 820823, v := 5004994, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_627__GateII_HBoxData_0 : HBox :=
  { p := 3673, k := 820878, v := 5000212, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_628__GateII_HBoxData_0 : HBox :=
  { p := 3677, k := 820987, v := 4990658, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_629__GateII_HBoxData_0 : HBox :=
  { p := 3691, k := 821367, v := 4957436, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_630__GateII_HBoxData_0 : HBox :=
  { p := 3697, k := 821529, v := 4943299, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_631__GateII_HBoxData_0 : HBox :=
  { p := 3701, k := 821637, v := 4933910, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_632__GateII_HBoxData_0 : HBox :=
  { p := 3709, k := 821853, v := 4915221, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_633__GateII_HBoxData_0 : HBox :=
  { p := 3719, k := 822123, v := 4892022, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_634__GateII_HBoxData_0 : HBox :=
  { p := 3727, k := 822337, v := 4873568, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_635__GateII_HBoxData_0 : HBox :=
  { p := 3733, k := 822498, v := 4859808, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_636__GateII_HBoxData_0 : HBox :=
  { p := 3739, k := 822659, v := 4846112, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_637__GateII_HBoxData_0 : HBox :=
  { p := 3761, k := 823246, v := 4796391, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_638__GateII_HBoxData_0 : HBox :=
  { p := 3767, k := 823405, v := 4782963, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_639__GateII_HBoxData_0 : HBox :=
  { p := 3769, k := 823458, v := 4778500, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_640__GateII_HBoxData_0 : HBox :=
  { p := 3779, k := 823723, v := 4756290, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_641__GateII_HBoxData_0 : HBox :=
  { p := 3793, k := 824093, v := 4725468, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_642__GateII_HBoxData_0 : HBox :=
  { p := 3797, k := 824198, v := 4716714, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_643__GateII_HBoxData_0 : HBox :=
  { p := 3803, k := 824356, v := 4703637, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_644__GateII_HBoxData_0 : HBox :=
  { p := 3821, k := 824828, v := 4664740, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_645__GateII_HBoxData_0 : HBox :=
  { p := 3823, k := 824881, v := 4660457, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_646__GateII_HBoxData_0 : HBox :=
  { p := 3833, k := 825142, v := 4639093, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_647__GateII_HBoxData_0 : HBox :=
  { p := 3847, k := 825506, v := 4609435, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_648__GateII_HBoxData_0 : HBox :=
  { p := 3851, k := 825610, v := 4601019, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_649__GateII_HBoxData_0 : HBox :=
  { p := 3853, k := 825662, v := 4596820, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_650__GateII_HBoxData_0 : HBox :=
  { p := 3863, k := 825921, v := 4575909, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_651__GateII_HBoxData_0 : HBox :=
  { p := 3877, k := 826283, v := 4546887, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_652__GateII_HBoxData_0 : HBox :=
  { p := 3881, k := 826386, v := 4538646, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_653__GateII_HBoxData_0 : HBox :=
  { p := 3889, k := 826592, v := 4522237, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_654__GateII_HBoxData_0 : HBox :=
  { p := 3907, k := 827054, v := 4485652, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_655__GateII_HBoxData_0 : HBox :=
  { p := 3911, k := 827156, v := 4477581, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_656__GateII_HBoxData_0 : HBox :=
  { p := 3917, k := 827310, v := 4465530, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_657__GateII_HBoxData_0 : HBox :=
  { p := 3919, k := 827361, v := 4461521, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_658__GateII_HBoxData_0 : HBox :=
  { p := 3923, k := 827463, v := 4453520, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_659__GateII_HBoxData_0 : HBox :=
  { p := 3929, k := 827616, v := 4441564, N := 25, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_660__GateII_HBoxData_0 : HBox :=
  { p := 3931, k := 827666, v := 4437579, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_661__GateII_HBoxData_0 : HBox :=
  { p := 3943, k := 827971, v := 4413848, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_662__GateII_HBoxData_0 : HBox :=
  { p := 3947, k := 828073, v := 4405987, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_663__GateII_HBoxData_0 : HBox :=
  { p := 3967, k := 828578, v := 4366972, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_664__GateII_HBoxData_0 : HBox :=
  { p := 3989, k := 829131, v := 4324678, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_665__GateII_HBoxData_0 : HBox :=
  { p := 4001, k := 829431, v := 4301874, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_666__GateII_HBoxData_0 : HBox :=
  { p := 4003, k := 829481, v := 4298092, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_667__GateII_HBoxData_0 : HBox :=
  { p := 4007, k := 829581, v := 4290546, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_668__GateII_HBoxData_0 : HBox :=
  { p := 4013, k := 829731, v := 4279266, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_669__GateII_HBoxData_0 : HBox :=
  { p := 4019, k := 829880, v := 4268024, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_670__GateII_HBoxData_0 : HBox :=
  { p := 4021, k := 829930, v := 4264292, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_671__GateII_HBoxData_0 : HBox :=
  { p := 4027, k := 830079, v := 4253114, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_672__GateII_HBoxData_0 : HBox :=
  { p := 4049, k := 830624, v := 4212525, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_673__GateII_HBoxData_0 : HBox :=
  { p := 4051, k := 830673, v := 4208861, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_674__GateII_HBoxData_0 : HBox :=
  { p := 4057, k := 830821, v := 4197911, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_675__GateII_HBoxData_0 : HBox :=
  { p := 4073, k := 831215, v := 4168929, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_676__GateII_HBoxData_0 : HBox :=
  { p := 4079, k := 831362, v := 4158138, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_677__GateII_HBoxData_0 : HBox :=
  { p := 4091, k := 831656, v := 4136692, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_678__GateII_HBoxData_0 : HBox :=
  { p := 4093, k := 831705, v := 4133135, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_679__GateII_HBoxData_0 : HBox :=
  { p := 4099, k := 831851, v := 4122485, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_680__GateII_HBoxData_0 : HBox :=
  { p := 4111, k := 832144, v := 4101330, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_681__GateII_HBoxData_0 : HBox :=
  { p := 4127, k := 832532, v := 4073371, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_682__GateII_HBoxData_0 : HBox :=
  { p := 4129, k := 832581, v := 4069903, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_683__GateII_HBoxData_0 : HBox :=
  { p := 4133, k := 832677, v := 4062962, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_684__GateII_HBoxData_0 : HBox :=
  { p := 4139, k := 832822, v := 4052596, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_685__GateII_HBoxData_0 : HBox :=
  { p := 4153, k := 833160, v := 4028574, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_686__GateII_HBoxData_0 : HBox :=
  { p := 4157, k := 833256, v := 4021748, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_687__GateII_HBoxData_0 : HBox :=
  { p := 4159, k := 833304, v := 4018342, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_688__GateII_HBoxData_0 : HBox :=
  { p := 4177, k := 833736, v := 3987899, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_689__GateII_HBoxData_0 : HBox :=
  { p := 4201, k := 834309, v := 3947863, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_690__GateII_HBoxData_0 : HBox :=
  { p := 4211, k := 834547, v := 3931368, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_691__GateII_HBoxData_0 : HBox :=
  { p := 4217, k := 834689, v := 3921518, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_692__GateII_HBoxData_0 : HBox :=
  { p := 4219, k := 834737, v := 3918250, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_693__GateII_HBoxData_0 : HBox :=
  { p := 4229, k := 834974, v := 3901947, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_694__GateII_HBoxData_0 : HBox :=
  { p := 4231, k := 835021, v := 3898696, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_695__GateII_HBoxData_0 : HBox :=
  { p := 4241, k := 835257, v := 3882517, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_696__GateII_HBoxData_0 : HBox :=
  { p := 4243, k := 835304, v := 3879293, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_697__GateII_HBoxData_0 : HBox :=
  { p := 4253, k := 835539, v := 3863236, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_698__GateII_HBoxData_0 : HBox :=
  { p := 4259, k := 835680, v := 3853654, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_699__GateII_HBoxData_0 : HBox :=
  { p := 4261, k := 835727, v := 3850468, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_700__GateII_HBoxData_0 : HBox :=
  { p := 4271, k := 835962, v := 3834606, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_701__GateII_HBoxData_0 : HBox :=
  { p := 4273, k := 836009, v := 3831446, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_702__GateII_HBoxData_0 : HBox :=
  { p := 4283, k := 836242, v := 3815694, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_703__GateII_HBoxData_0 : HBox :=
  { p := 4289, k := 836382, v := 3806294, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_704__GateII_HBoxData_0 : HBox :=
  { p := 4297, k := 836569, v := 3793824, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_705__GateII_HBoxData_0 : HBox :=
  { p := 4327, k := 837264, v := 3747595, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_706__GateII_HBoxData_0 : HBox :=
  { p := 4337, k := 837495, v := 3732383, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_707__GateII_HBoxData_0 : HBox :=
  { p := 4339, k := 837541, v := 3729351, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_708__GateII_HBoxData_0 : HBox :=
  { p := 4349, k := 837772, v := 3714261, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_709__GateII_HBoxData_0 : HBox :=
  { p := 4357, k := 837955, v := 3702244, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_710__GateII_HBoxData_0 : HBox :=
  { p := 4363, k := 838093, v := 3693280, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_711__GateII_HBoxData_0 : HBox :=
  { p := 4373, k := 838322, v := 3678410, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_712__GateII_HBoxData_0 : HBox :=
  { p := 4391, k := 838733, v := 3651878, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_713__GateII_HBoxData_0 : HBox :=
  { p := 4397, k := 838869, v := 3643095, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_714__GateII_HBoxData_0 : HBox :=
  { p := 4409, k := 839142, v := 3625641, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_715__GateII_HBoxData_0 : HBox :=
  { p := 4421, k := 839414, v := 3608315, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_716__GateII_HBoxData_0 : HBox :=
  { p := 4423, k := 839459, v := 3605437, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_717__GateII_HBoxData_0 : HBox :=
  { p := 4441, k := 839865, v := 3579717, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_718__GateII_HBoxData_0 : HBox :=
  { p := 4447, k := 840000, v := 3571207, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_719__GateII_HBoxData_0 : HBox :=
  { p := 4451, k := 840090, v := 3565552, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_720__GateII_HBoxData_0 : HBox :=
  { p := 4457, k := 840225, v := 3557098, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_721__GateII_HBoxData_0 : HBox :=
  { p := 4463, k := 840359, v := 3548667, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_722__GateII_HBoxData_0 : HBox :=
  { p := 4481, k := 840762, v := 3523579, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_723__GateII_HBoxData_0 : HBox :=
  { p := 4483, k := 840806, v := 3520803, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_724__GateII_HBoxData_0 : HBox :=
  { p := 4493, k := 841029, v := 3507001, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_725__GateII_HBoxData_0 : HBox :=
  { p := 4507, k := 841340, v := 3487815, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_726__GateII_HBoxData_0 : HBox :=
  { p := 4513, k := 841473, v := 3479643, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_727__GateII_HBoxData_0 : HBox :=
  { p := 4517, k := 841562, v := 3474215, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_728__GateII_HBoxData_0 : HBox :=
  { p := 4519, k := 841606, v := 3471502, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_729__GateII_HBoxData_0 : HBox :=
  { p := 4523, k := 841695, v := 3466095, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_730__GateII_HBoxData_0 : HBox :=
  { p := 4547, k := 842224, v := 3433898, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_731__GateII_HBoxData_0 : HBox :=
  { p := 4549, k := 842268, v := 3431237, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_732__GateII_HBoxData_0 : HBox :=
  { p := 4561, k := 842531, v := 3415329, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_733__GateII_HBoxData_0 : HBox :=
  { p := 4567, k := 842663, v := 3407425, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_734__GateII_HBoxData_0 : HBox :=
  { p := 4583, k := 843012, v := 3386468, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_735__GateII_HBoxData_0 : HBox :=
  { p := 4591, k := 843187, v := 3376072, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_736__GateII_HBoxData_0 : HBox :=
  { p := 4597, k := 843317, v := 3368299, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_737__GateII_HBoxData_0 : HBox :=
  { p := 4603, k := 843448, v := 3360564, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_738__GateII_HBoxData_0 : HBox :=
  { p := 4621, k := 843838, v := 3337507, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_739__GateII_HBoxData_0 : HBox :=
  { p := 4637, k := 844184, v := 3317224, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_740__GateII_HBoxData_0 : HBox :=
  { p := 4639, k := 844227, v := 3314700, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_741__GateII_HBoxData_0 : HBox :=
  { p := 4643, k := 844313, v := 3309663, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_742__GateII_HBoxData_0 : HBox :=
  { p := 4649, k := 844442, v := 3302131, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_743__GateII_HBoxData_0 : HBox :=
  { p := 4651, k := 844485, v := 3299627, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_744__GateII_HBoxData_0 : HBox :=
  { p := 4657, k := 844614, v := 3292132, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_745__GateII_HBoxData_0 : HBox :=
  { p := 4663, k := 844743, v := 3284664, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_746__GateII_HBoxData_0 : HBox :=
  { p := 4673, k := 844957, v := 3272273, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_747__GateII_HBoxData_0 : HBox :=
  { p := 4679, k := 845085, v := 3264871, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_748__GateII_HBoxData_0 : HBox :=
  { p := 4691, k := 845342, v := 3250158, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_749__GateII_HBoxData_0 : HBox :=
  { p := 4703, k := 845597, v := 3235537, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_750__GateII_HBoxData_0 : HBox :=
  { p := 4721, k := 845979, v := 3213803, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_751__GateII_HBoxData_0 : HBox :=
  { p := 4723, k := 846021, v := 3211399, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_752__GateII_HBoxData_0 : HBox :=
  { p := 4729, k := 846148, v := 3204214, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_753__GateII_HBoxData_0 : HBox :=
  { p := 4733, k := 846233, v := 3199440, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_754__GateII_HBoxData_0 : HBox :=
  { p := 4751, k := 846613, v := 3178085, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_755__GateII_HBoxData_0 : HBox :=
  { p := 4759, k := 846781, v := 3168662, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_756__GateII_HBoxData_0 : HBox :=
  { p := 4783, k := 847284, v := 3140657, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_757__GateII_HBoxData_0 : HBox :=
  { p := 4787, k := 847367, v := 3136023, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_758__GateII_HBoxData_0 : HBox :=
  { p := 4789, k := 847409, v := 3133714, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_759__GateII_HBoxData_0 : HBox :=
  { p := 4793, k := 847493, v := 3129103, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_760__GateII_HBoxData_0 : HBox :=
  { p := 4799, k := 847618, v := 3122201, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_761__GateII_HBoxData_0 : HBox :=
  { p := 4801, k := 847659, v := 3119901, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_762__GateII_HBoxData_0 : HBox :=
  { p := 4813, k := 847909, v := 3106188, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_763__GateII_HBoxData_0 : HBox :=
  { p := 4817, k := 847992, v := 3101637, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_764__GateII_HBoxData_0 : HBox :=
  { p := 4831, k := 848282, v := 3085788, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_765__GateII_HBoxData_0 : HBox :=
  { p := 4861, k := 848901, v := 3052251, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_766__GateII_HBoxData_0 : HBox :=
  { p := 4871, k := 849107, v := 3041202, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_767__GateII_HBoxData_0 : HBox :=
  { p := 4877, k := 849230, v := 3034600, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_768__GateII_HBoxData_0 : HBox :=
  { p := 4889, k := 849476, v := 3021465, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_769__GateII_HBoxData_0 : HBox :=
  { p := 4903, k := 849762, v := 3006251, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_770__GateII_HBoxData_0 : HBox :=
  { p := 4909, k := 849884, v := 2999765, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_771__GateII_HBoxData_0 : HBox :=
  { p := 4919, k := 850088, v := 2989010, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_772__GateII_HBoxData_0 : HBox :=
  { p := 4931, k := 850331, v := 2976175, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_773__GateII_HBoxData_0 : HBox :=
  { p := 4933, k := 850372, v := 2974048, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_774__GateII_HBoxData_0 : HBox :=
  { p := 4937, k := 850453, v := 2969794, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_775__GateII_HBoxData_0 : HBox :=
  { p := 4943, k := 850574, v := 2963429, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_776__GateII_HBoxData_0 : HBox :=
  { p := 4951, k := 850736, v := 2954981, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_777__GateII_HBoxData_0 : HBox :=
  { p := 4957, k := 850857, v := 2948668, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_778__GateII_HBoxData_0 : HBox :=
  { p := 4967, k := 851059, v := 2938197, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_779__GateII_HBoxData_0 : HBox :=
  { p := 4969, k := 851099, v := 2936107, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_780__GateII_HBoxData_0 : HBox :=
  { p := 4973, k := 851179, v := 2931935, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_781__GateII_HBoxData_0 : HBox :=
  { p := 4987, k := 851460, v := 2917415, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_782__GateII_HBoxData_0 : HBox :=
  { p := 4993, k := 851581, v := 2911232, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_783__GateII_HBoxData_0 : HBox :=
  { p := 4999, k := 851701, v := 2905064, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_784__GateII_HBoxData_0 : HBox :=
  { p := 5003, k := 851781, v := 2900963, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_785__GateII_HBoxData_0 : HBox :=
  { p := 5009, k := 851901, v := 2894830, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_786__GateII_HBoxData_0 : HBox :=
  { p := 5011, k := 851941, v := 2892791, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_787__GateII_HBoxData_0 : HBox :=
  { p := 5021, k := 852140, v := 2882621, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_788__GateII_HBoxData_0 : HBox :=
  { p := 5023, k := 852180, v := 2880595, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_789__GateII_HBoxData_0 : HBox :=
  { p := 5039, k := 852498, v := 2864461, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_790__GateII_HBoxData_0 : HBox :=
  { p := 5051, k := 852736, v := 2852453, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_791__GateII_HBoxData_0 : HBox :=
  { p := 5059, k := 852894, v := 2844489, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_792__GateII_HBoxData_0 : HBox :=
  { p := 5077, k := 853249, v := 2826699, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_793__GateII_HBoxData_0 : HBox :=
  { p := 5081, k := 853328, v := 2822771, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_794__GateII_HBoxData_0 : HBox :=
  { p := 5087, k := 853446, v := 2816892, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_795__GateII_HBoxData_0 : HBox :=
  { p := 5099, k := 853681, v := 2805188, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_796__GateII_HBoxData_0 : HBox :=
  { p := 5101, k := 853721, v := 2803251, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_797__GateII_HBoxData_0 : HBox :=
  { p := 5107, k := 853838, v := 2797432, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_798__GateII_HBoxData_0 : HBox :=
  { p := 5113, k := 853956, v := 2791639, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_799__GateII_HBoxData_0 : HBox :=
  { p := 5119, k := 854073, v := 2785859, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_800__GateII_HBoxData_0 : HBox :=
  { p := 5147, k := 854618, v := 2759137, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_801__GateII_HBoxData_0 : HBox :=
  { p := 5153, k := 854735, v := 2753467, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_802__GateII_HBoxData_0 : HBox :=
  { p := 5167, k := 855006, v := 2740297, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_803__GateII_HBoxData_0 : HBox :=
  { p := 5171, k := 855084, v := 2736557, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_804__GateII_HBoxData_0 : HBox :=
  { p := 5179, k := 855238, v := 2729089, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_805__GateII_HBoxData_0 : HBox :=
  { p := 5189, k := 855431, v := 2719803, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_806__GateII_HBoxData_0 : HBox :=
  { p := 5197, k := 855585, v := 2712409, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_807__GateII_HBoxData_0 : HBox :=
  { p := 5209, k := 855816, v := 2701380, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_808__GateII_HBoxData_0 : HBox :=
  { p := 5227, k := 856161, v := 2684963, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_809__GateII_HBoxData_0 : HBox :=
  { p := 5231, k := 856237, v := 2681333, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_810__GateII_HBoxData_0 : HBox :=
  { p := 5233, k := 856276, v := 2679527, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_811__GateII_HBoxData_0 : HBox :=
  { p := 5237, k := 856352, v := 2675909, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_812__GateII_HBoxData_0 : HBox :=
  { p := 5261, k := 856809, v := 2654372, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_813__GateII_HBoxData_0 : HBox :=
  { p := 5273, k := 857037, v := 2643706, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_814__GateII_HBoxData_0 : HBox :=
  { p := 5279, k := 857151, v := 2638399, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_815__GateII_HBoxData_0 : HBox :=
  { p := 5281, k := 857189, v := 2636634, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_816__GateII_HBoxData_0 : HBox :=
  { p := 5297, k := 857491, v := 2622571, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_817__GateII_HBoxData_0 : HBox :=
  { p := 5303, k := 857604, v := 2617327, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_818__GateII_HBoxData_0 : HBox :=
  { p := 5309, k := 857717, v := 2612101, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_819__GateII_HBoxData_0 : HBox :=
  { p := 5323, k := 857981, v := 2599973, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_820__GateII_HBoxData_0 : HBox :=
  { p := 5333, k := 858168, v := 2591357, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_821__GateII_HBoxData_0 : HBox :=
  { p := 5347, k := 858431, v := 2579380, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_822__GateII_HBoxData_0 : HBox :=
  { p := 5351, k := 858505, v := 2575968, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_823__GateII_HBoxData_0 : HBox :=
  { p := 5381, k := 859064, v := 2550633, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_824__GateII_HBoxData_0 : HBox :=
  { p := 5387, k := 859176, v := 2545616, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_825__GateII_HBoxData_0 : HBox :=
  { p := 5393, k := 859287, v := 2540609, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_826__GateII_HBoxData_0 : HBox :=
  { p := 5399, k := 859398, v := 2535618, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_827__GateII_HBoxData_0 : HBox :=
  { p := 5407, k := 859546, v := 2528989, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_828__GateII_HBoxData_0 : HBox :=
  { p := 5413, k := 859657, v := 2524035, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_829__GateII_HBoxData_0 : HBox :=
  { p := 5417, k := 859731, v := 2520741, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_830__GateII_HBoxData_0 : HBox :=
  { p := 5419, k := 859768, v := 2519097, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_831__GateII_HBoxData_0 : HBox :=
  { p := 5431, k := 859989, v := 2509263, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_832__GateII_HBoxData_0 : HBox :=
  { p := 5437, k := 860100, v := 2504372, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_833__GateII_HBoxData_0 : HBox :=
  { p := 5441, k := 860173, v := 2501114, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_834__GateII_HBoxData_0 : HBox :=
  { p := 5443, k := 860210, v := 2499491, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_835__GateII_HBoxData_0 : HBox :=
  { p := 5449, k := 860320, v := 2494625, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_836__GateII_HBoxData_0 : HBox :=
  { p := 5471, k := 860723, v := 2476914, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_837__GateII_HBoxData_0 : HBox :=
  { p := 5477, k := 860833, v := 2472120, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_838__GateII_HBoxData_0 : HBox :=
  { p := 5479, k := 860869, v := 2470522, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_839__GateII_HBoxData_0 : HBox :=
  { p := 5483, k := 860942, v := 2467336, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_840__GateII_HBoxData_0 : HBox :=
  { p := 5501, k := 861270, v := 2453077, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_841__GateII_HBoxData_0 : HBox :=
  { p := 5503, k := 861306, v := 2451499, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_842__GateII_HBoxData_0 : HBox :=
  { p := 5507, k := 861379, v := 2448353, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_843__GateII_HBoxData_0 : HBox :=
  { p := 5519, k := 861597, v := 2438947, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_844__GateII_HBoxData_0 : HBox :=
  { p := 5521, k := 861633, v := 2437384, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_845__GateII_HBoxData_0 : HBox :=
  { p := 5527, k := 861742, v := 2432708, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_846__GateII_HBoxData_0 : HBox :=
  { p := 5531, k := 861814, v := 2429595, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_847__GateII_HBoxData_0 : HBox :=
  { p := 5557, k := 862283, v := 2409526, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_848__GateII_HBoxData_0 : HBox :=
  { p := 5563, k := 862391, v := 2404931, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_849__GateII_HBoxData_0 : HBox :=
  { p := 5569, k := 862499, v := 2400351, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_850__GateII_HBoxData_0 : HBox :=
  { p := 5573, k := 862570, v := 2397300, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_851__GateII_HBoxData_0 : HBox :=
  { p := 5581, k := 862714, v := 2391228, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_852__GateII_HBoxData_0 : HBox :=
  { p := 5591, k := 862893, v := 2383668, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_853__GateII_HBoxData_0 : HBox :=
  { p := 5623, k := 863464, v := 2359725, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_854__GateII_HBoxData_0 : HBox :=
  { p := 5639, k := 863748, v := 2347892, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_855__GateII_HBoxData_0 : HBox :=
  { p := 5641, k := 863783, v := 2346417, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_856__GateII_HBoxData_0 : HBox :=
  { p := 5647, k := 863889, v := 2342006, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_857__GateII_HBoxData_0 : HBox :=
  { p := 5651, k := 863960, v := 2339075, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_858__GateII_HBoxData_0 : HBox :=
  { p := 5653, k := 863996, v := 2337615, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_859__GateII_HBoxData_0 : HBox :=
  { p := 5657, k := 864066, v := 2334687, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_860__GateII_HBoxData_0 : HBox :=
  { p := 5659, k := 864102, v := 2333231, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_861__GateII_HBoxData_0 : HBox :=
  { p := 5669, k := 864278, v := 2325951, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_862__GateII_HBoxData_0 : HBox :=
  { p := 5683, k := 864525, v := 2315824, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_863__GateII_HBoxData_0 : HBox :=
  { p := 5689, k := 864630, v := 2311502, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_864__GateII_HBoxData_0 : HBox :=
  { p := 5693, k := 864701, v := 2308632, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_865__GateII_HBoxData_0 : HBox :=
  { p := 5701, k := 864841, v := 2302901, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_866__GateII_HBoxData_0 : HBox :=
  { p := 5711, k := 865016, v := 2295769, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_867__GateII_HBoxData_0 : HBox :=
  { p := 5717, k := 865121, v := 2291508, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_868__GateII_HBoxData_0 : HBox :=
  { p := 5737, k := 865471, v := 2277394, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_869__GateII_HBoxData_0 : HBox :=
  { p := 5741, k := 865540, v := 2274584, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_870__GateII_HBoxData_0 : HBox :=
  { p := 5743, k := 865575, v := 2273183, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_871__GateII_HBoxData_0 : HBox :=
  { p := 5749, k := 865680, v := 2268989, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_872__GateII_HBoxData_0 : HBox :=
  { p := 5779, k := 866200, v := 2248183, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_873__GateII_HBoxData_0 : HBox :=
  { p := 5783, k := 866269, v := 2245431, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_874__GateII_HBoxData_0 : HBox :=
  { p := 5791, k := 866408, v := 2239948, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_875__GateII_HBoxData_0 : HBox :=
  { p := 5801, k := 866580, v := 2233115, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_876__GateII_HBoxData_0 : HBox :=
  { p := 5807, k := 866683, v := 2229031, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_877__GateII_HBoxData_0 : HBox :=
  { p := 5813, k := 866787, v := 2224965, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_878__GateII_HBoxData_0 : HBox :=
  { p := 5821, k := 866924, v := 2219552, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_879__GateII_HBoxData_0 : HBox :=
  { p := 5827, k := 867027, v := 2215509, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_880__GateII_HBoxData_0 : HBox :=
  { p := 5839, k := 867233, v := 2207457, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_881__GateII_HBoxData_0 : HBox :=
  { p := 5843, k := 867301, v := 2204780, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_882__GateII_HBoxData_0 : HBox :=
  { p := 5849, k := 867404, v := 2200780, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_883__GateII_HBoxData_0 : HBox :=
  { p := 5851, k := 867438, v := 2199448, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_884__GateII_HBoxData_0 : HBox :=
  { p := 5857, k := 867541, v := 2195464, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_885__GateII_HBoxData_0 : HBox :=
  { p := 5861, k := 867609, v := 2192811, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_886__GateII_HBoxData_0 : HBox :=
  { p := 5867, k := 867711, v := 2188841, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_887__GateII_HBoxData_0 : HBox :=
  { p := 5869, k := 867745, v := 2187520, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_888__GateII_HBoxData_0 : HBox :=
  { p := 5879, k := 867916, v := 2180942, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_889__GateII_HBoxData_0 : HBox :=
  { p := 5881, k := 867950, v := 2179629, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_890__GateII_HBoxData_0 : HBox :=
  { p := 5897, k := 868221, v := 2169167, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_891__GateII_HBoxData_0 : HBox :=
  { p := 5903, k := 868323, v := 2165267, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_892__GateII_HBoxData_0 : HBox :=
  { p := 5923, k := 868661, v := 2152339, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_893__GateII_HBoxData_0 : HBox :=
  { p := 5927, k := 868729, v := 2149770, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_894__GateII_HBoxData_0 : HBox :=
  { p := 5939, k := 868931, v := 2142084, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_895__GateII_HBoxData_0 : HBox :=
  { p := 5953, k := 869167, v := 2133176, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_896__GateII_HBoxData_0 : HBox :=
  { p := 5981, k := 869636, v := 2115524, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_897__GateII_HBoxData_0 : HBox :=
  { p := 5987, k := 869736, v := 2111770, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_898__GateII_HBoxData_0 : HBox :=
  { p := 6007, k := 870070, v := 2099338, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_899__GateII_HBoxData_0 : HBox :=
  { p := 6011, k := 870136, v := 2096862, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_900__GateII_HBoxData_0 : HBox :=
  { p := 6029, k := 870435, v := 2085789, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_901__GateII_HBoxData_0 : HBox :=
  { p := 6037, k := 870568, v := 2080899, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_902__GateII_HBoxData_0 : HBox :=
  { p := 6043, k := 870667, v := 2077239, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_903__GateII_HBoxData_0 : HBox :=
  { p := 6047, k := 870733, v := 2074806, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_904__GateII_HBoxData_0 : HBox :=
  { p := 6053, k := 870832, v := 2071164, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_905__GateII_HBoxData_0 : HBox :=
  { p := 6067, k := 871063, v := 2062707, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_906__GateII_HBoxData_0 : HBox :=
  { p := 6073, k := 871162, v := 2059100, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_907__GateII_HBoxData_0 : HBox :=
  { p := 6079, k := 871261, v := 2055503, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_908__GateII_HBoxData_0 : HBox :=
  { p := 6089, k := 871425, v := 2049526, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_909__GateII_HBoxData_0 : HBox :=
  { p := 6091, k := 871458, v := 2048335, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_910__GateII_HBoxData_0 : HBox :=
  { p := 6101, k := 871622, v := 2042392, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_911__GateII_HBoxData_0 : HBox :=
  { p := 6113, k := 871819, v := 2035299, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_912__GateII_HBoxData_0 : HBox :=
  { p := 6121, k := 871950, v := 2030590, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_913__GateII_HBoxData_0 : HBox :=
  { p := 6131, k := 872113, v := 2024726, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_914__GateII_HBoxData_0 : HBox :=
  { p := 6133, k := 872145, v := 2023554, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_915__GateII_HBoxData_0 : HBox :=
  { p := 6143, k := 872308, v := 2017723, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_916__GateII_HBoxData_0 : HBox :=
  { p := 6151, k := 872438, v := 2013076, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_917__GateII_HBoxData_0 : HBox :=
  { p := 6163, k := 872633, v := 2006139, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_918__GateII_HBoxData_0 : HBox :=
  { p := 6173, k := 872796, v := 2000389, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_919__GateII_HBoxData_0 : HBox :=
  { p := 6197, k := 873184, v := 1986685, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_920__GateII_HBoxData_0 : HBox :=
  { p := 6199, k := 873216, v := 1985548, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_921__GateII_HBoxData_0 : HBox :=
  { p := 6203, k := 873280, v := 1983278, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_922__GateII_HBoxData_0 : HBox :=
  { p := 6211, k := 873409, v := 1978755, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_923__GateII_HBoxData_0 : HBox :=
  { p := 6217, k := 873506, v := 1975375, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_924__GateII_HBoxData_0 : HBox :=
  { p := 6221, k := 873570, v := 1973124, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_925__GateII_HBoxData_0 : HBox :=
  { p := 6229, k := 873699, v := 1968639, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_926__GateII_HBoxData_0 : HBox :=
  { p := 6247, k := 873987, v := 1958597, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_927__GateII_HBoxData_0 : HBox :=
  { p := 6257, k := 874147, v := 1953055, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_928__GateII_HBoxData_0 : HBox :=
  { p := 6263, k := 874243, v := 1949741, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_929__GateII_HBoxData_0 : HBox :=
  { p := 6269, k := 874339, v := 1946437, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_930__GateII_HBoxData_0 : HBox :=
  { p := 6271, k := 874371, v := 1945338, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_931__GateII_HBoxData_0 : HBox :=
  { p := 6277, k := 874466, v := 1942041, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_932__GateII_HBoxData_0 : HBox :=
  { p := 6287, k := 874625, v := 1936570, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_933__GateII_HBoxData_0 : HBox :=
  { p := 6299, k := 874816, v := 1930039, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_934__GateII_HBoxData_0 : HBox :=
  { p := 6301, k := 874848, v := 1928955, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_935__GateII_HBoxData_0 : HBox :=
  { p := 6311, k := 875006, v := 1923539, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_936__GateII_HBoxData_0 : HBox :=
  { p := 6317, k := 875101, v := 1920303, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_937__GateII_HBoxData_0 : HBox :=
  { p := 6323, k := 875196, v := 1917075, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_938__GateII_HBoxData_0 : HBox :=
  { p := 6329, k := 875291, v := 1913856, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_939__GateII_HBoxData_0 : HBox :=
  { p := 6337, k := 875418, v := 1909580, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_940__GateII_HBoxData_0 : HBox :=
  { p := 6343, k := 875512, v := 1906377, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_941__GateII_HBoxData_0 : HBox :=
  { p := 6353, k := 875670, v := 1901064, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_942__GateII_HBoxData_0 : HBox :=
  { p := 6359, k := 875764, v := 1897885, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_943__GateII_HBoxData_0 : HBox :=
  { p := 6361, k := 875796, v := 1896830, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_944__GateII_HBoxData_0 : HBox :=
  { p := 6367, k := 875890, v := 1893662, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_945__GateII_HBoxData_0 : HBox :=
  { p := 6373, k := 875984, v := 1890502, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_946__GateII_HBoxData_0 : HBox :=
  { p := 6379, k := 876078, v := 1887352, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_947__GateII_HBoxData_0 : HBox :=
  { p := 6389, k := 876235, v := 1882121, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_948__GateII_HBoxData_0 : HBox :=
  { p := 6397, k := 876360, v := 1877950, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_949__GateII_HBoxData_0 : HBox :=
  { p := 6421, k := 876734, v := 1865525, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_950__GateII_HBoxData_0 : HBox :=
  { p := 6427, k := 876828, v := 1862442, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_951__GateII_HBoxData_0 : HBox :=
  { p := 6449, k := 877170, v := 1851195, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_952__GateII_HBoxData_0 : HBox :=
  { p := 6451, k := 877201, v := 1850178, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_953__GateII_HBoxData_0 : HBox :=
  { p := 6469, k := 877479, v := 1841060, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_954__GateII_HBoxData_0 : HBox :=
  { p := 6473, k := 877541, v := 1839044, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_955__GateII_HBoxData_0 : HBox :=
  { p := 6481, k := 877665, v := 1835024, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_956__GateII_HBoxData_0 : HBox :=
  { p := 6491, k := 877819, v := 1830014, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_957__GateII_HBoxData_0 : HBox :=
  { p := 6521, k := 878280, v := 1815115, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_958__GateII_HBoxData_0 : HBox :=
  { p := 6529, k := 878402, v := 1811171, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_959__GateII_HBoxData_0 : HBox :=
  { p := 6547, k := 878678, v := 1802355, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_960__GateII_HBoxData_0 : HBox :=
  { p := 6551, k := 878739, v := 1800404, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_961__GateII_HBoxData_0 : HBox :=
  { p := 6553, k := 878769, v := 1799427, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_962__GateII_HBoxData_0 : HBox :=
  { p := 6563, k := 878922, v := 1794571, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_963__GateII_HBoxData_0 : HBox :=
  { p := 6569, k := 879013, v := 1791664, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_964__GateII_HBoxData_0 : HBox :=
  { p := 6571, k := 879044, v := 1790700, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_965__GateII_HBoxData_0 : HBox :=
  { p := 6577, k := 879135, v := 1787803, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_966__GateII_HBoxData_0 : HBox :=
  { p := 6581, k := 879196, v := 1785878, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_967__GateII_HBoxData_0 : HBox :=
  { p := 6599, k := 879469, v := 1777249, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_968__GateII_HBoxData_0 : HBox :=
  { p := 6607, k := 879590, v := 1773434, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_969__GateII_HBoxData_0 : HBox :=
  { p := 6619, k := 879771, v := 1767735, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_970__GateII_HBoxData_0 : HBox :=
  { p := 6637, k := 880043, v := 1759244, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_971__GateII_HBoxData_0 : HBox :=
  { p := 6653, k := 880284, v := 1751749, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_972__GateII_HBoxData_0 : HBox :=
  { p := 6659, k := 880374, v := 1748950, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_973__GateII_HBoxData_0 : HBox :=
  { p := 6661, k := 880404, v := 1748019, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_974__GateII_HBoxData_0 : HBox :=
  { p := 6673, k := 880584, v := 1742448, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_975__GateII_HBoxData_0 : HBox :=
  { p := 6679, k := 880674, v := 1739673, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_976__GateII_HBoxData_0 : HBox :=
  { p := 6689, k := 880823, v := 1735061, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_977__GateII_HBoxData_0 : HBox :=
  { p := 6691, k := 880853, v := 1734142, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_978__GateII_HBoxData_0 : HBox :=
  { p := 6701, k := 881003, v := 1729557, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_979__GateII_HBoxData_0 : HBox :=
  { p := 6703, k := 881033, v := 1728643, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_980__GateII_HBoxData_0 : HBox :=
  { p := 6709, k := 881122, v := 1725900, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_981__GateII_HBoxData_0 : HBox :=
  { p := 6719, k := 881271, v := 1721347, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_982__GateII_HBoxData_0 : HBox :=
  { p := 6733, k := 881479, v := 1715003, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_983__GateII_HBoxData_0 : HBox :=
  { p := 6737, k := 881539, v := 1713200, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_984__GateII_HBoxData_0 : HBox :=
  { p := 6761, k := 881894, v := 1702425, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_985__GateII_HBoxData_0 : HBox :=
  { p := 6763, k := 881924, v := 1701534, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_986__GateII_HBoxData_0 : HBox :=
  { p := 6779, k := 882160, v := 1694415, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_987__GateII_HBoxData_0 : HBox :=
  { p := 6781, k := 882189, v := 1693527, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_988__GateII_HBoxData_0 : HBox :=
  { p := 6791, k := 882337, v := 1689108, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_989__GateII_HBoxData_0 : HBox :=
  { p := 6793, k := 882366, v := 1688224, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_990__GateII_HBoxData_0 : HBox :=
  { p := 6803, k := 882513, v := 1683824, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_991__GateII_HBoxData_0 : HBox :=
  { p := 6823, k := 882807, v := 1675080, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_992__GateII_HBoxData_0 : HBox :=
  { p := 6827, k := 882866, v := 1673341, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_993__GateII_HBoxData_0 : HBox :=
  { p := 6829, k := 882895, v := 1672470, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_994__GateII_HBoxData_0 : HBox :=
  { p := 6833, k := 882953, v := 1670732, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_995__GateII_HBoxData_0 : HBox :=
  { p := 6841, k := 883070, v := 1667267, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_996__GateII_HBoxData_0 : HBox :=
  { p := 6857, k := 883304, v := 1660373, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_997__GateII_HBoxData_0 : HBox :=
  { p := 6863, k := 883391, v := 1657796, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_998__GateII_HBoxData_0 : HBox :=
  { p := 6869, k := 883479, v := 1655230, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_999__GateII_HBoxData_0 : HBox :=
  { p := 6871, k := 883508, v := 1654375, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1000__GateII_HBoxData_0 : HBox :=
  { p := 6883, k := 883682, v := 1649260, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1001__GateII_HBoxData_0 : HBox :=
  { p := 6899, k := 883915, v := 1642482, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1002__GateII_HBoxData_0 : HBox :=
  { p := 6907, k := 884031, v := 1639109, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1003__GateII_HBoxData_0 : HBox :=
  { p := 6911, k := 884088, v := 1637422, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1004__GateII_HBoxData_0 : HBox :=
  { p := 6917, k := 884175, v := 1634904, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1005__GateII_HBoxData_0 : HBox :=
  { p := 6947, k := 884608, v := 1622398, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1006__GateII_HBoxData_0 : HBox :=
  { p := 6949, k := 884637, v := 1621570, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1007__GateII_HBoxData_0 : HBox :=
  { p := 6959, k := 884781, v := 1617438, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1008__GateII_HBoxData_0 : HBox :=
  { p := 6961, k := 884809, v := 1616611, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1009__GateII_HBoxData_0 : HBox :=
  { p := 6967, k := 884895, v := 1614141, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1010__GateII_HBoxData_0 : HBox :=
  { p := 6971, k := 884953, v := 1612500, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1011__GateII_HBoxData_0 : HBox :=
  { p := 6977, k := 885039, v := 1610039, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1012__GateII_HBoxData_0 : HBox :=
  { p := 6983, k := 885125, v := 1607585, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1013__GateII_HBoxData_0 : HBox :=
  { p := 6991, k := 885239, v := 1604320, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1014__GateII_HBoxData_0 : HBox :=
  { p := 6997, k := 885325, v := 1601881, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1015__GateII_HBoxData_0 : HBox :=
  { p := 7001, k := 885382, v := 1600256, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1016__GateII_HBoxData_0 : HBox :=
  { p := 7013, k := 885554, v := 1595403, N := 26, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1017__GateII_HBoxData_0 : HBox :=
  { p := 7019, k := 885639, v := 1592981, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1018__GateII_HBoxData_0 : HBox :=
  { p := 7027, k := 885753, v := 1589764, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1019__GateII_HBoxData_0 : HBox :=
  { p := 7039, k := 885924, v := 1584959, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1020__GateII_HBoxData_0 : HBox :=
  { p := 7043, k := 885980, v := 1583359, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1021__GateII_HBoxData_0 : HBox :=
  { p := 7057, k := 886179, v := 1577789, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1022__GateII_HBoxData_0 : HBox :=
  { p := 7069, k := 886349, v := 1573039, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1023__GateII_HBoxData_0 : HBox :=
  { p := 7079, k := 886490, v := 1569096, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1024__GateII_HBoxData_0 : HBox :=
  { p := 7103, k := 886829, v := 1559699, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1025__GateII_HBoxData_0 : HBox :=
  { p := 7109, k := 886913, v := 1557362, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1026__GateII_HBoxData_0 : HBox :=
  { p := 7121, k := 887082, v := 1552708, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1027__GateII_HBoxData_0 : HBox :=
  { p := 7127, k := 887166, v := 1550387, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1028__GateII_HBoxData_0 : HBox :=
  { p := 7129, k := 887194, v := 1549615, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1029__GateII_HBoxData_0 : HBox :=
  { p := 7151, k := 887502, v := 1541162, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1030__GateII_HBoxData_0 : HBox :=
  { p := 7159, k := 887614, v := 1538106, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1031__GateII_HBoxData_0 : HBox :=
  { p := 7177, k := 887865, v := 1531264, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1032__GateII_HBoxData_0 : HBox :=
  { p := 7187, k := 888004, v := 1527483, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1033__GateII_HBoxData_0 : HBox :=
  { p := 7193, k := 888088, v := 1525224, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1034__GateII_HBoxData_0 : HBox :=
  { p := 7207, k := 888282, v := 1519966, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1035__GateII_HBoxData_0 : HBox :=
  { p := 7211, k := 888338, v := 1518471, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1036__GateII_HBoxData_0 : HBox :=
  { p := 7213, k := 888366, v := 1517725, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1037__GateII_HBoxData_0 : HBox :=
  { p := 7219, k := 888449, v := 1515485, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1038__GateII_HBoxData_0 : HBox :=
  { p := 7229, k := 888587, v := 1511764, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1039__GateII_HBoxData_0 : HBox :=
  { p := 7237, k := 888698, v := 1508799, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1040__GateII_HBoxData_0 : HBox :=
  { p := 7243, k := 888781, v := 1506581, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1041__GateII_HBoxData_0 : HBox :=
  { p := 7247, k := 888836, v := 1505104, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1042__GateII_HBoxData_0 : HBox :=
  { p := 7253, k := 888919, v := 1502895, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1043__GateII_HBoxData_0 : HBox :=
  { p := 7283, k := 889331, v := 1491918, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1044__GateII_HBoxData_0 : HBox :=
  { p := 7297, k := 889523, v := 1486839, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1045__GateII_HBoxData_0 : HBox :=
  { p := 7307, k := 889660, v := 1483228, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1046__GateII_HBoxData_0 : HBox :=
  { p := 7309, k := 889688, v := 1482509, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1047__GateII_HBoxData_0 : HBox :=
  { p := 7321, k := 889852, v := 1478197, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1048__GateII_HBoxData_0 : HBox :=
  { p := 7331, k := 889988, v := 1474616, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1049__GateII_HBoxData_0 : HBox :=
  { p := 7333, k := 890015, v := 1473901, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1050__GateII_HBoxData_0 : HBox :=
  { p := 7349, k := 890233, v := 1468207, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1051__GateII_HBoxData_0 : HBox :=
  { p := 7351, k := 890261, v := 1467501, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1052__GateII_HBoxData_0 : HBox :=
  { p := 7369, k := 890505, v := 1461139, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1053__GateII_HBoxData_0 : HBox :=
  { p := 7393, k := 890830, v := 1452725, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1054__GateII_HBoxData_0 : HBox :=
  { p := 7411, k := 891074, v := 1446467, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1055__GateII_HBoxData_0 : HBox :=
  { p := 7417, k := 891154, v := 1444386, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1056__GateII_HBoxData_0 : HBox :=
  { p := 7433, k := 891370, v := 1438870, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1057__GateII_HBoxData_0 : HBox :=
  { p := 7451, k := 891612, v := 1432702, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1058__GateII_HBoxData_0 : HBox :=
  { p := 7457, k := 891692, v := 1430654, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1059__GateII_HBoxData_0 : HBox :=
  { p := 7459, k := 891719, v := 1429973, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1060__GateII_HBoxData_0 : HBox :=
  { p := 7477, k := 891960, v := 1423864, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1061__GateII_HBoxData_0 : HBox :=
  { p := 7481, k := 892014, v := 1422514, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1062__GateII_HBoxData_0 : HBox :=
  { p := 7487, k := 892094, v := 1420489, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1063__GateII_HBoxData_0 : HBox :=
  { p := 7489, k := 892121, v := 1419816, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1064__GateII_HBoxData_0 : HBox :=
  { p := 7499, k := 892254, v := 1416453, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1065__GateII_HBoxData_0 : HBox :=
  { p := 7507, k := 892361, v := 1413774, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1066__GateII_HBoxData_0 : HBox :=
  { p := 7517, k := 892494, v := 1410434, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1067__GateII_HBoxData_0 : HBox :=
  { p := 7523, k := 892574, v := 1408437, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1068__GateII_HBoxData_0 : HBox :=
  { p := 7529, k := 892653, v := 1406441, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1069__GateII_HBoxData_0 : HBox :=
  { p := 7537, k := 892759, v := 1403790, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1070__GateII_HBoxData_0 : HBox :=
  { p := 7541, k := 892813, v := 1402470, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1071__GateII_HBoxData_0 : HBox :=
  { p := 7547, k := 892892, v := 1400488, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1072__GateII_HBoxData_0 : HBox :=
  { p := 7549, k := 892919, v := 1399831, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1073__GateII_HBoxData_0 : HBox :=
  { p := 7559, k := 893051, v := 1396541, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1074__GateII_HBoxData_0 : HBox :=
  { p := 7561, k := 893077, v := 1395884, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1075__GateII_HBoxData_0 : HBox :=
  { p := 7573, k := 893236, v := 1391958, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1076__GateII_HBoxData_0 : HBox :=
  { p := 7577, k := 893289, v := 1390653, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1077__GateII_HBoxData_0 : HBox :=
  { p := 7583, k := 893368, v := 1388698, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1078__GateII_HBoxData_0 : HBox :=
  { p := 7589, k := 893447, v := 1386748, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1079__GateII_HBoxData_0 : HBox :=
  { p := 7591, k := 893473, v := 1386098, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1080__GateII_HBoxData_0 : HBox :=
  { p := 7603, k := 893631, v := 1382213, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1081__GateII_HBoxData_0 : HBox :=
  { p := 7607, k := 893684, v := 1380924, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1082__GateII_HBoxData_0 : HBox :=
  { p := 7621, k := 893868, v := 1376420, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1083__GateII_HBoxData_0 : HBox :=
  { p := 7639, k := 894104, v := 1370663, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1084__GateII_HBoxData_0 : HBox :=
  { p := 7643, k := 894156, v := 1369387, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1085__GateII_HBoxData_0 : HBox :=
  { p := 7649, k := 894235, v := 1367481, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1086__GateII_HBoxData_0 : HBox :=
  { p := 7669, k := 894496, v := 1361150, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1087__GateII_HBoxData_0 : HBox :=
  { p := 7673, k := 894548, v := 1359889, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1088__GateII_HBoxData_0 : HBox :=
  { p := 7681, k := 894652, v := 1357373, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1089__GateII_HBoxData_0 : HBox :=
  { p := 7687, k := 894730, v := 1355490, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1090__GateII_HBoxData_0 : HBox :=
  { p := 7691, k := 894782, v := 1354238, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1091__GateII_HBoxData_0 : HBox :=
  { p := 7699, k := 894886, v := 1351738, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1092__GateII_HBoxData_0 : HBox :=
  { p := 7703, k := 894938, v := 1350491, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1093__GateII_HBoxData_0 : HBox :=
  { p := 7717, k := 895120, v := 1346142, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1094__GateII_HBoxData_0 : HBox :=
  { p := 7723, k := 895197, v := 1344282, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1095__GateII_HBoxData_0 : HBox :=
  { p := 7727, k := 895249, v := 1343046, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1096__GateII_HBoxData_0 : HBox :=
  { p := 7741, k := 895430, v := 1338732, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1097__GateII_HBoxData_0 : HBox :=
  { p := 7753, k := 895585, v := 1335052, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1098__GateII_HBoxData_0 : HBox :=
  { p := 7757, k := 895637, v := 1333830, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1099__GateII_HBoxData_0 : HBox :=
  { p := 7759, k := 895662, v := 1333217, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1100__GateII_HBoxData_0 : HBox :=
  { p := 7789, k := 896048, v := 1324105, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1101__GateII_HBoxData_0 : HBox :=
  { p := 7793, k := 896100, v := 1322899, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1102__GateII_HBoxData_0 : HBox :=
  { p := 7817, k := 896407, v := 1315687, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1103__GateII_HBoxData_0 : HBox :=
  { p := 7823, k := 896484, v := 1313895, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1104__GateII_HBoxData_0 : HBox :=
  { p := 7829, k := 896561, v := 1312107, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1105__GateII_HBoxData_0 : HBox :=
  { p := 7841, k := 896714, v := 1308539, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1106__GateII_HBoxData_0 : HBox :=
  { p := 7853, k := 896867, v := 1304987, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1107__GateII_HBoxData_0 : HBox :=
  { p := 7867, k := 897045, v := 1300862, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1108__GateII_HBoxData_0 : HBox :=
  { p := 7873, k := 897121, v := 1299099, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1109__GateII_HBoxData_0 : HBox :=
  { p := 7877, k := 897172, v := 1297928, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1110__GateII_HBoxData_0 : HBox :=
  { p := 7879, k := 897197, v := 1297341, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1111__GateII_HBoxData_0 : HBox :=
  { p := 7883, k := 897248, v := 1296172, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1112__GateII_HBoxData_0 : HBox :=
  { p := 7901, k := 897476, v := 1290927, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1113__GateII_HBoxData_0 : HBox :=
  { p := 7907, k := 897552, v := 1289186, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1114__GateII_HBoxData_0 : HBox :=
  { p := 7919, k := 897704, v := 1285716, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1115__GateII_HBoxData_0 : HBox :=
  { p := 7927, k := 897804, v := 1283408, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1116__GateII_HBoxData_0 : HBox :=
  { p := 7933, k := 897880, v := 1281684, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1117__GateII_HBoxData_0 : HBox :=
  { p := 7937, k := 897931, v := 1280537, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1118__GateII_HBoxData_0 : HBox :=
  { p := 7949, k := 898082, v := 1277102, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1119__GateII_HBoxData_0 : HBox :=
  { p := 7951, k := 898107, v := 1276531, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1120__GateII_HBoxData_0 : HBox :=
  { p := 7963, k := 898258, v := 1273113, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1121__GateII_HBoxData_0 : HBox :=
  { p := 7993, k := 898634, v := 1264630, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1122__GateII_HBoxData_0 : HBox :=
  { p := 8009, k := 898834, v := 1260142, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1123__GateII_HBoxData_0 : HBox :=
  { p := 8011, k := 898859, v := 1259583, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1124__GateII_HBoxData_0 : HBox :=
  { p := 8017, k := 898933, v := 1257905, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1125__GateII_HBoxData_0 : HBox :=
  { p := 8039, k := 899207, v := 1251790, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1126__GateII_HBoxData_0 : HBox :=
  { p := 8053, k := 899381, v := 1247923, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1127__GateII_HBoxData_0 : HBox :=
  { p := 8059, k := 899456, v := 1246273, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1128__GateII_HBoxData_0 : HBox :=
  { p := 8069, k := 899580, v := 1243528, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1129__GateII_HBoxData_0 : HBox :=
  { p := 8081, k := 899729, v := 1240248, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1130__GateII_HBoxData_0 : HBox :=
  { p := 8087, k := 899803, v := 1238611, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1131__GateII_HBoxData_0 : HBox :=
  { p := 8089, k := 899828, v := 1238067, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1132__GateII_HBoxData_0 : HBox :=
  { p := 8093, k := 899877, v := 1236978, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1133__GateII_HBoxData_0 : HBox :=
  { p := 8101, k := 899976, v := 1234807, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1134__GateII_HBoxData_0 : HBox :=
  { p := 8111, k := 900099, v := 1232100, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1135__GateII_HBoxData_0 : HBox :=
  { p := 8117, k := 900173, v := 1230481, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1136__GateII_HBoxData_0 : HBox :=
  { p := 8123, k := 900247, v := 1228866, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1137__GateII_HBoxData_0 : HBox :=
  { p := 8147, k := 900542, v := 1222435, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1138__GateII_HBoxData_0 : HBox :=
  { p := 8161, k := 900714, v := 1218709, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1139__GateII_HBoxData_0 : HBox :=
  { p := 8167, k := 900787, v := 1217116, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1140__GateII_HBoxData_0 : HBox :=
  { p := 8171, k := 900836, v := 1216057, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1141__GateII_HBoxData_0 : HBox :=
  { p := 8179, k := 900934, v := 1213943, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1142__GateII_HBoxData_0 : HBox :=
  { p := 8191, k := 901081, v := 1210782, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1143__GateII_HBoxData_0 : HBox :=
  { p := 8209, k := 901300, v := 1206063, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1144__GateII_HBoxData_0 : HBox :=
  { p := 8219, k := 901422, v := 1203455, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1145__GateII_HBoxData_0 : HBox :=
  { p := 8221, k := 901446, v := 1202934, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1146__GateII_HBoxData_0 : HBox :=
  { p := 8231, k := 901568, v := 1200337, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1147__GateII_HBoxData_0 : HBox :=
  { p := 8233, k := 901592, v := 1199817, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1148__GateII_HBoxData_0 : HBox :=
  { p := 8237, k := 901641, v := 1198782, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1149__GateII_HBoxData_0 : HBox :=
  { p := 8243, k := 901713, v := 1197228, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1150__GateII_HBoxData_0 : HBox :=
  { p := 8263, k := 901956, v := 1192081, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1151__GateII_HBoxData_0 : HBox :=
  { p := 8269, k := 902028, v := 1190541, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1152__GateII_HBoxData_0 : HBox :=
  { p := 8273, k := 902077, v := 1189519, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1153__GateII_HBoxData_0 : HBox :=
  { p := 8287, k := 902246, v := 1185946, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1154__GateII_HBoxData_0 : HBox :=
  { p := 8291, k := 902294, v := 1184928, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1155__GateII_HBoxData_0 : HBox :=
  { p := 8293, k := 902318, v := 1184420, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1156__GateII_HBoxData_0 : HBox :=
  { p := 8297, k := 902366, v := 1183403, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1157__GateII_HBoxData_0 : HBox :=
  { p := 8311, k := 902535, v := 1179861, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1158__GateII_HBoxData_0 : HBox :=
  { p := 8317, k := 902607, v := 1178347, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1159__GateII_HBoxData_0 : HBox :=
  { p := 8329, k := 902751, v := 1175328, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1160__GateII_HBoxData_0 : HBox :=
  { p := 8353, k := 903039, v := 1169328, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1161__GateII_HBoxData_0 : HBox :=
  { p := 8363, k := 903159, v := 1166842, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1162__GateII_HBoxData_0 : HBox :=
  { p := 8369, k := 903230, v := 1165353, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1163__GateII_HBoxData_0 : HBox :=
  { p := 8377, k := 903326, v := 1163375, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1164__GateII_HBoxData_0 : HBox :=
  { p := 8387, k := 903445, v := 1160907, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1165__GateII_HBoxData_0 : HBox :=
  { p := 8389, k := 903469, v := 1160415, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1166__GateII_HBoxData_0 : HBox :=
  { p := 8419, k := 903826, v := 1153069, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1167__GateII_HBoxData_0 : HBox :=
  { p := 8423, k := 903874, v := 1152096, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1168__GateII_HBoxData_0 : HBox :=
  { p := 8429, k := 903945, v := 1150637, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1169__GateII_HBoxData_0 : HBox :=
  { p := 8431, k := 903969, v := 1150152, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1170__GateII_HBoxData_0 : HBox :=
  { p := 8443, k := 904111, v := 1147244, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1171__GateII_HBoxData_0 : HBox :=
  { p := 8447, k := 904158, v := 1146277, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1172__GateII_HBoxData_0 : HBox :=
  { p := 8461, k := 904324, v := 1142905, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1173__GateII_HBoxData_0 : HBox :=
  { p := 8467, k := 904395, v := 1141465, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1174__GateII_HBoxData_0 : HBox :=
  { p := 8501, k := 904795, v := 1133352, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1175__GateII_HBoxData_0 : HBox :=
  { p := 8513, k := 904936, v := 1130511, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1176__GateII_HBoxData_0 : HBox :=
  { p := 8521, k := 905030, v := 1128623, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1177__GateII_HBoxData_0 : HBox :=
  { p := 8527, k := 905101, v := 1127212, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1178__GateII_HBoxData_0 : HBox :=
  { p := 8537, k := 905218, v := 1124863, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1179__GateII_HBoxData_0 : HBox :=
  { p := 8539, k := 905241, v := 1124393, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1180__GateII_HBoxData_0 : HBox :=
  { p := 8543, k := 905288, v := 1123456, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1181__GateII_HBoxData_0 : HBox :=
  { p := 8563, k := 905522, v := 1118792, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1182__GateII_HBoxData_0 : HBox :=
  { p := 8573, k := 905639, v := 1116471, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1183__GateII_HBoxData_0 : HBox :=
  { p := 8581, k := 905732, v := 1114619, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1184__GateII_HBoxData_0 : HBox :=
  { p := 8597, k := 905918, v := 1110929, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1185__GateII_HBoxData_0 : HBox :=
  { p := 8599, k := 905942, v := 1110471, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1186__GateII_HBoxData_0 : HBox :=
  { p := 8609, k := 906058, v := 1108176, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1187__GateII_HBoxData_0 : HBox :=
  { p := 8623, k := 906220, v := 1104974, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1188__GateII_HBoxData_0 : HBox :=
  { p := 8627, k := 906267, v := 1104064, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1189__GateII_HBoxData_0 : HBox :=
  { p := 8629, k := 906290, v := 1103608, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1190__GateII_HBoxData_0 : HBox :=
  { p := 8641, k := 906429, v := 1100882, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1191__GateII_HBoxData_0 : HBox :=
  { p := 8647, k := 906498, v := 1099522, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1192__GateII_HBoxData_0 : HBox :=
  { p := 8663, k := 906683, v := 1095910, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1193__GateII_HBoxData_0 : HBox :=
  { p := 8669, k := 906752, v := 1094560, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1194__GateII_HBoxData_0 : HBox :=
  { p := 8677, k := 906845, v := 1092766, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1195__GateII_HBoxData_0 : HBox :=
  { p := 8681, k := 906891, v := 1091870, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1196__GateII_HBoxData_0 : HBox :=
  { p := 8689, k := 906983, v := 1090081, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1197__GateII_HBoxData_0 : HBox :=
  { p := 8693, k := 907029, v := 1089188, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1198__GateII_HBoxData_0 : HBox :=
  { p := 8699, k := 907098, v := 1087852, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1199__GateII_HBoxData_0 : HBox :=
  { p := 8707, k := 907190, v := 1086073, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1200__GateII_HBoxData_0 : HBox :=
  { p := 8713, k := 907259, v := 1084743, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1201__GateII_HBoxData_0 : HBox :=
  { p := 8719, k := 907327, v := 1083412, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1202__GateII_HBoxData_0 : HBox :=
  { p := 8731, k := 907465, v := 1080764, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1203__GateII_HBoxData_0 : HBox :=
  { p := 8737, k := 907534, v := 1079444, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1204__GateII_HBoxData_0 : HBox :=
  { p := 8741, k := 907579, v := 1078563, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1205__GateII_HBoxData_0 : HBox :=
  { p := 8747, k := 907648, v := 1077247, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1206__GateII_HBoxData_0 : HBox :=
  { p := 8753, k := 907717, v := 1075934, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1207__GateII_HBoxData_0 : HBox :=
  { p := 8761, k := 907808, v := 1074185, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1208__GateII_HBoxData_0 : HBox :=
  { p := 8779, k := 908013, v := 1070267, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1209__GateII_HBoxData_0 : HBox :=
  { p := 8783, k := 908059, v := 1069400, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1210__GateII_HBoxData_0 : HBox :=
  { p := 8803, k := 908286, v := 1065078, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1211__GateII_HBoxData_0 : HBox :=
  { p := 8807, k := 908332, v := 1064218, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1212__GateII_HBoxData_0 : HBox :=
  { p := 8819, k := 908468, v := 1061641, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1213__GateII_HBoxData_0 : HBox :=
  { p := 8821, k := 908491, v := 1061213, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1214__GateII_HBoxData_0 : HBox :=
  { p := 8831, k := 908604, v := 1059074, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1215__GateII_HBoxData_0 : HBox :=
  { p := 8837, k := 908672, v := 1057795, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1216__GateII_HBoxData_0 : HBox :=
  { p := 8839, k := 908694, v := 1057367, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1217__GateII_HBoxData_0 : HBox :=
  { p := 8849, k := 908807, v := 1055241, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1218__GateII_HBoxData_0 : HBox :=
  { p := 8861, k := 908943, v := 1052699, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1219__GateII_HBoxData_0 : HBox :=
  { p := 8863, k := 908966, v := 1052277, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1220__GateII_HBoxData_0 : HBox :=
  { p := 8867, k := 909011, v := 1051432, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1221__GateII_HBoxData_0 : HBox :=
  { p := 8887, k := 909236, v := 1047222, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1222__GateII_HBoxData_0 : HBox :=
  { p := 8893, k := 909303, v := 1045963, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1223__GateII_HBoxData_0 : HBox :=
  { p := 8923, k := 909640, v := 1039710, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1224__GateII_HBoxData_0 : HBox :=
  { p := 8929, k := 909707, v := 1038466, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1225__GateII_HBoxData_0 : HBox :=
  { p := 8933, k := 909752, v := 1037638, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1226__GateII_HBoxData_0 : HBox :=
  { p := 8941, k := 909842, v := 1035987, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1227__GateII_HBoxData_0 : HBox :=
  { p := 8951, k := 909954, v := 1033927, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1228__GateII_HBoxData_0 : HBox :=
  { p := 8963, k := 910088, v := 1031464, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1229__GateII_HBoxData_0 : HBox :=
  { p := 8969, k := 910154, v := 1030233, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1230__GateII_HBoxData_0 : HBox :=
  { p := 8971, k := 910177, v := 1029826, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1231__GateII_HBoxData_0 : HBox :=
  { p := 8999, k := 910488, v := 1024126, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1232__GateII_HBoxData_0 : HBox :=
  { p := 9001, k := 910511, v := 1023722, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1233__GateII_HBoxData_0 : HBox :=
  { p := 9007, k := 910577, v := 1022507, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1234__GateII_HBoxData_0 : HBox :=
  { p := 9011, k := 910622, v := 1021700, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1235__GateII_HBoxData_0 : HBox :=
  { p := 9013, k := 910644, v := 1021296, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1236__GateII_HBoxData_0 : HBox :=
  { p := 9029, k := 910821, v := 1018074, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1237__GateII_HBoxData_0 : HBox :=
  { p := 9041, k := 910954, v := 1015669, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1238__GateII_HBoxData_0 : HBox :=
  { p := 9043, k := 910976, v := 1015269, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1239__GateII_HBoxData_0 : HBox :=
  { p := 9049, k := 911042, v := 1014070, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1240__GateII_HBoxData_0 : HBox :=
  { p := 9059, k := 911153, v := 1012078, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1241__GateII_HBoxData_0 : HBox :=
  { p := 9067, k := 911241, v := 1010488, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1242__GateII_HBoxData_0 : HBox :=
  { p := 9091, k := 911506, v := 1005743, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1243__GateII_HBoxData_0 : HBox :=
  { p := 9103, k := 911637, v := 1003381, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1244__GateII_HBoxData_0 : HBox :=
  { p := 9109, k := 911703, v := 1002204, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1245__GateII_HBoxData_0 : HBox :=
  { p := 9127, k := 911901, v := 998688, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1246__GateII_HBoxData_0 : HBox :=
  { p := 9133, k := 911966, v := 997518, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1247__GateII_HBoxData_0 : HBox :=
  { p := 9137, k := 912010, v := 996741, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1248__GateII_HBoxData_0 : HBox :=
  { p := 9151, k := 912163, v := 994026, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1249__GateII_HBoxData_0 : HBox :=
  { p := 9157, k := 912229, v := 992867, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1250__GateII_HBoxData_0 : HBox :=
  { p := 9161, k := 912273, v := 992096, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1251__GateII_HBoxData_0 : HBox :=
  { p := 9173, k := 912403, v := 989784, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1252__GateII_HBoxData_0 : HBox :=
  { p := 9181, k := 912491, v := 988250, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1253__GateII_HBoxData_0 : HBox :=
  { p := 9187, k := 912556, v := 987100, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1254__GateII_HBoxData_0 : HBox :=
  { p := 9199, k := 912687, v := 984808, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1255__GateII_HBoxData_0 : HBox :=
  { p := 9203, k := 912730, v := 984045, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1256__GateII_HBoxData_0 : HBox :=
  { p := 9209, k := 912795, v := 982902, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1257__GateII_HBoxData_0 : HBox :=
  { p := 9221, k := 912925, v := 980625, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1258__GateII_HBoxData_0 : HBox :=
  { p := 9227, k := 912990, v := 979489, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1259__GateII_HBoxData_0 : HBox :=
  { p := 9239, k := 913120, v := 977224, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1260__GateII_HBoxData_0 : HBox :=
  { p := 9241, k := 913142, v := 976848, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1261__GateII_HBoxData_0 : HBox :=
  { p := 9257, k := 913315, v := 973842, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1262__GateII_HBoxData_0 : HBox :=
  { p := 9277, k := 913531, v := 970105, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1263__GateII_HBoxData_0 : HBox :=
  { p := 9281, k := 913574, v := 969361, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1264__GateII_HBoxData_0 : HBox :=
  { p := 9283, k := 913596, v := 968989, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1265__GateII_HBoxData_0 : HBox :=
  { p := 9293, k := 913703, v := 967131, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1266__GateII_HBoxData_0 : HBox :=
  { p := 9311, k := 913897, v := 963804, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1267__GateII_HBoxData_0 : HBox :=
  { p := 9319, k := 913983, v := 962331, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1268__GateII_HBoxData_0 : HBox :=
  { p := 9323, k := 914025, v := 961593, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1269__GateII_HBoxData_0 : HBox :=
  { p := 9337, k := 914176, v := 959028, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1270__GateII_HBoxData_0 : HBox :=
  { p := 9341, k := 914218, v := 958295, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1271__GateII_HBoxData_0 : HBox :=
  { p := 9343, k := 914240, v := 957930, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1272__GateII_HBoxData_0 : HBox :=
  { p := 9349, k := 914304, v := 956835, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1273__GateII_HBoxData_0 : HBox :=
  { p := 9371, k := 914539, v := 952836, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1274__GateII_HBoxData_0 : HBox :=
  { p := 9377, k := 914603, v := 951750, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1275__GateII_HBoxData_0 : HBox :=
  { p := 9391, k := 914752, v := 949223, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1276__GateII_HBoxData_0 : HBox :=
  { p := 9397, k := 914816, v := 948144, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1277__GateII_HBoxData_0 : HBox :=
  { p := 9403, k := 914880, v := 947066, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1278__GateII_HBoxData_0 : HBox :=
  { p := 9413, k := 914986, v := 945274, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1279__GateII_HBoxData_0 : HBox :=
  { p := 9419, k := 915050, v := 944202, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1280__GateII_HBoxData_0 : HBox :=
  { p := 9421, k := 915071, v := 943844, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1281__GateII_HBoxData_0 : HBox :=
  { p := 9431, k := 915177, v := 942061, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1282__GateII_HBoxData_0 : HBox :=
  { p := 9433, k := 915198, v := 941705, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1283__GateII_HBoxData_0 : HBox :=
  { p := 9437, k := 915241, v := 940995, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1284__GateII_HBoxData_0 : HBox :=
  { p := 9439, k := 915262, v := 940639, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1285__GateII_HBoxData_0 : HBox :=
  { p := 9461, k := 915495, v := 936746, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1286__GateII_HBoxData_0 : HBox :=
  { p := 9463, k := 915516, v := 936393, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1287__GateII_HBoxData_0 : HBox :=
  { p := 9467, k := 915558, v := 935687, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1288__GateII_HBoxData_0 : HBox :=
  { p := 9473, k := 915622, v := 934633, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1289__GateII_HBoxData_0 : HBox :=
  { p := 9479, k := 915685, v := 933578, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1290__GateII_HBoxData_0 : HBox :=
  { p := 9491, k := 915811, v := 931475, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1291__GateII_HBoxData_0 : HBox :=
  { p := 9497, k := 915875, v := 930428, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1292__GateII_HBoxData_0 : HBox :=
  { p := 9511, k := 916022, v := 927988, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1293__GateII_HBoxData_0 : HBox :=
  { p := 9521, k := 916127, v := 926252, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1294__GateII_HBoxData_0 : HBox :=
  { p := 9533, k := 916253, v := 924175, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1295__GateII_HBoxData_0 : HBox :=
  { p := 9539, k := 916316, v := 923139, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1296__GateII_HBoxData_0 : HBox :=
  { p := 9547, k := 916400, v := 921761, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1297__GateII_HBoxData_0 : HBox :=
  { p := 9551, k := 916442, v := 921074, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1298__GateII_HBoxData_0 : HBox :=
  { p := 9587, k := 916818, v := 914918, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1299__GateII_HBoxData_0 : HBox :=
  { p := 9601, k := 916964, v := 912542, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1300__GateII_HBoxData_0 : HBox :=
  { p := 9613, k := 917089, v := 910513, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1301__GateII_HBoxData_0 : HBox :=
  { p := 9619, k := 917151, v := 909500, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1302__GateII_HBoxData_0 : HBox :=
  { p := 9623, k := 917193, v := 908827, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1303__GateII_HBoxData_0 : HBox :=
  { p := 9629, k := 917255, v := 907817, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1304__GateII_HBoxData_0 : HBox :=
  { p := 9631, k := 917276, v := 907482, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1305__GateII_HBoxData_0 : HBox :=
  { p := 9643, k := 917400, v := 905469, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1306__GateII_HBoxData_0 : HBox :=
  { p := 9649, k := 917462, v := 904465, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1307__GateII_HBoxData_0 : HBox :=
  { p := 9661, k := 917587, v := 902465, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1308__GateII_HBoxData_0 : HBox :=
  { p := 9677, k := 917752, v := 899806, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1309__GateII_HBoxData_0 : HBox :=
  { p := 9679, k := 917773, v := 899475, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1310__GateII_HBoxData_0 : HBox :=
  { p := 9689, k := 917876, v := 897821, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1311__GateII_HBoxData_0 : HBox :=
  { p := 9697, k := 917959, v := 896502, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1312__GateII_HBoxData_0 : HBox :=
  { p := 9719, k := 918185, v := 892886, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1313__GateII_HBoxData_0 : HBox :=
  { p := 9721, k := 918206, v := 892560, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1314__GateII_HBoxData_0 : HBox :=
  { p := 9733, k := 918329, v := 890598, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1315__GateII_HBoxData_0 : HBox :=
  { p := 9739, k := 918391, v := 889621, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1316__GateII_HBoxData_0 : HBox :=
  { p := 9743, k := 918432, v := 888970, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1317__GateII_HBoxData_0 : HBox :=
  { p := 9749, k := 918493, v := 887994, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1318__GateII_HBoxData_0 : HBox :=
  { p := 9767, k := 918678, v := 885080, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1319__GateII_HBoxData_0 : HBox :=
  { p := 9769, k := 918698, v := 884756, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1320__GateII_HBoxData_0 : HBox :=
  { p := 9781, k := 918821, v := 882822, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1321__GateII_HBoxData_0 : HBox :=
  { p := 9787, k := 918883, v := 881859, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1322__GateII_HBoxData_0 : HBox :=
  { p := 9791, k := 918923, v := 881215, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1323__GateII_HBoxData_0 : HBox :=
  { p := 9803, k := 919046, v := 879294, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1324__GateII_HBoxData_0 : HBox :=
  { p := 9811, k := 919127, v := 878015, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1325__GateII_HBoxData_0 : HBox :=
  { p := 9817, k := 919189, v := 877060, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1326__GateII_HBoxData_0 : HBox :=
  { p := 9829, k := 919311, v := 875151, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1327__GateII_HBoxData_0 : HBox :=
  { p := 9833, k := 919351, v := 874516, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1328__GateII_HBoxData_0 : HBox :=
  { p := 9839, k := 919412, v := 873565, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1329__GateII_HBoxData_0 : HBox :=
  { p := 9851, k := 919534, v := 871669, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1330__GateII_HBoxData_0 : HBox :=
  { p := 9857, k := 919595, v := 870723, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1331__GateII_HBoxData_0 : HBox :=
  { p := 9859, k := 919616, v := 870410, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1332__GateII_HBoxData_0 : HBox :=
  { p := 9871, k := 919737, v := 868523, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1333__GateII_HBoxData_0 : HBox :=
  { p := 9883, k := 919859, v := 866644, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1334__GateII_HBoxData_0 : HBox :=
  { p := 9887, k := 919899, v := 866019, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1335__GateII_HBoxData_0 : HBox :=
  { p := 9901, k := 920041, v := 863837, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1336__GateII_HBoxData_0 : HBox :=
  { p := 9907, k := 920101, v := 862904, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1337__GateII_HBoxData_0 : HBox :=
  { p := 9923, k := 920263, v := 860425, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1338__GateII_HBoxData_0 : HBox :=
  { p := 9929, k := 920323, v := 859498, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1339__GateII_HBoxData_0 : HBox :=
  { p := 9931, k := 920343, v := 859189, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1340__GateII_HBoxData_0 : HBox :=
  { p := 9941, k := 920444, v := 857649, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1341__GateII_HBoxData_0 : HBox :=
  { p := 9949, k := 920524, v := 856419, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1342__GateII_HBoxData_0 : HBox :=
  { p := 9967, k := 920705, v := 853663, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1343__GateII_HBoxData_0 : HBox :=
  { p := 9973, k := 920765, v := 852747, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1344__GateII_HBoxData_0 : HBox :=
  { p := 10007, k := 921106, v := 847589, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1345__GateII_HBoxData_0 : HBox :=
  { p := 10009, k := 921125, v := 847285, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1346__GateII_HBoxData_0 : HBox :=
  { p := 10037, k := 921405, v := 843076, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1347__GateII_HBoxData_0 : HBox :=
  { p := 10039, k := 921425, v := 842776, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1348__GateII_HBoxData_0 : HBox :=
  { p := 10061, k := 921644, v := 839493, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1349__GateII_HBoxData_0 : HBox :=
  { p := 10067, k := 921703, v := 838600, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1350__GateII_HBoxData_0 : HBox :=
  { p := 10069, k := 921723, v := 838303, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1351__GateII_HBoxData_0 : HBox :=
  { p := 10079, k := 921822, v := 836820, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1352__GateII_HBoxData_0 : HBox :=
  { p := 10091, k := 921941, v := 835046, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1353__GateII_HBoxData_0 : HBox :=
  { p := 10093, k := 921961, v := 834751, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1354__GateII_HBoxData_0 : HBox :=
  { p := 10099, k := 922021, v := 833868, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1355__GateII_HBoxData_0 : HBox :=
  { p := 10103, k := 922060, v := 833278, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1356__GateII_HBoxData_0 : HBox :=
  { p := 10111, k := 922139, v := 832102, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1357__GateII_HBoxData_0 : HBox :=
  { p := 10133, k := 922357, v := 828884, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1358__GateII_HBoxData_0 : HBox :=
  { p := 10139, k := 922416, v := 828009, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1359__GateII_HBoxData_0 : HBox :=
  { p := 10141, k := 922436, v := 827718, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1360__GateII_HBoxData_0 : HBox :=
  { p := 10151, k := 922534, v := 826263, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1361__GateII_HBoxData_0 : HBox :=
  { p := 10159, k := 922613, v := 825104, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1362__GateII_HBoxData_0 : HBox :=
  { p := 10163, k := 922652, v := 824524, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1363__GateII_HBoxData_0 : HBox :=
  { p := 10169, k := 922711, v := 823656, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1364__GateII_HBoxData_0 : HBox :=
  { p := 10177, k := 922790, v := 822502, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1365__GateII_HBoxData_0 : HBox :=
  { p := 10181, k := 922829, v := 821926, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1366__GateII_HBoxData_0 : HBox :=
  { p := 10193, k := 922947, v := 820201, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1367__GateII_HBoxData_0 : HBox :=
  { p := 10211, k := 923124, v := 817625, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1368__GateII_HBoxData_0 : HBox :=
  { p := 10223, k := 923241, v := 815913, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1369__GateII_HBoxData_0 : HBox :=
  { p := 10243, k := 923436, v := 813072, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1370__GateII_HBoxData_0 : HBox :=
  { p := 10247, k := 923476, v := 812508, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1371__GateII_HBoxData_0 : HBox :=
  { p := 10253, k := 923534, v := 811659, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1372__GateII_HBoxData_0 : HBox :=
  { p := 10259, k := 923593, v := 810813, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1373__GateII_HBoxData_0 : HBox :=
  { p := 10267, k := 923671, v := 809687, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1374__GateII_HBoxData_0 : HBox :=
  { p := 10271, k := 923709, v := 809123, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1375__GateII_HBoxData_0 : HBox :=
  { p := 10273, k := 923729, v := 808842, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1376__GateII_HBoxData_0 : HBox :=
  { p := 10289, k := 923885, v := 806601, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1377__GateII_HBoxData_0 : HBox :=
  { p := 10301, k := 924001, v := 804924, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1378__GateII_HBoxData_0 : HBox :=
  { p := 10303, k := 924021, v := 804647, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1379__GateII_HBoxData_0 : HBox :=
  { p := 10313, k := 924118, v := 803255, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1380__GateII_HBoxData_0 : HBox :=
  { p := 10321, k := 924195, v := 802144, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1381__GateII_HBoxData_0 : HBox :=
  { p := 10331, k := 924292, v := 800759, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1382__GateII_HBoxData_0 : HBox :=
  { p := 10333, k := 924311, v := 800482, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1383__GateII_HBoxData_0 : HBox :=
  { p := 10337, k := 924350, v := 799930, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1384__GateII_HBoxData_0 : HBox :=
  { p := 10343, k := 924408, v := 799103, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1385__GateII_HBoxData_0 : HBox :=
  { p := 10357, k := 924543, v := 797176, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1386__GateII_HBoxData_0 : HBox :=
  { p := 10369, k := 924659, v := 795531, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1387__GateII_HBoxData_0 : HBox :=
  { p := 10391, k := 924871, v := 792529, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1388__GateII_HBoxData_0 : HBox :=
  { p := 10399, k := 924948, v := 791441, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1389__GateII_HBoxData_0 : HBox :=
  { p := 10427, k := 925217, v := 787654, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1390__GateII_HBoxData_0 : HBox :=
  { p := 10429, k := 925236, v := 787384, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1391__GateII_HBoxData_0 : HBox :=
  { p := 10433, k := 925274, v := 786845, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1392__GateII_HBoxData_0 : HBox :=
  { p := 10453, k := 925466, v := 784161, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1393__GateII_HBoxData_0 : HBox :=
  { p := 10457, k := 925504, v := 783626, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1394__GateII_HBoxData_0 : HBox :=
  { p := 10459, k := 925523, v := 783358, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1395__GateII_HBoxData_0 : HBox :=
  { p := 10463, k := 925562, v := 782825, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1396__GateII_HBoxData_0 : HBox :=
  { p := 10477, k := 925695, v := 780959, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1397__GateII_HBoxData_0 : HBox :=
  { p := 10487, k := 925791, v := 779631, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1398__GateII_HBoxData_0 : HBox :=
  { p := 10499, k := 925905, v := 778041, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1399__GateII_HBoxData_0 : HBox :=
  { p := 10501, k := 925924, v := 777777, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1400__GateII_HBoxData_0 : HBox :=
  { p := 10513, k := 926038, v := 776193, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1401__GateII_HBoxData_0 : HBox :=
  { p := 10529, k := 926190, v := 774090, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1402__GateII_HBoxData_0 : HBox :=
  { p := 10531, k := 926209, v := 773827, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1403__GateII_HBoxData_0 : HBox :=
  { p := 10559, k := 926475, v := 770170, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1404__GateII_HBoxData_0 : HBox :=
  { p := 10567, k := 926551, v := 769130, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1405__GateII_HBoxData_0 : HBox :=
  { p := 10589, k := 926759, v := 766281, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1406__GateII_HBoxData_0 : HBox :=
  { p := 10597, k := 926834, v := 765248, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1407__GateII_HBoxData_0 : HBox :=
  { p := 10601, k := 926872, v := 764733, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1408__GateII_HBoxData_0 : HBox :=
  { p := 10607, k := 926928, v := 763961, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1409__GateII_HBoxData_0 : HBox :=
  { p := 10613, k := 926985, v := 763191, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1410__GateII_HBoxData_0 : HBox :=
  { p := 10627, k := 927117, v := 761398, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1411__GateII_HBoxData_0 : HBox :=
  { p := 10631, k := 927154, v := 760885, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1412__GateII_HBoxData_0 : HBox :=
  { p := 10639, k := 927230, v := 759866, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1413__GateII_HBoxData_0 : HBox :=
  { p := 10651, k := 927342, v := 758337, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1414__GateII_HBoxData_0 : HBox :=
  { p := 10657, k := 927399, v := 757577, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1415__GateII_HBoxData_0 : HBox :=
  { p := 10663, k := 927455, v := 756816, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1416__GateII_HBoxData_0 : HBox :=
  { p := 10667, k := 927493, v := 756310, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1417__GateII_HBoxData_0 : HBox :=
  { p := 10687, k := 927680, v := 753785, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1418__GateII_HBoxData_0 : HBox :=
  { p := 10691, k := 927717, v := 753281, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1419__GateII_HBoxData_0 : HBox :=
  { p := 10709, k := 927885, v := 751023, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1420__GateII_HBoxData_0 : HBox :=
  { p := 10711, k := 927904, v := 750773, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1421__GateII_HBoxData_0 : HBox :=
  { p := 10723, k := 928016, v := 749274, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1422__GateII_HBoxData_0 : HBox :=
  { p := 10729, k := 928072, v := 748526, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1423__GateII_HBoxData_0 : HBox :=
  { p := 10733, k := 928109, v := 748028, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1424__GateII_HBoxData_0 : HBox :=
  { p := 10739, k := 928165, v := 747282, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1425__GateII_HBoxData_0 : HBox :=
  { p := 10753, k := 928296, v := 745548, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1426__GateII_HBoxData_0 : HBox :=
  { p := 10771, k := 928463, v := 743325, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1427__GateII_HBoxData_0 : HBox :=
  { p := 10781, k := 928556, v := 742095, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1428__GateII_HBoxData_0 : HBox :=
  { p := 10789, k := 928630, v := 741113, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1429__GateII_HBoxData_0 : HBox :=
  { p := 10799, k := 928722, v := 739887, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1430__GateII_HBoxData_0 : HBox :=
  { p := 10831, k := 929018, v := 735990, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1431__GateII_HBoxData_0 : HBox :=
  { p := 10837, k := 929074, v := 735264, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1432__GateII_HBoxData_0 : HBox :=
  { p := 10847, k := 929166, v := 734054, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1433__GateII_HBoxData_0 : HBox :=
  { p := 10853, k := 929221, v := 733329, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1434__GateII_HBoxData_0 : HBox :=
  { p := 10859, k := 929276, v := 732605, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1435__GateII_HBoxData_0 : HBox :=
  { p := 10861, k := 929295, v := 732365, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1436__GateII_HBoxData_0 : HBox :=
  { p := 10867, k := 929350, v := 731643, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1437__GateII_HBoxData_0 : HBox :=
  { p := 10883, k := 929497, v := 729724, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1438__GateII_HBoxData_0 : HBox :=
  { p := 10889, k := 929552, v := 729006, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1439__GateII_HBoxData_0 : HBox :=
  { p := 10891, k := 929571, v := 728768, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1440__GateII_HBoxData_0 : HBox :=
  { p := 10903, k := 929681, v := 727337, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1441__GateII_HBoxData_0 : HBox :=
  { p := 10909, k := 929736, v := 726623, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1442__GateII_HBoxData_0 : HBox :=
  { p := 10937, k := 929992, v := 723304, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1443__GateII_HBoxData_0 : HBox :=
  { p := 10939, k := 930010, v := 723068, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1444__GateII_HBoxData_0 : HBox :=
  { p := 10949, k := 930102, v := 721890, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1445__GateII_HBoxData_0 : HBox :=
  { p := 10957, k := 930175, v := 720950, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1446__GateII_HBoxData_0 : HBox :=
  { p := 10973, k := 930321, v := 719074, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1447__GateII_HBoxData_0 : HBox :=
  { p := 10979, k := 930375, v := 718371, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1448__GateII_HBoxData_0 : HBox :=
  { p := 10987, k := 930448, v := 717438, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1449__GateII_HBoxData_0 : HBox :=
  { p := 10993, k := 930503, v := 716740, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1450__GateII_HBoxData_0 : HBox :=
  { p := 11003, k := 930594, v := 715577, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1451__GateII_HBoxData_0 : HBox :=
  { p := 11027, k := 930812, v := 712799, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1452__GateII_HBoxData_0 : HBox :=
  { p := 11047, k := 930993, v := 710496, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1453__GateII_HBoxData_0 : HBox :=
  { p := 11057, k := 931083, v := 709348, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1454__GateII_HBoxData_0 : HBox :=
  { p := 11059, k := 931101, v := 709119, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1455__GateII_HBoxData_0 : HBox :=
  { p := 11069, k := 931192, v := 707977, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1456__GateII_HBoxData_0 : HBox :=
  { p := 11071, k := 931210, v := 707748, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1457__GateII_HBoxData_0 : HBox :=
  { p := 11083, k := 931318, v := 706380, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1458__GateII_HBoxData_0 : HBox :=
  { p := 11087, k := 931354, v := 705925, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1459__GateII_HBoxData_0 : HBox :=
  { p := 11093, k := 931408, v := 705243, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1460__GateII_HBoxData_0 : HBox :=
  { p := 11113, k := 931589, v := 702980, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1461__GateII_HBoxData_0 : HBox :=
  { p := 11117, k := 931625, v := 702528, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1462__GateII_HBoxData_0 : HBox :=
  { p := 11119, k := 931643, v := 702302, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1463__GateII_HBoxData_0 : HBox :=
  { p := 11131, k := 931750, v := 700950, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1464__GateII_HBoxData_0 : HBox :=
  { p := 11149, k := 931912, v := 698931, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1465__GateII_HBoxData_0 : HBox :=
  { p := 11159, k := 932002, v := 697813, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1466__GateII_HBoxData_0 : HBox :=
  { p := 11161, k := 932020, v := 697590, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1467__GateII_HBoxData_0 : HBox :=
  { p := 11171, k := 932109, v := 696474, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1468__GateII_HBoxData_0 : HBox :=
  { p := 11173, k := 932127, v := 696252, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1469__GateII_HBoxData_0 : HBox :=
  { p := 11177, k := 932163, v := 695807, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1470__GateII_HBoxData_0 : HBox :=
  { p := 11197, k := 932342, v := 693590, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1471__GateII_HBoxData_0 : HBox :=
  { p := 11213, k := 932484, v := 691822, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1472__GateII_HBoxData_0 : HBox :=
  { p := 11239, k := 932716, v := 688967, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1473__GateII_HBoxData_0 : HBox :=
  { p := 11243, k := 932752, v := 688530, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1474__GateII_HBoxData_0 : HBox :=
  { p := 11251, k := 932823, v := 687656, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1475__GateII_HBoxData_0 : HBox :=
  { p := 11257, k := 932876, v := 687001, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1476__GateII_HBoxData_0 : HBox :=
  { p := 11261, k := 932912, v := 686566, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1477__GateII_HBoxData_0 : HBox :=
  { p := 11273, k := 933018, v := 685260, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1478__GateII_HBoxData_0 : HBox :=
  { p := 11279, k := 933071, v := 684609, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1479__GateII_HBoxData_0 : HBox :=
  { p := 11287, k := 933142, v := 683743, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1480__GateII_HBoxData_0 : HBox :=
  { p := 11299, k := 933248, v := 682446, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1481__GateII_HBoxData_0 : HBox :=
  { p := 11311, k := 933355, v := 681154, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1482__GateII_HBoxData_0 : HBox :=
  { p := 11317, k := 933408, v := 680510, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1483__GateII_HBoxData_0 : HBox :=
  { p := 11321, k := 933443, v := 680080, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1484__GateII_HBoxData_0 : HBox :=
  { p := 11329, k := 933514, v := 679223, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1485__GateII_HBoxData_0 : HBox :=
  { p := 11351, k := 933708, v := 676873, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1486__GateII_HBoxData_0 : HBox :=
  { p := 11353, k := 933725, v := 676659, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1487__GateII_HBoxData_0 : HBox :=
  { p := 11369, k := 933866, v := 674960, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1488__GateII_HBoxData_0 : HBox :=
  { p := 11383, k := 933989, v := 673477, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1489__GateII_HBoxData_0 : HBox :=
  { p := 11393, k := 934077, v := 672422, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1490__GateII_HBoxData_0 : HBox :=
  { p := 11399, k := 934130, v := 671790, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1491__GateII_HBoxData_0 : HBox :=
  { p := 11411, k := 934235, v := 670529, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1492__GateII_HBoxData_0 : HBox :=
  { p := 11423, k := 934340, v := 669271, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1493__GateII_HBoxData_0 : HBox :=
  { p := 11437, k := 934462, v := 667807, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1494__GateII_HBoxData_0 : HBox :=
  { p := 11443, k := 934515, v := 667183, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1495__GateII_HBoxData_0 : HBox :=
  { p := 11447, k := 934550, v := 666767, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1496__GateII_HBoxData_0 : HBox :=
  { p := 11467, k := 934724, v := 664690, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1497__GateII_HBoxData_0 : HBox :=
  { p := 11471, k := 934759, v := 664276, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1498__GateII_HBoxData_0 : HBox :=
  { p := 11483, k := 934864, v := 663037, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1499__GateII_HBoxData_0 : HBox :=
  { p := 11489, k := 934916, v := 662418, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1500__GateII_HBoxData_0 : HBox :=
  { p := 11491, k := 934933, v := 662212, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1501__GateII_HBoxData_0 : HBox :=
  { p := 11497, k := 934986, v := 661596, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1502__GateII_HBoxData_0 : HBox :=
  { p := 11503, k := 935038, v := 660979, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1503__GateII_HBoxData_0 : HBox :=
  { p := 11519, k := 935177, v := 659340, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1504__GateII_HBoxData_0 : HBox :=
  { p := 11527, k := 935246, v := 658522, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1505__GateII_HBoxData_0 : HBox :=
  { p := 11549, k := 935437, v := 656283, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1506__GateII_HBoxData_0 : HBox :=
  { p := 11551, k := 935454, v := 656079, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1507__GateII_HBoxData_0 : HBox :=
  { p := 11579, k := 935696, v := 653248, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1508__GateII_HBoxData_0 : HBox :=
  { p := 11587, k := 935765, v := 652442, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1509__GateII_HBoxData_0 : HBox :=
  { p := 11593, k := 935817, v := 651839, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1510__GateII_HBoxData_0 : HBox :=
  { p := 11597, k := 935852, v := 651438, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1511__GateII_HBoxData_0 : HBox :=
  { p := 11617, k := 936024, v := 649435, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1512__GateII_HBoxData_0 : HBox :=
  { p := 11621, k := 936058, v := 649035, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1513__GateII_HBoxData_0 : HBox :=
  { p := 11633, k := 936162, v := 647841, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1514__GateII_HBoxData_0 : HBox :=
  { p := 11657, k := 936368, v := 645459, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1515__GateII_HBoxData_0 : HBox :=
  { p := 11677, k := 936539, v := 643485, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1516__GateII_HBoxData_0 : HBox :=
  { p := 11681, k := 936573, v := 643091, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1517__GateII_HBoxData_0 : HBox :=
  { p := 11689, k := 936642, v := 642305, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1518__GateII_HBoxData_0 : HBox :=
  { p := 11699, k := 936727, v := 641324, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1519__GateII_HBoxData_0 : HBox :=
  { p := 11701, k := 936744, v := 641128, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1520__GateII_HBoxData_0 : HBox :=
  { p := 11717, k := 936881, v := 639565, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1521__GateII_HBoxData_0 : HBox :=
  { p := 11719, k := 936898, v := 639370, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1522__GateII_HBoxData_0 : HBox :=
  { p := 11731, k := 937001, v := 638202, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1523__GateII_HBoxData_0 : HBox :=
  { p := 11743, k := 937103, v := 637037, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1524__GateII_HBoxData_0 : HBox :=
  { p := 11777, k := 937392, v := 633754, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1525__GateII_HBoxData_0 : HBox :=
  { p := 11779, k := 937409, v := 633562, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1526__GateII_HBoxData_0 : HBox :=
  { p := 11783, k := 937443, v := 633178, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1527__GateII_HBoxData_0 : HBox :=
  { p := 11789, k := 937494, v := 632602, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1528__GateII_HBoxData_0 : HBox :=
  { p := 11801, k := 937595, v := 631452, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1529__GateII_HBoxData_0 : HBox :=
  { p := 11807, k := 937646, v := 630879, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1530__GateII_HBoxData_0 : HBox :=
  { p := 11813, k := 937697, v := 630307, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1531__GateII_HBoxData_0 : HBox :=
  { p := 11821, k := 937765, v := 629545, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1532__GateII_HBoxData_0 : HBox :=
  { p := 11827, k := 937816, v := 628975, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1533__GateII_HBoxData_0 : HBox :=
  { p := 11831, k := 937849, v := 628594, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1534__GateII_HBoxData_0 : HBox :=
  { p := 11833, k := 937866, v := 628404, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1535__GateII_HBoxData_0 : HBox :=
  { p := 11839, k := 937917, v := 627835, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1536__GateII_HBoxData_0 : HBox :=
  { p := 11863, k := 938119, v := 625567, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1537__GateII_HBoxData_0 : HBox :=
  { p := 11867, k := 938153, v := 625190, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1538__GateII_HBoxData_0 : HBox :=
  { p := 11887, k := 938322, v := 623312, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1539__GateII_HBoxData_0 : HBox :=
  { p := 11897, k := 938406, v := 622376, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1540__GateII_HBoxData_0 : HBox :=
  { p := 11903, k := 938456, v := 621815, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1541__GateII_HBoxData_0 : HBox :=
  { p := 11909, k := 938506, v := 621255, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1542__GateII_HBoxData_0 : HBox :=
  { p := 11923, k := 938624, v := 619952, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1543__GateII_HBoxData_0 : HBox :=
  { p := 11927, k := 938658, v := 619581, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1544__GateII_HBoxData_0 : HBox :=
  { p := 11933, k := 938708, v := 619024, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1545__GateII_HBoxData_0 : HBox :=
  { p := 11939, k := 938758, v := 618468, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1546__GateII_HBoxData_0 : HBox :=
  { p := 11941, k := 938775, v := 618283, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1547__GateII_HBoxData_0 : HBox :=
  { p := 11953, k := 938875, v := 617174, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1548__GateII_HBoxData_0 : HBox :=
  { p := 11959, k := 938925, v := 616620, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1549__GateII_HBoxData_0 : HBox :=
  { p := 11969, k := 939009, v := 615700, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1550__GateII_HBoxData_0 : HBox :=
  { p := 11971, k := 939026, v := 615517, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1551__GateII_HBoxData_0 : HBox :=
  { p := 11981, k := 939109, v := 614598, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1552__GateII_HBoxData_0 : HBox :=
  { p := 11987, k := 939159, v := 614048, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1553__GateII_HBoxData_0 : HBox :=
  { p := 12007, k := 939326, v := 612222, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1554__GateII_HBoxData_0 : HBox :=
  { p := 12011, k := 939359, v := 611857, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1555__GateII_HBoxData_0 : HBox :=
  { p := 12037, k := 939576, v := 609498, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1556__GateII_HBoxData_0 : HBox :=
  { p := 12041, k := 939609, v := 609135, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1557__GateII_HBoxData_0 : HBox :=
  { p := 12043, k := 939625, v := 608954, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1558__GateII_HBoxData_0 : HBox :=
  { p := 12049, k := 939675, v := 608412, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1559__GateII_HBoxData_0 : HBox :=
  { p := 12071, k := 939858, v := 606432, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1560__GateII_HBoxData_0 : HBox :=
  { p := 12073, k := 939874, v := 606252, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1561__GateII_HBoxData_0 : HBox :=
  { p := 12097, k := 940073, v := 604104, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1562__GateII_HBoxData_0 : HBox :=
  { p := 12101, k := 940106, v := 603747, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1563__GateII_HBoxData_0 : HBox :=
  { p := 12107, k := 940155, v := 603212, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1564__GateII_HBoxData_0 : HBox :=
  { p := 12109, k := 940172, v := 603034, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1565__GateII_HBoxData_0 : HBox :=
  { p := 12113, k := 940205, v := 602678, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1566__GateII_HBoxData_0 : HBox :=
  { p := 12119, k := 940254, v := 602144, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1567__GateII_HBoxData_0 : HBox :=
  { p := 12143, k := 940452, v := 600019, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1568__GateII_HBoxData_0 : HBox :=
  { p := 12149, k := 940502, v := 599490, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1569__GateII_HBoxData_0 : HBox :=
  { p := 12157, k := 940568, v := 598785, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1570__GateII_HBoxData_0 : HBox :=
  { p := 12161, k := 940600, v := 598432, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1571__GateII_HBoxData_0 : HBox :=
  { p := 12163, k := 940617, v := 598256, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1572__GateII_HBoxData_0 : HBox :=
  { p := 12197, k := 940896, v := 595278, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1573__GateII_HBoxData_0 : HBox :=
  { p := 12203, k := 940945, v := 594755, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1574__GateII_HBoxData_0 : HBox :=
  { p := 12211, k := 941011, v := 594059, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1575__GateII_HBoxData_0 : HBox :=
  { p := 12227, k := 941142, v := 592670, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1576__GateII_HBoxData_0 : HBox :=
  { p := 12239, k := 941240, v := 591631, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1577__GateII_HBoxData_0 : HBox :=
  { p := 12241, k := 941256, v := 591458, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1578__GateII_HBoxData_0 : HBox :=
  { p := 12251, k := 941338, v := 590596, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1579__GateII_HBoxData_0 : HBox :=
  { p := 12253, k := 941354, v := 590423, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1580__GateII_HBoxData_0 : HBox :=
  { p := 12263, k := 941436, v := 589563, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1581__GateII_HBoxData_0 : HBox :=
  { p := 12269, k := 941485, v := 589048, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1582__GateII_HBoxData_0 : HBox :=
  { p := 12277, k := 941550, v := 588361, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1583__GateII_HBoxData_0 : HBox :=
  { p := 12281, k := 941582, v := 588018, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1584__GateII_HBoxData_0 : HBox :=
  { p := 12289, k := 941647, v := 587334, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1585__GateII_HBoxData_0 : HBox :=
  { p := 12301, k := 941745, v := 586310, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1586__GateII_HBoxData_0 : HBox :=
  { p := 12323, k := 941924, v := 584440, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1587__GateII_HBoxData_0 : HBox :=
  { p := 12329, k := 941972, v := 583931, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1588__GateII_HBoxData_0 : HBox :=
  { p := 12343, k := 942086, v := 582748, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1589__GateII_HBoxData_0 : HBox :=
  { p := 12347, k := 942118, v := 582410, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1590__GateII_HBoxData_0 : HBox :=
  { p := 12373, k := 942329, v := 580224, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1591__GateII_HBoxData_0 : HBox :=
  { p := 12377, k := 942361, v := 579889, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1592__GateII_HBoxData_0 : HBox :=
  { p := 12379, k := 942377, v := 579721, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1593__GateII_HBoxData_0 : HBox :=
  { p := 12391, k := 942474, v := 578718, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1594__GateII_HBoxData_0 : HBox :=
  { p := 12401, k := 942555, v := 577884, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1595__GateII_HBoxData_0 : HBox :=
  { p := 12409, k := 942619, v := 577217, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1596__GateII_HBoxData_0 : HBox :=
  { p := 12413, k := 942651, v := 576884, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1597__GateII_HBoxData_0 : HBox :=
  { p := 12421, k := 942716, v := 576221, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1598__GateII_HBoxData_0 : HBox :=
  { p := 12433, k := 942812, v := 575226, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1599__GateII_HBoxData_0 : HBox :=
  { p := 12437, k := 942845, v := 574896, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1600__GateII_HBoxData_0 : HBox :=
  { p := 12451, k := 942957, v := 573740, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1601__GateII_HBoxData_0 : HBox :=
  { p := 12457, k := 943005, v := 573246, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1602__GateII_HBoxData_0 : HBox :=
  { p := 12473, k := 943134, v := 571932, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1603__GateII_HBoxData_0 : HBox :=
  { p := 12479, k := 943182, v := 571441, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1604__GateII_HBoxData_0 : HBox :=
  { p := 12487, k := 943246, v := 570786, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1605__GateII_HBoxData_0 : HBox :=
  { p := 12491, k := 943278, v := 570459, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1606__GateII_HBoxData_0 : HBox :=
  { p := 12497, k := 943326, v := 569969, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1607__GateII_HBoxData_0 : HBox :=
  { p := 12503, k := 943374, v := 569480, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1608__GateII_HBoxData_0 : HBox :=
  { p := 12511, k := 943438, v := 568829, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1609__GateII_HBoxData_0 : HBox :=
  { p := 12517, k := 943486, v := 568342, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1610__GateII_HBoxData_0 : HBox :=
  { p := 12527, k := 943566, v := 567531, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1611__GateII_HBoxData_0 : HBox :=
  { p := 12539, k := 943661, v := 566559, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1612__GateII_HBoxData_0 : HBox :=
  { p := 12541, k := 943677, v := 566397, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1613__GateII_HBoxData_0 : HBox :=
  { p := 12547, k := 943725, v := 565913, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1614__GateII_HBoxData_0 : HBox :=
  { p := 12553, k := 943773, v := 565430, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1615__GateII_HBoxData_0 : HBox :=
  { p := 12569, k := 943900, v := 564143, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1616__GateII_HBoxData_0 : HBox :=
  { p := 12577, k := 943964, v := 563502, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1617__GateII_HBoxData_0 : HBox :=
  { p := 12583, k := 944012, v := 563022, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1618__GateII_HBoxData_0 : HBox :=
  { p := 12589, k := 944059, v := 562541, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1619__GateII_HBoxData_0 : HBox :=
  { p := 12601, k := 944155, v := 561584, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1620__GateII_HBoxData_0 : HBox :=
  { p := 12611, k := 944234, v := 560788, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1621__GateII_HBoxData_0 : HBox :=
  { p := 12613, k := 944250, v := 560629, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1622__GateII_HBoxData_0 : HBox :=
  { p := 12619, k := 944297, v := 560151, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1623__GateII_HBoxData_0 : HBox :=
  { p := 12637, k := 944440, v := 558726, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1624__GateII_HBoxData_0 : HBox :=
  { p := 12641, k := 944472, v := 558410, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1625__GateII_HBoxData_0 : HBox :=
  { p := 12647, k := 944519, v := 557936, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1626__GateII_HBoxData_0 : HBox :=
  { p := 12653, k := 944566, v := 557462, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1627__GateII_HBoxData_0 : HBox :=
  { p := 12659, k := 944614, v := 556990, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1628__GateII_HBoxData_0 : HBox :=
  { p := 12671, k := 944709, v := 556047, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1629__GateII_HBoxData_0 : HBox :=
  { p := 12689, k := 944851, v := 554637, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1630__GateII_HBoxData_0 : HBox :=
  { p := 12697, k := 944914, v := 554012, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1631__GateII_HBoxData_0 : HBox :=
  { p := 12703, k := 944961, v := 553544, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1632__GateII_HBoxData_0 : HBox :=
  { p := 12713, k := 945040, v := 552766, N := 27, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1633__GateII_HBoxData_0 : HBox :=
  { p := 12721, k := 945102, v := 552143, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1634__GateII_HBoxData_0 : HBox :=
  { p := 12739, k := 945244, v := 550749, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1635__GateII_HBoxData_0 : HBox :=
  { p := 12743, k := 945275, v := 550440, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1636__GateII_HBoxData_0 : HBox :=
  { p := 12757, k := 945385, v := 549360, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1637__GateII_HBoxData_0 : HBox :=
  { p := 12763, k := 945432, v := 548898, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1638__GateII_HBoxData_0 : HBox :=
  { p := 12781, k := 945573, v := 547516, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1639__GateII_HBoxData_0 : HBox :=
  { p := 12791, k := 945651, v := 546750, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1640__GateII_HBoxData_0 : HBox :=
  { p := 12799, k := 945714, v := 546140, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1641__GateII_HBoxData_0 : HBox :=
  { p := 12809, k := 945792, v := 545377, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1642__GateII_HBoxData_0 : HBox :=
  { p := 12821, k := 945885, v := 544464, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1643__GateII_HBoxData_0 : HBox :=
  { p := 12823, k := 945901, v := 544312, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1644__GateII_HBoxData_0 : HBox :=
  { p := 12829, k := 945948, v := 543857, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1645__GateII_HBoxData_0 : HBox :=
  { p := 12841, k := 946041, v := 542948, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1646__GateII_HBoxData_0 : HBox :=
  { p := 12853, k := 946135, v := 542042, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1647__GateII_HBoxData_0 : HBox :=
  { p := 12889, k := 946414, v := 539336, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1648__GateII_HBoxData_0 : HBox :=
  { p := 12893, k := 946445, v := 539036, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1649__GateII_HBoxData_0 : HBox :=
  { p := 12899, k := 946492, v := 538588, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1650__GateII_HBoxData_0 : HBox :=
  { p := 12907, k := 946554, v := 537991, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1651__GateII_HBoxData_0 : HBox :=
  { p := 12911, k := 946585, v := 537693, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1652__GateII_HBoxData_0 : HBox :=
  { p := 12917, k := 946631, v := 537246, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1653__GateII_HBoxData_0 : HBox :=
  { p := 12919, k := 946647, v := 537098, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1654__GateII_HBoxData_0 : HBox :=
  { p := 12923, k := 946678, v := 536800, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1655__GateII_HBoxData_0 : HBox :=
  { p := 12941, k := 946817, v := 535465, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1656__GateII_HBoxData_0 : HBox :=
  { p := 12953, k := 946910, v := 534578, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1657__GateII_HBoxData_0 : HBox :=
  { p := 12959, k := 946956, v := 534135, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1658__GateII_HBoxData_0 : HBox :=
  { p := 12967, k := 947018, v := 533546, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1659__GateII_HBoxData_0 : HBox :=
  { p := 12973, k := 947064, v := 533104, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1660__GateII_HBoxData_0 : HBox :=
  { p := 12979, k := 947110, v := 532663, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1661__GateII_HBoxData_0 : HBox :=
  { p := 12983, k := 947141, v := 532370, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1662__GateII_HBoxData_0 : HBox :=
  { p := 13001, k := 947280, v := 531052, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1663__GateII_HBoxData_0 : HBox :=
  { p := 13003, k := 947295, v := 530906, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1664__GateII_HBoxData_0 : HBox :=
  { p := 13007, k := 947326, v := 530614, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1665__GateII_HBoxData_0 : HBox :=
  { p := 13009, k := 947341, v := 530468, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1666__GateII_HBoxData_0 : HBox :=
  { p := 13033, k := 947525, v := 528721, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1667__GateII_HBoxData_0 : HBox :=
  { p := 13037, k := 947556, v := 528431, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1668__GateII_HBoxData_0 : HBox :=
  { p := 13043, k := 947602, v := 527996, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1669__GateII_HBoxData_0 : HBox :=
  { p := 13049, k := 947648, v := 527562, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1670__GateII_HBoxData_0 : HBox :=
  { p := 13063, k := 947755, v := 526550, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1671__GateII_HBoxData_0 : HBox :=
  { p := 13093, k := 947985, v := 524394, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1672__GateII_HBoxData_0 : HBox :=
  { p := 13099, k := 948031, v := 523964, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1673__GateII_HBoxData_0 : HBox :=
  { p := 13103, k := 948061, v := 523678, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1674__GateII_HBoxData_0 : HBox :=
  { p := 13109, k := 948107, v := 523249, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1675__GateII_HBoxData_0 : HBox :=
  { p := 13121, k := 948198, v := 522393, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1676__GateII_HBoxData_0 : HBox :=
  { p := 13127, k := 948244, v := 521966, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1677__GateII_HBoxData_0 : HBox :=
  { p := 13147, k := 948396, v := 520545, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1678__GateII_HBoxData_0 : HBox :=
  { p := 13151, k := 948427, v := 520263, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1679__GateII_HBoxData_0 : HBox :=
  { p := 13159, k := 948488, v := 519697, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1680__GateII_HBoxData_0 : HBox :=
  { p := 13163, k := 948518, v := 519414, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1681__GateII_HBoxData_0 : HBox :=
  { p := 13171, k := 948579, v := 518850, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1682__GateII_HBoxData_0 : HBox :=
  { p := 13177, k := 948624, v := 518427, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1683__GateII_HBoxData_0 : HBox :=
  { p := 13183, k := 948670, v := 518005, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1684__GateII_HBoxData_0 : HBox :=
  { p := 13187, k := 948700, v := 517724, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1685__GateII_HBoxData_0 : HBox :=
  { p := 13217, k := 948927, v := 515622, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1686__GateII_HBoxData_0 : HBox :=
  { p := 13219, k := 948943, v := 515484, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1687__GateII_HBoxData_0 : HBox :=
  { p := 13229, k := 949018, v := 514786, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1688__GateII_HBoxData_0 : HBox :=
  { p := 13241, k := 949109, v := 513952, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1689__GateII_HBoxData_0 : HBox :=
  { p := 13249, k := 949169, v := 513396, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1690__GateII_HBoxData_0 : HBox :=
  { p := 13259, k := 949245, v := 512704, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1691__GateII_HBoxData_0 : HBox :=
  { p := 13267, k := 949305, v := 512150, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1692__GateII_HBoxData_0 : HBox :=
  { p := 13291, k := 949486, v := 510497, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1693__GateII_HBoxData_0 : HBox :=
  { p := 13297, k := 949531, v := 510084, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1694__GateII_HBoxData_0 : HBox :=
  { p := 13309, k := 949621, v := 509261, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1695__GateII_HBoxData_0 : HBox :=
  { p := 13313, k := 949651, v := 508987, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1696__GateII_HBoxData_0 : HBox :=
  { p := 13327, k := 949756, v := 508031, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1697__GateII_HBoxData_0 : HBox :=
  { p := 13331, k := 949786, v := 507758, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1698__GateII_HBoxData_0 : HBox :=
  { p := 13337, k := 949831, v := 507349, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1699__GateII_HBoxData_0 : HBox :=
  { p := 13339, k := 949846, v := 507213, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1700__GateII_HBoxData_0 : HBox :=
  { p := 13367, k := 950056, v := 505314, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1701__GateII_HBoxData_0 : HBox :=
  { p := 13381, k := 950161, v := 504368, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1702__GateII_HBoxData_0 : HBox :=
  { p := 13397, k := 950280, v := 503290, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1703__GateII_HBoxData_0 : HBox :=
  { p := 13399, k := 950295, v := 503155, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1704__GateII_HBoxData_0 : HBox :=
  { p := 13411, k := 950385, v := 502350, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1705__GateII_HBoxData_0 : HBox :=
  { p := 13417, k := 950429, v := 501948, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1706__GateII_HBoxData_0 : HBox :=
  { p := 13421, k := 950459, v := 501680, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1707__GateII_HBoxData_0 : HBox :=
  { p := 13441, k := 950608, v := 500345, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1708__GateII_HBoxData_0 : HBox :=
  { p := 13451, k := 950682, v := 499679, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1709__GateII_HBoxData_0 : HBox :=
  { p := 13457, k := 950727, v := 499281, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1710__GateII_HBoxData_0 : HBox :=
  { p := 13463, k := 950772, v := 498883, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1711__GateII_HBoxData_0 : HBox :=
  { p := 13469, k := 950816, v := 498485, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1712__GateII_HBoxData_0 : HBox :=
  { p := 13477, k := 950875, v := 497955, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1713__GateII_HBoxData_0 : HBox :=
  { p := 13487, k := 950950, v := 497295, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1714__GateII_HBoxData_0 : HBox :=
  { p := 13499, k := 951039, v := 496504, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1715__GateII_HBoxData_0 : HBox :=
  { p := 13513, k := 951142, v := 495583, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1716__GateII_HBoxData_0 : HBox :=
  { p := 13523, k := 951216, v := 494927, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1717__GateII_HBoxData_0 : HBox :=
  { p := 13537, k := 951320, v := 494012, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1718__GateII_HBoxData_0 : HBox :=
  { p := 13553, k := 951438, v := 492968, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1719__GateII_HBoxData_0 : HBox :=
  { p := 13567, k := 951541, v := 492057, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1720__GateII_HBoxData_0 : HBox :=
  { p := 13577, k := 951615, v := 491409, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1721__GateII_HBoxData_0 : HBox :=
  { p := 13591, k := 951718, v := 490503, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1722__GateII_HBoxData_0 : HBox :=
  { p := 13597, k := 951762, v := 490116, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1723__GateII_HBoxData_0 : HBox :=
  { p := 13613, k := 951880, v := 489085, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1724__GateII_HBoxData_0 : HBox :=
  { p := 13619, k := 951924, v := 488700, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1725__GateII_HBoxData_0 : HBox :=
  { p := 13627, k := 951982, v := 488186, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1726__GateII_HBoxData_0 : HBox :=
  { p := 13633, k := 952026, v := 487801, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1727__GateII_HBoxData_0 : HBox :=
  { p := 13649, k := 952144, v := 486778, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1728__GateII_HBoxData_0 : HBox :=
  { p := 13669, k := 952290, v := 485504, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1729__GateII_HBoxData_0 : HBox :=
  { p := 13679, k := 952363, v := 484868, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1730__GateII_HBoxData_0 : HBox :=
  { p := 13681, k := 952378, v := 484742, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1731__GateII_HBoxData_0 : HBox :=
  { p := 13687, k := 952422, v := 484362, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1732__GateII_HBoxData_0 : HBox :=
  { p := 13691, k := 952451, v := 484108, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1733__GateII_HBoxData_0 : HBox :=
  { p := 13693, k := 952466, v := 483982, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1734__GateII_HBoxData_0 : HBox :=
  { p := 13697, k := 952495, v := 483729, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1735__GateII_HBoxData_0 : HBox :=
  { p := 13709, k := 952582, v := 482970, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1736__GateII_HBoxData_0 : HBox :=
  { p := 13711, k := 952597, v := 482845, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1737__GateII_HBoxData_0 : HBox :=
  { p := 13721, k := 952670, v := 482215, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1738__GateII_HBoxData_0 : HBox :=
  { p := 13723, k := 952684, v := 482088, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1739__GateII_HBoxData_0 : HBox :=
  { p := 13729, k := 952728, v := 481712, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1740__GateII_HBoxData_0 : HBox :=
  { p := 13751, k := 952888, v := 480332, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1741__GateII_HBoxData_0 : HBox :=
  { p := 13757, k := 952932, v := 479958, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1742__GateII_HBoxData_0 : HBox :=
  { p := 13759, k := 952946, v := 479832, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1743__GateII_HBoxData_0 : HBox :=
  { p := 13763, k := 952975, v := 479583, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1744__GateII_HBoxData_0 : HBox :=
  { p := 13781, k := 953106, v := 478462, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1745__GateII_HBoxData_0 : HBox :=
  { p := 13789, k := 953164, v := 477965, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1746__GateII_HBoxData_0 : HBox :=
  { p := 13799, k := 953237, v := 477346, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1747__GateII_HBoxData_0 : HBox :=
  { p := 13807, k := 953295, v := 476851, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1748__GateII_HBoxData_0 : HBox :=
  { p := 13829, k := 953454, v := 475493, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1749__GateII_HBoxData_0 : HBox :=
  { p := 13831, k := 953468, v := 475369, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1750__GateII_HBoxData_0 : HBox :=
  { p := 13841, k := 953541, v := 474755, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1751__GateII_HBoxData_0 : HBox :=
  { p := 13859, k := 953671, v := 473652, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1752__GateII_HBoxData_0 : HBox :=
  { p := 13873, k := 953771, v := 472795, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1753__GateII_HBoxData_0 : HBox :=
  { p := 13877, k := 953800, v := 472551, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1754__GateII_HBoxData_0 : HBox :=
  { p := 13879, k := 953815, v := 472430, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1755__GateII_HBoxData_0 : HBox :=
  { p := 13883, k := 953844, v := 472187, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1756__GateII_HBoxData_0 : HBox :=
  { p := 13901, k := 953973, v := 471092, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1757__GateII_HBoxData_0 : HBox :=
  { p := 13903, k := 953987, v := 470970, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1758__GateII_HBoxData_0 : HBox :=
  { p := 13907, k := 954016, v := 470728, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1759__GateII_HBoxData_0 : HBox :=
  { p := 13913, k := 954059, v := 470364, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1760__GateII_HBoxData_0 : HBox :=
  { p := 13921, k := 954117, v := 469881, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1761__GateII_HBoxData_0 : HBox :=
  { p := 13931, k := 954189, v := 469277, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1762__GateII_HBoxData_0 : HBox :=
  { p := 13933, k := 954203, v := 469156, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1763__GateII_HBoxData_0 : HBox :=
  { p := 13963, k := 954418, v := 467353, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1764__GateII_HBoxData_0 : HBox :=
  { p := 13967, k := 954447, v := 467113, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1765__GateII_HBoxData_0 : HBox :=
  { p := 13997, k := 954661, v := 465321, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1766__GateII_HBoxData_0 : HBox :=
  { p := 13999, k := 954676, v := 465203, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1767__GateII_HBoxData_0 : HBox :=
  { p := 14009, k := 954747, v := 464608, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1768__GateII_HBoxData_0 : HBox :=
  { p := 14011, k := 954761, v := 464489, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1769__GateII_HBoxData_0 : HBox :=
  { p := 14029, k := 954890, v := 463423, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1770__GateII_HBoxData_0 : HBox :=
  { p := 14033, k := 954918, v := 463186, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1771__GateII_HBoxData_0 : HBox :=
  { p := 14051, k := 955046, v := 462124, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1772__GateII_HBoxData_0 : HBox :=
  { p := 14057, k := 955089, v := 461771, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1773__GateII_HBoxData_0 : HBox :=
  { p := 14071, k := 955189, v := 460949, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1774__GateII_HBoxData_0 : HBox :=
  { p := 14081, k := 955260, v := 460363, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1775__GateII_HBoxData_0 : HBox :=
  { p := 14083, k := 955274, v := 460245, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1776__GateII_HBoxData_0 : HBox :=
  { p := 14087, k := 955302, v := 460011, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1777__GateII_HBoxData_0 : HBox :=
  { p := 14107, k := 955444, v := 458844, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1778__GateII_HBoxData_0 : HBox :=
  { p := 14143, k := 955699, v := 456754, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1779__GateII_HBoxData_0 : HBox :=
  { p := 14149, k := 955741, v := 456407, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1780__GateII_HBoxData_0 : HBox :=
  { p := 14153, k := 955770, v := 456177, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1781__GateII_HBoxData_0 : HBox :=
  { p := 14159, k := 955812, v := 455830, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1782__GateII_HBoxData_0 : HBox :=
  { p := 14173, k := 955911, v := 455024, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1783__GateII_HBoxData_0 : HBox :=
  { p := 14177, k := 955939, v := 454794, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1784__GateII_HBoxData_0 : HBox :=
  { p := 14197, k := 956080, v := 453647, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1785__GateII_HBoxData_0 : HBox :=
  { p := 14207, k := 956151, v := 453076, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1786__GateII_HBoxData_0 : HBox :=
  { p := 14221, k := 956249, v := 452277, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1787__GateII_HBoxData_0 : HBox :=
  { p := 14243, k := 956404, v := 451027, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1788__GateII_HBoxData_0 : HBox :=
  { p := 14249, k := 956446, v := 450686, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1789__GateII_HBoxData_0 : HBox :=
  { p := 14251, k := 956460, v := 450573, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1790__GateII_HBoxData_0 : HBox :=
  { p := 14281, k := 956670, v := 448879, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1791__GateII_HBoxData_0 : HBox :=
  { p := 14293, k := 956754, v := 448204, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1792__GateII_HBoxData_0 : HBox :=
  { p := 14303, k := 956824, v := 447643, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1793__GateII_HBoxData_0 : HBox :=
  { p := 14321, k := 956950, v := 446636, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1794__GateII_HBoxData_0 : HBox :=
  { p := 14323, k := 956964, v := 446524, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1795__GateII_HBoxData_0 : HBox :=
  { p := 14327, k := 956992, v := 446301, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1796__GateII_HBoxData_0 : HBox :=
  { p := 14341, k := 957089, v := 445520, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1797__GateII_HBoxData_0 : HBox :=
  { p := 14347, k := 957131, v := 445187, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1798__GateII_HBoxData_0 : HBox :=
  { p := 14369, k := 957284, v := 443966, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1799__GateII_HBoxData_0 : HBox :=
  { p := 14387, k := 957410, v := 442972, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1800__GateII_HBoxData_0 : HBox :=
  { p := 14389, k := 957423, v := 442861, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1801__GateII_HBoxData_0 : HBox :=
  { p := 14401, k := 957507, v := 442201, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1802__GateII_HBoxData_0 : HBox :=
  { p := 14407, k := 957548, v := 441871, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1803__GateII_HBoxData_0 : HBox :=
  { p := 14411, k := 957576, v := 441651, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1804__GateII_HBoxData_0 : HBox :=
  { p := 14419, k := 957632, v := 441213, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1805__GateII_HBoxData_0 : HBox :=
  { p := 14423, k := 957659, v := 440993, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1806__GateII_HBoxData_0 : HBox :=
  { p := 14431, k := 957715, v := 440555, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1807__GateII_HBoxData_0 : HBox :=
  { p := 14437, k := 957756, v := 440227, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1808__GateII_HBoxData_0 : HBox :=
  { p := 14447, k := 957826, v := 439682, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1809__GateII_HBoxData_0 : HBox :=
  { p := 14449, k := 957840, v := 439573, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1810__GateII_HBoxData_0 : HBox :=
  { p := 14461, k := 957923, v := 438920, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1811__GateII_HBoxData_0 : HBox :=
  { p := 14479, k := 958047, v := 437942, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1812__GateII_HBoxData_0 : HBox :=
  { p := 14489, k := 958116, v := 437401, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1813__GateII_HBoxData_0 : HBox :=
  { p := 14503, k := 958213, v := 436645, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1814__GateII_HBoxData_0 : HBox :=
  { p := 14519, k := 958323, v := 435783, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1815__GateII_HBoxData_0 : HBox :=
  { p := 14533, k := 958419, v := 435031, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1816__GateII_HBoxData_0 : HBox :=
  { p := 14537, k := 958447, v := 434817, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1817__GateII_HBoxData_0 : HBox :=
  { p := 14543, k := 958488, v := 434496, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1818__GateII_HBoxData_0 : HBox :=
  { p := 14549, k := 958529, v := 434174, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1819__GateII_HBoxData_0 : HBox :=
  { p := 14551, k := 958543, v := 434068, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1820__GateII_HBoxData_0 : HBox :=
  { p := 14557, k := 958584, v := 433747, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1821__GateII_HBoxData_0 : HBox :=
  { p := 14561, k := 958612, v := 433534, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1822__GateII_HBoxData_0 : HBox :=
  { p := 14563, k := 958625, v := 433427, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1823__GateII_HBoxData_0 : HBox :=
  { p := 14591, k := 958818, v := 431938, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1824__GateII_HBoxData_0 : HBox :=
  { p := 14593, k := 958831, v := 431832, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1825__GateII_HBoxData_0 : HBox :=
  { p := 14621, k := 959023, v := 430351, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1826__GateII_HBoxData_0 : HBox :=
  { p := 14627, k := 959064, v := 430035, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1827__GateII_HBoxData_0 : HBox :=
  { p := 14629, k := 959078, v := 429930, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1828__GateII_HBoxData_0 : HBox :=
  { p := 14633, k := 959105, v := 429719, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1829__GateII_HBoxData_0 : HBox :=
  { p := 14639, k := 959146, v := 429404, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1830__GateII_HBoxData_0 : HBox :=
  { p := 14653, k := 959242, v := 428669, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1831__GateII_HBoxData_0 : HBox :=
  { p := 14657, k := 959269, v := 428459, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1832__GateII_HBoxData_0 : HBox :=
  { p := 14669, k := 959351, v := 427832, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1833__GateII_HBoxData_0 : HBox :=
  { p := 14683, k := 959446, v := 427101, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1834__GateII_HBoxData_0 : HBox :=
  { p := 14699, k := 959555, v := 426268, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1835__GateII_HBoxData_0 : HBox :=
  { p := 14713, k := 959650, v := 425541, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1836__GateII_HBoxData_0 : HBox :=
  { p := 14717, k := 959677, v := 425334, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1837__GateII_HBoxData_0 : HBox :=
  { p := 14723, k := 959718, v := 425024, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1838__GateII_HBoxData_0 : HBox :=
  { p := 14731, k := 959772, v := 424610, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1839__GateII_HBoxData_0 : HBox :=
  { p := 14737, k := 959813, v := 424300, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1840__GateII_HBoxData_0 : HBox :=
  { p := 14741, k := 959840, v := 424094, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1841__GateII_HBoxData_0 : HBox :=
  { p := 14747, k := 959881, v := 423785, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1842__GateII_HBoxData_0 : HBox :=
  { p := 14753, k := 959922, v := 423477, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1843__GateII_HBoxData_0 : HBox :=
  { p := 14759, k := 959962, v := 423168, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1844__GateII_HBoxData_0 : HBox :=
  { p := 14767, k := 960017, v := 422758, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1845__GateII_HBoxData_0 : HBox :=
  { p := 14771, k := 960044, v := 422552, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1846__GateII_HBoxData_0 : HBox :=
  { p := 14779, k := 960098, v := 422143, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1847__GateII_HBoxData_0 : HBox :=
  { p := 14783, k := 960125, v := 421938, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1848__GateII_HBoxData_0 : HBox :=
  { p := 14797, k := 960219, v := 421222, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1849__GateII_HBoxData_0 : HBox :=
  { p := 14813, k := 960328, v := 420408, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1850__GateII_HBoxData_0 : HBox :=
  { p := 14821, k := 960382, v := 420001, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1851__GateII_HBoxData_0 : HBox :=
  { p := 14827, k := 960422, v := 419696, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1852__GateII_HBoxData_0 : HBox :=
  { p := 14831, k := 960449, v := 419494, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1853__GateII_HBoxData_0 : HBox :=
  { p := 14843, k := 960530, v := 418886, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1854__GateII_HBoxData_0 : HBox :=
  { p := 14851, k := 960584, v := 418482, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1855__GateII_HBoxData_0 : HBox :=
  { p := 14867, k := 960691, v := 417675, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1856__GateII_HBoxData_0 : HBox :=
  { p := 14869, k := 960705, v := 417574, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1857__GateII_HBoxData_0 : HBox :=
  { p := 14879, k := 960772, v := 417071, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1858__GateII_HBoxData_0 : HBox :=
  { p := 14887, k := 960826, v := 416670, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1859__GateII_HBoxData_0 : HBox :=
  { p := 14891, k := 960853, v := 416470, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1860__GateII_HBoxData_0 : HBox :=
  { p := 14897, k := 960893, v := 416169, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1861__GateII_HBoxData_0 : HBox :=
  { p := 14923, k := 961067, v := 414870, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1862__GateII_HBoxData_0 : HBox :=
  { p := 14929, k := 961108, v := 414572, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1863__GateII_HBoxData_0 : HBox :=
  { p := 14939, k := 961175, v := 414075, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1864__GateII_HBoxData_0 : HBox :=
  { p := 14947, k := 961228, v := 413677, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1865__GateII_HBoxData_0 : HBox :=
  { p := 14951, k := 961255, v := 413479, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1866__GateII_HBoxData_0 : HBox :=
  { p := 14957, k := 961295, v := 413182, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1867__GateII_HBoxData_0 : HBox :=
  { p := 14969, k := 961375, v := 412588, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1868__GateII_HBoxData_0 : HBox :=
  { p := 14983, k := 961469, v := 411898, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1869__GateII_HBoxData_0 : HBox :=
  { p := 15013, k := 961669, v := 410424, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1870__GateII_HBoxData_0 : HBox :=
  { p := 15017, k := 961695, v := 410227, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1871__GateII_HBoxData_0 : HBox :=
  { p := 15031, k := 961789, v := 409543, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1872__GateII_HBoxData_0 : HBox :=
  { p := 15053, k := 961935, v := 408471, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1873__GateII_HBoxData_0 : HBox :=
  { p := 15061, k := 961988, v := 408082, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1874__GateII_HBoxData_0 : HBox :=
  { p := 15073, k := 962068, v := 407500, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1875__GateII_HBoxData_0 : HBox :=
  { p := 15077, k := 962094, v := 407306, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1876__GateII_HBoxData_0 : HBox :=
  { p := 15083, k := 962134, v := 407016, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1877__GateII_HBoxData_0 : HBox :=
  { p := 15091, k := 962187, v := 406629, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1878__GateII_HBoxData_0 : HBox :=
  { p := 15101, k := 962253, v := 406146, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1879__GateII_HBoxData_0 : HBox :=
  { p := 15107, k := 962293, v := 405858, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1880__GateII_HBoxData_0 : HBox :=
  { p := 15121, k := 962385, v := 405184, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1881__GateII_HBoxData_0 : HBox :=
  { p := 15131, k := 962452, v := 404705, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1882__GateII_HBoxData_0 : HBox :=
  { p := 15137, k := 962491, v := 404417, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1883__GateII_HBoxData_0 : HBox :=
  { p := 15139, k := 962504, v := 404321, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1884__GateII_HBoxData_0 : HBox :=
  { p := 15149, k := 962570, v := 403842, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1885__GateII_HBoxData_0 : HBox :=
  { p := 15161, k := 962650, v := 403270, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1886__GateII_HBoxData_0 : HBox :=
  { p := 15173, k := 962729, v := 402699, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1887__GateII_HBoxData_0 : HBox :=
  { p := 15187, k := 962821, v := 402033, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1888__GateII_HBoxData_0 : HBox :=
  { p := 15193, k := 962861, v := 401749, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1889__GateII_HBoxData_0 : HBox :=
  { p := 15199, k := 962900, v := 401465, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1890__GateII_HBoxData_0 : HBox :=
  { p := 15217, k := 963018, v := 400613, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1891__GateII_HBoxData_0 : HBox :=
  { p := 15227, k := 963084, v := 400142, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1892__GateII_HBoxData_0 : HBox :=
  { p := 15233, k := 963123, v := 399859, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1893__GateII_HBoxData_0 : HBox :=
  { p := 15241, k := 963176, v := 399484, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1894__GateII_HBoxData_0 : HBox :=
  { p := 15259, k := 963294, v := 398639, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1895__GateII_HBoxData_0 : HBox :=
  { p := 15263, k := 963320, v := 398452, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1896__GateII_HBoxData_0 : HBox :=
  { p := 15269, k := 963359, v := 398171, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1897__GateII_HBoxData_0 : HBox :=
  { p := 15271, k := 963373, v := 398078, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1898__GateII_HBoxData_0 : HBox :=
  { p := 15277, k := 963412, v := 397798, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1899__GateII_HBoxData_0 : HBox :=
  { p := 15287, k := 963477, v := 397331, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1900__GateII_HBoxData_0 : HBox :=
  { p := 15289, k := 963490, v := 397238, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1901__GateII_HBoxData_0 : HBox :=
  { p := 15299, k := 963556, v := 396773, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1902__GateII_HBoxData_0 : HBox :=
  { p := 15307, k := 963608, v := 396401, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1903__GateII_HBoxData_0 : HBox :=
  { p := 15313, k := 963647, v := 396122, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1904__GateII_HBoxData_0 : HBox :=
  { p := 15319, k := 963686, v := 395844, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1905__GateII_HBoxData_0 : HBox :=
  { p := 15329, k := 963752, v := 395382, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1906__GateII_HBoxData_0 : HBox :=
  { p := 15331, k := 963765, v := 395289, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1907__GateII_HBoxData_0 : HBox :=
  { p := 15349, k := 963882, v := 394458, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1908__GateII_HBoxData_0 : HBox :=
  { p := 15359, k := 963947, v := 393998, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1909__GateII_HBoxData_0 : HBox :=
  { p := 15361, k := 963960, v := 393906, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1910__GateII_HBoxData_0 : HBox :=
  { p := 15373, k := 964038, v := 393355, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1911__GateII_HBoxData_0 : HBox :=
  { p := 15377, k := 964064, v := 393172, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1912__GateII_HBoxData_0 : HBox :=
  { p := 15383, k := 964103, v := 392897, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1913__GateII_HBoxData_0 : HBox :=
  { p := 15391, k := 964155, v := 392531, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1914__GateII_HBoxData_0 : HBox :=
  { p := 15401, k := 964220, v := 392074, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1915__GateII_HBoxData_0 : HBox :=
  { p := 15413, k := 964298, v := 391527, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1916__GateII_HBoxData_0 : HBox :=
  { p := 15427, k := 964389, v := 390890, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1917__GateII_HBoxData_0 : HBox :=
  { p := 15439, k := 964467, v := 390346, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1918__GateII_HBoxData_0 : HBox :=
  { p := 15443, k := 964493, v := 390165, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1919__GateII_HBoxData_0 : HBox :=
  { p := 15451, k := 964544, v := 389802, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1920__GateII_HBoxData_0 : HBox :=
  { p := 15461, k := 964609, v := 389350, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1921__GateII_HBoxData_0 : HBox :=
  { p := 15467, k := 964648, v := 389080, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1922__GateII_HBoxData_0 : HBox :=
  { p := 15473, k := 964687, v := 388809, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1923__GateII_HBoxData_0 : HBox :=
  { p := 15493, k := 964816, v := 387910, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1924__GateII_HBoxData_0 : HBox :=
  { p := 15497, k := 964842, v := 387730, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1925__GateII_HBoxData_0 : HBox :=
  { p := 15511, k := 964932, v := 387103, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1926__GateII_HBoxData_0 : HBox :=
  { p := 15527, k := 965035, v := 386388, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1927__GateII_HBoxData_0 : HBox :=
  { p := 15541, k := 965125, v := 385764, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1928__GateII_HBoxData_0 : HBox :=
  { p := 15551, k := 965190, v := 385320, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1929__GateII_HBoxData_0 : HBox :=
  { p := 15559, k := 965241, v := 384964, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1930__GateII_HBoxData_0 : HBox :=
  { p := 15569, k := 965305, v := 384521, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1931__GateII_HBoxData_0 : HBox :=
  { p := 15581, k := 965382, v := 383990, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1932__GateII_HBoxData_0 : HBox :=
  { p := 15583, k := 965395, v := 383902, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1933__GateII_HBoxData_0 : HBox :=
  { p := 15601, k := 965511, v := 383108, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1934__GateII_HBoxData_0 : HBox :=
  { p := 15607, k := 965549, v := 382844, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1935__GateII_HBoxData_0 : HBox :=
  { p := 15619, k := 965626, v := 382317, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1936__GateII_HBoxData_0 : HBox :=
  { p := 15629, k := 965690, v := 381878, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1937__GateII_HBoxData_0 : HBox :=
  { p := 15641, k := 965767, v := 381353, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1938__GateII_HBoxData_0 : HBox :=
  { p := 15643, k := 965779, v := 381265, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1939__GateII_HBoxData_0 : HBox :=
  { p := 15647, k := 965805, v := 381091, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1940__GateII_HBoxData_0 : HBox :=
  { p := 15649, k := 965818, v := 381004, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1941__GateII_HBoxData_0 : HBox :=
  { p := 15661, k := 965894, v := 380480, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1942__GateII_HBoxData_0 : HBox :=
  { p := 15667, k := 965933, v := 380219, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1943__GateII_HBoxData_0 : HBox :=
  { p := 15671, k := 965958, v := 380045, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1944__GateII_HBoxData_0 : HBox :=
  { p := 15679, k := 966009, v := 379697, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1945__GateII_HBoxData_0 : HBox :=
  { p := 15683, k := 966035, v := 379524, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1946__GateII_HBoxData_0 : HBox :=
  { p := 15727, k := 966315, v := 377621, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1947__GateII_HBoxData_0 : HBox :=
  { p := 15731, k := 966340, v := 377449, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1948__GateII_HBoxData_0 : HBox :=
  { p := 15733, k := 966353, v := 377363, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1949__GateII_HBoxData_0 : HBox :=
  { p := 15737, k := 966378, v := 377191, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1950__GateII_HBoxData_0 : HBox :=
  { p := 15739, k := 966391, v := 377105, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1951__GateII_HBoxData_0 : HBox :=
  { p := 15749, k := 966455, v := 376676, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1952__GateII_HBoxData_0 : HBox :=
  { p := 15761, k := 966531, v := 376162, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1953__GateII_HBoxData_0 : HBox :=
  { p := 15767, k := 966569, v := 375905, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1954__GateII_HBoxData_0 : HBox :=
  { p := 15773, k := 966607, v := 375649, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1955__GateII_HBoxData_0 : HBox :=
  { p := 15787, k := 966696, v := 375052, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1956__GateII_HBoxData_0 : HBox :=
  { p := 15791, k := 966721, v := 374881, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1957__GateII_HBoxData_0 : HBox :=
  { p := 15797, k := 966759, v := 374626, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1958__GateII_HBoxData_0 : HBox :=
  { p := 15803, k := 966797, v := 374371, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1959__GateII_HBoxData_0 : HBox :=
  { p := 15809, k := 966835, v := 374116, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1960__GateII_HBoxData_0 : HBox :=
  { p := 15817, k := 966886, v := 373777, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1961__GateII_HBoxData_0 : HBox :=
  { p := 15823, k := 966923, v := 373522, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1962__GateII_HBoxData_0 : HBox :=
  { p := 15859, k := 967151, v := 372004, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1963__GateII_HBoxData_0 : HBox :=
  { p := 15877, k := 967264, v := 371247, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1964__GateII_HBoxData_0 : HBox :=
  { p := 15881, k := 967289, v := 371079, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1965__GateII_HBoxData_0 : HBox :=
  { p := 15887, k := 967327, v := 370828, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1966__GateII_HBoxData_0 : HBox :=
  { p := 15889, k := 967340, v := 370745, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1967__GateII_HBoxData_0 : HBox :=
  { p := 15901, k := 967415, v := 370243, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1968__GateII_HBoxData_0 : HBox :=
  { p := 15907, k := 967453, v := 369993, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1969__GateII_HBoxData_0 : HBox :=
  { p := 15913, k := 967491, v := 369743, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1970__GateII_HBoxData_0 : HBox :=
  { p := 15919, k := 967528, v := 369492, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1971__GateII_HBoxData_0 : HBox :=
  { p := 15923, k := 967553, v := 369326, N := 29, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1972__GateII_HBoxData_0 : HBox :=
  { p := 15937, k := 967641, v := 368744, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1973__GateII_HBoxData_0 : HBox :=
  { p := 15959, k := 967779, v := 367833, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1974__GateII_HBoxData_0 : HBox :=
  { p := 15971, k := 967854, v := 367337, N := 29, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1975__GateII_HBoxData_0 : HBox :=
  { p := 15973, k := 967867, v := 367255, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1976__GateII_HBoxData_0 : HBox :=
  { p := 15991, k := 967980, v := 366514, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1977__GateII_HBoxData_0 : HBox :=
  { p := 16001, k := 968042, v := 366103, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1978__GateII_HBoxData_0 : HBox :=
  { p := 16007, k := 968080, v := 365857, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1979__GateII_HBoxData_0 : HBox :=
  { p := 16033, k := 968242, v := 364794, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1980__GateII_HBoxData_0 : HBox :=
  { p := 16057, k := 968392, v := 363816, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1981__GateII_HBoxData_0 : HBox :=
  { p := 16061, k := 968416, v := 363653, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1982__GateII_HBoxData_0 : HBox :=
  { p := 16063, k := 968429, v := 363572, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1983__GateII_HBoxData_0 : HBox :=
  { p := 16067, k := 968454, v := 363410, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1984__GateII_HBoxData_0 : HBox :=
  { p := 16069, k := 968466, v := 363329, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1985__GateII_HBoxData_0 : HBox :=
  { p := 16073, k := 968491, v := 363167, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1986__GateII_HBoxData_0 : HBox :=
  { p := 16087, k := 968578, v := 362600, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1987__GateII_HBoxData_0 : HBox :=
  { p := 16091, k := 968603, v := 362438, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1988__GateII_HBoxData_0 : HBox :=
  { p := 16097, k := 968640, v := 362196, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1989__GateII_HBoxData_0 : HBox :=
  { p := 16103, k := 968678, v := 361954, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1990__GateII_HBoxData_0 : HBox :=
  { p := 16111, k := 968727, v := 361631, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1991__GateII_HBoxData_0 : HBox :=
  { p := 16127, k := 968827, v := 360989, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1992__GateII_HBoxData_0 : HBox :=
  { p := 16139, k := 968901, v := 360507, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1993__GateII_HBoxData_0 : HBox :=
  { p := 16141, k := 968913, v := 360427, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1994__GateII_HBoxData_0 : HBox :=
  { p := 16183, k := 969173, v := 358750, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1995__GateII_HBoxData_0 : HBox :=
  { p := 16187, k := 969198, v := 358592, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1996__GateII_HBoxData_0 : HBox :=
  { p := 16189, k := 969210, v := 358512, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1997__GateII_HBoxData_0 : HBox :=
  { p := 16193, k := 969235, v := 358353, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1998__GateII_HBoxData_0 : HBox :=
  { p := 16217, k := 969383, v := 357402, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

set_option maxHeartbeats 2000000 in
private def hbox_0_1999__GateII_HBoxData_0 : HBox :=
  { p := 16223, k := 969420, v := 357165, N := 28, hp := by norm_num, hk := by norm_num, hv := fun _ => by norm_num, htaylor := fun _ => by norm_num [Finset.sum_range_succ] }

def boxChunk_0 : List HBox := [
  hbox_0_0__GateII_HBoxData_0,
  hbox_0_1__GateII_HBoxData_0,
  hbox_0_2__GateII_HBoxData_0,
  hbox_0_3__GateII_HBoxData_0,
  hbox_0_4__GateII_HBoxData_0,
  hbox_0_5__GateII_HBoxData_0,
  hbox_0_6__GateII_HBoxData_0,
  hbox_0_7__GateII_HBoxData_0,
  hbox_0_8__GateII_HBoxData_0,
  hbox_0_9__GateII_HBoxData_0,
  hbox_0_10__GateII_HBoxData_0,
  hbox_0_11__GateII_HBoxData_0,
  hbox_0_12__GateII_HBoxData_0,
  hbox_0_13__GateII_HBoxData_0,
  hbox_0_14__GateII_HBoxData_0,
  hbox_0_15__GateII_HBoxData_0,
  hbox_0_16__GateII_HBoxData_0,
  hbox_0_17__GateII_HBoxData_0,
  hbox_0_18__GateII_HBoxData_0,
  hbox_0_19__GateII_HBoxData_0,
  hbox_0_20__GateII_HBoxData_0,
  hbox_0_21__GateII_HBoxData_0,
  hbox_0_22__GateII_HBoxData_0,
  hbox_0_23__GateII_HBoxData_0,
  hbox_0_24__GateII_HBoxData_0,
  hbox_0_25__GateII_HBoxData_0,
  hbox_0_26__GateII_HBoxData_0,
  hbox_0_27__GateII_HBoxData_0,
  hbox_0_28__GateII_HBoxData_0,
  hbox_0_29__GateII_HBoxData_0,
  hbox_0_30__GateII_HBoxData_0,
  hbox_0_31__GateII_HBoxData_0,
  hbox_0_32__GateII_HBoxData_0,
  hbox_0_33__GateII_HBoxData_0,
  hbox_0_34__GateII_HBoxData_0,
  hbox_0_35__GateII_HBoxData_0,
  hbox_0_36__GateII_HBoxData_0,
  hbox_0_37__GateII_HBoxData_0,
  hbox_0_38__GateII_HBoxData_0,
  hbox_0_39__GateII_HBoxData_0,
  hbox_0_40__GateII_HBoxData_0,
  hbox_0_41__GateII_HBoxData_0,
  hbox_0_42__GateII_HBoxData_0,
  hbox_0_43__GateII_HBoxData_0,
  hbox_0_44__GateII_HBoxData_0,
  hbox_0_45__GateII_HBoxData_0,
  hbox_0_46__GateII_HBoxData_0,
  hbox_0_47__GateII_HBoxData_0,
  hbox_0_48__GateII_HBoxData_0,
  hbox_0_49__GateII_HBoxData_0,
  hbox_0_50__GateII_HBoxData_0,
  hbox_0_51__GateII_HBoxData_0,
  hbox_0_52__GateII_HBoxData_0,
  hbox_0_53__GateII_HBoxData_0,
  hbox_0_54__GateII_HBoxData_0,
  hbox_0_55__GateII_HBoxData_0,
  hbox_0_56__GateII_HBoxData_0,
  hbox_0_57__GateII_HBoxData_0,
  hbox_0_58__GateII_HBoxData_0,
  hbox_0_59__GateII_HBoxData_0,
  hbox_0_60__GateII_HBoxData_0,
  hbox_0_61__GateII_HBoxData_0,
  hbox_0_62__GateII_HBoxData_0,
  hbox_0_63__GateII_HBoxData_0,
  hbox_0_64__GateII_HBoxData_0,
  hbox_0_65__GateII_HBoxData_0,
  hbox_0_66__GateII_HBoxData_0,
  hbox_0_67__GateII_HBoxData_0,
  hbox_0_68__GateII_HBoxData_0,
  hbox_0_69__GateII_HBoxData_0,
  hbox_0_70__GateII_HBoxData_0,
  hbox_0_71__GateII_HBoxData_0,
  hbox_0_72__GateII_HBoxData_0,
  hbox_0_73__GateII_HBoxData_0,
  hbox_0_74__GateII_HBoxData_0,
  hbox_0_75__GateII_HBoxData_0,
  hbox_0_76__GateII_HBoxData_0,
  hbox_0_77__GateII_HBoxData_0,
  hbox_0_78__GateII_HBoxData_0,
  hbox_0_79__GateII_HBoxData_0,
  hbox_0_80__GateII_HBoxData_0,
  hbox_0_81__GateII_HBoxData_0,
  hbox_0_82__GateII_HBoxData_0,
  hbox_0_83__GateII_HBoxData_0,
  hbox_0_84__GateII_HBoxData_0,
  hbox_0_85__GateII_HBoxData_0,
  hbox_0_86__GateII_HBoxData_0,
  hbox_0_87__GateII_HBoxData_0,
  hbox_0_88__GateII_HBoxData_0,
  hbox_0_89__GateII_HBoxData_0,
  hbox_0_90__GateII_HBoxData_0,
  hbox_0_91__GateII_HBoxData_0,
  hbox_0_92__GateII_HBoxData_0,
  hbox_0_93__GateII_HBoxData_0,
  hbox_0_94__GateII_HBoxData_0,
  hbox_0_95__GateII_HBoxData_0,
  hbox_0_96__GateII_HBoxData_0,
  hbox_0_97__GateII_HBoxData_0,
  hbox_0_98__GateII_HBoxData_0,
  hbox_0_99__GateII_HBoxData_0,
  hbox_0_100__GateII_HBoxData_0,
  hbox_0_101__GateII_HBoxData_0,
  hbox_0_102__GateII_HBoxData_0,
  hbox_0_103__GateII_HBoxData_0,
  hbox_0_104__GateII_HBoxData_0,
  hbox_0_105__GateII_HBoxData_0,
  hbox_0_106__GateII_HBoxData_0,
  hbox_0_107__GateII_HBoxData_0,
  hbox_0_108__GateII_HBoxData_0,
  hbox_0_109__GateII_HBoxData_0,
  hbox_0_110__GateII_HBoxData_0,
  hbox_0_111__GateII_HBoxData_0,
  hbox_0_112__GateII_HBoxData_0,
  hbox_0_113__GateII_HBoxData_0,
  hbox_0_114__GateII_HBoxData_0,
  hbox_0_115__GateII_HBoxData_0,
  hbox_0_116__GateII_HBoxData_0,
  hbox_0_117__GateII_HBoxData_0,
  hbox_0_118__GateII_HBoxData_0,
  hbox_0_119__GateII_HBoxData_0,
  hbox_0_120__GateII_HBoxData_0,
  hbox_0_121__GateII_HBoxData_0,
  hbox_0_122__GateII_HBoxData_0,
  hbox_0_123__GateII_HBoxData_0,
  hbox_0_124__GateII_HBoxData_0,
  hbox_0_125__GateII_HBoxData_0,
  hbox_0_126__GateII_HBoxData_0,
  hbox_0_127__GateII_HBoxData_0,
  hbox_0_128__GateII_HBoxData_0,
  hbox_0_129__GateII_HBoxData_0,
  hbox_0_130__GateII_HBoxData_0,
  hbox_0_131__GateII_HBoxData_0,
  hbox_0_132__GateII_HBoxData_0,
  hbox_0_133__GateII_HBoxData_0,
  hbox_0_134__GateII_HBoxData_0,
  hbox_0_135__GateII_HBoxData_0,
  hbox_0_136__GateII_HBoxData_0,
  hbox_0_137__GateII_HBoxData_0,
  hbox_0_138__GateII_HBoxData_0,
  hbox_0_139__GateII_HBoxData_0,
  hbox_0_140__GateII_HBoxData_0,
  hbox_0_141__GateII_HBoxData_0,
  hbox_0_142__GateII_HBoxData_0,
  hbox_0_143__GateII_HBoxData_0,
  hbox_0_144__GateII_HBoxData_0,
  hbox_0_145__GateII_HBoxData_0,
  hbox_0_146__GateII_HBoxData_0,
  hbox_0_147__GateII_HBoxData_0,
  hbox_0_148__GateII_HBoxData_0,
  hbox_0_149__GateII_HBoxData_0,
  hbox_0_150__GateII_HBoxData_0,
  hbox_0_151__GateII_HBoxData_0,
  hbox_0_152__GateII_HBoxData_0,
  hbox_0_153__GateII_HBoxData_0,
  hbox_0_154__GateII_HBoxData_0,
  hbox_0_155__GateII_HBoxData_0,
  hbox_0_156__GateII_HBoxData_0,
  hbox_0_157__GateII_HBoxData_0,
  hbox_0_158__GateII_HBoxData_0,
  hbox_0_159__GateII_HBoxData_0,
  hbox_0_160__GateII_HBoxData_0,
  hbox_0_161__GateII_HBoxData_0,
  hbox_0_162__GateII_HBoxData_0,
  hbox_0_163__GateII_HBoxData_0,
  hbox_0_164__GateII_HBoxData_0,
  hbox_0_165__GateII_HBoxData_0,
  hbox_0_166__GateII_HBoxData_0,
  hbox_0_167__GateII_HBoxData_0,
  hbox_0_168__GateII_HBoxData_0,
  hbox_0_169__GateII_HBoxData_0,
  hbox_0_170__GateII_HBoxData_0,
  hbox_0_171__GateII_HBoxData_0,
  hbox_0_172__GateII_HBoxData_0,
  hbox_0_173__GateII_HBoxData_0,
  hbox_0_174__GateII_HBoxData_0,
  hbox_0_175__GateII_HBoxData_0,
  hbox_0_176__GateII_HBoxData_0,
  hbox_0_177__GateII_HBoxData_0,
  hbox_0_178__GateII_HBoxData_0,
  hbox_0_179__GateII_HBoxData_0,
  hbox_0_180__GateII_HBoxData_0,
  hbox_0_181__GateII_HBoxData_0,
  hbox_0_182__GateII_HBoxData_0,
  hbox_0_183__GateII_HBoxData_0,
  hbox_0_184__GateII_HBoxData_0,
  hbox_0_185__GateII_HBoxData_0,
  hbox_0_186__GateII_HBoxData_0,
  hbox_0_187__GateII_HBoxData_0,
  hbox_0_188__GateII_HBoxData_0,
  hbox_0_189__GateII_HBoxData_0,
  hbox_0_190__GateII_HBoxData_0,
  hbox_0_191__GateII_HBoxData_0,
  hbox_0_192__GateII_HBoxData_0,
  hbox_0_193__GateII_HBoxData_0,
  hbox_0_194__GateII_HBoxData_0,
  hbox_0_195__GateII_HBoxData_0,
  hbox_0_196__GateII_HBoxData_0,
  hbox_0_197__GateII_HBoxData_0,
  hbox_0_198__GateII_HBoxData_0,
  hbox_0_199__GateII_HBoxData_0,
  hbox_0_200__GateII_HBoxData_0,
  hbox_0_201__GateII_HBoxData_0,
  hbox_0_202__GateII_HBoxData_0,
  hbox_0_203__GateII_HBoxData_0,
  hbox_0_204__GateII_HBoxData_0,
  hbox_0_205__GateII_HBoxData_0,
  hbox_0_206__GateII_HBoxData_0,
  hbox_0_207__GateII_HBoxData_0,
  hbox_0_208__GateII_HBoxData_0,
  hbox_0_209__GateII_HBoxData_0,
  hbox_0_210__GateII_HBoxData_0,
  hbox_0_211__GateII_HBoxData_0,
  hbox_0_212__GateII_HBoxData_0,
  hbox_0_213__GateII_HBoxData_0,
  hbox_0_214__GateII_HBoxData_0,
  hbox_0_215__GateII_HBoxData_0,
  hbox_0_216__GateII_HBoxData_0,
  hbox_0_217__GateII_HBoxData_0,
  hbox_0_218__GateII_HBoxData_0,
  hbox_0_219__GateII_HBoxData_0,
  hbox_0_220__GateII_HBoxData_0,
  hbox_0_221__GateII_HBoxData_0,
  hbox_0_222__GateII_HBoxData_0,
  hbox_0_223__GateII_HBoxData_0,
  hbox_0_224__GateII_HBoxData_0,
  hbox_0_225__GateII_HBoxData_0,
  hbox_0_226__GateII_HBoxData_0,
  hbox_0_227__GateII_HBoxData_0,
  hbox_0_228__GateII_HBoxData_0,
  hbox_0_229__GateII_HBoxData_0,
  hbox_0_230__GateII_HBoxData_0,
  hbox_0_231__GateII_HBoxData_0,
  hbox_0_232__GateII_HBoxData_0,
  hbox_0_233__GateII_HBoxData_0,
  hbox_0_234__GateII_HBoxData_0,
  hbox_0_235__GateII_HBoxData_0,
  hbox_0_236__GateII_HBoxData_0,
  hbox_0_237__GateII_HBoxData_0,
  hbox_0_238__GateII_HBoxData_0,
  hbox_0_239__GateII_HBoxData_0,
  hbox_0_240__GateII_HBoxData_0,
  hbox_0_241__GateII_HBoxData_0,
  hbox_0_242__GateII_HBoxData_0,
  hbox_0_243__GateII_HBoxData_0,
  hbox_0_244__GateII_HBoxData_0,
  hbox_0_245__GateII_HBoxData_0,
  hbox_0_246__GateII_HBoxData_0,
  hbox_0_247__GateII_HBoxData_0,
  hbox_0_248__GateII_HBoxData_0,
  hbox_0_249__GateII_HBoxData_0,
  hbox_0_250__GateII_HBoxData_0,
  hbox_0_251__GateII_HBoxData_0,
  hbox_0_252__GateII_HBoxData_0,
  hbox_0_253__GateII_HBoxData_0,
  hbox_0_254__GateII_HBoxData_0,
  hbox_0_255__GateII_HBoxData_0,
  hbox_0_256__GateII_HBoxData_0,
  hbox_0_257__GateII_HBoxData_0,
  hbox_0_258__GateII_HBoxData_0,
  hbox_0_259__GateII_HBoxData_0,
  hbox_0_260__GateII_HBoxData_0,
  hbox_0_261__GateII_HBoxData_0,
  hbox_0_262__GateII_HBoxData_0,
  hbox_0_263__GateII_HBoxData_0,
  hbox_0_264__GateII_HBoxData_0,
  hbox_0_265__GateII_HBoxData_0,
  hbox_0_266__GateII_HBoxData_0,
  hbox_0_267__GateII_HBoxData_0,
  hbox_0_268__GateII_HBoxData_0,
  hbox_0_269__GateII_HBoxData_0,
  hbox_0_270__GateII_HBoxData_0,
  hbox_0_271__GateII_HBoxData_0,
  hbox_0_272__GateII_HBoxData_0,
  hbox_0_273__GateII_HBoxData_0,
  hbox_0_274__GateII_HBoxData_0,
  hbox_0_275__GateII_HBoxData_0,
  hbox_0_276__GateII_HBoxData_0,
  hbox_0_277__GateII_HBoxData_0,
  hbox_0_278__GateII_HBoxData_0,
  hbox_0_279__GateII_HBoxData_0,
  hbox_0_280__GateII_HBoxData_0,
  hbox_0_281__GateII_HBoxData_0,
  hbox_0_282__GateII_HBoxData_0,
  hbox_0_283__GateII_HBoxData_0,
  hbox_0_284__GateII_HBoxData_0,
  hbox_0_285__GateII_HBoxData_0,
  hbox_0_286__GateII_HBoxData_0,
  hbox_0_287__GateII_HBoxData_0,
  hbox_0_288__GateII_HBoxData_0,
  hbox_0_289__GateII_HBoxData_0,
  hbox_0_290__GateII_HBoxData_0,
  hbox_0_291__GateII_HBoxData_0,
  hbox_0_292__GateII_HBoxData_0,
  hbox_0_293__GateII_HBoxData_0,
  hbox_0_294__GateII_HBoxData_0,
  hbox_0_295__GateII_HBoxData_0,
  hbox_0_296__GateII_HBoxData_0,
  hbox_0_297__GateII_HBoxData_0,
  hbox_0_298__GateII_HBoxData_0,
  hbox_0_299__GateII_HBoxData_0,
  hbox_0_300__GateII_HBoxData_0,
  hbox_0_301__GateII_HBoxData_0,
  hbox_0_302__GateII_HBoxData_0,
  hbox_0_303__GateII_HBoxData_0,
  hbox_0_304__GateII_HBoxData_0,
  hbox_0_305__GateII_HBoxData_0,
  hbox_0_306__GateII_HBoxData_0,
  hbox_0_307__GateII_HBoxData_0,
  hbox_0_308__GateII_HBoxData_0,
  hbox_0_309__GateII_HBoxData_0,
  hbox_0_310__GateII_HBoxData_0,
  hbox_0_311__GateII_HBoxData_0,
  hbox_0_312__GateII_HBoxData_0,
  hbox_0_313__GateII_HBoxData_0,
  hbox_0_314__GateII_HBoxData_0,
  hbox_0_315__GateII_HBoxData_0,
  hbox_0_316__GateII_HBoxData_0,
  hbox_0_317__GateII_HBoxData_0,
  hbox_0_318__GateII_HBoxData_0,
  hbox_0_319__GateII_HBoxData_0,
  hbox_0_320__GateII_HBoxData_0,
  hbox_0_321__GateII_HBoxData_0,
  hbox_0_322__GateII_HBoxData_0,
  hbox_0_323__GateII_HBoxData_0,
  hbox_0_324__GateII_HBoxData_0,
  hbox_0_325__GateII_HBoxData_0,
  hbox_0_326__GateII_HBoxData_0,
  hbox_0_327__GateII_HBoxData_0,
  hbox_0_328__GateII_HBoxData_0,
  hbox_0_329__GateII_HBoxData_0,
  hbox_0_330__GateII_HBoxData_0,
  hbox_0_331__GateII_HBoxData_0,
  hbox_0_332__GateII_HBoxData_0,
  hbox_0_333__GateII_HBoxData_0,
  hbox_0_334__GateII_HBoxData_0,
  hbox_0_335__GateII_HBoxData_0,
  hbox_0_336__GateII_HBoxData_0,
  hbox_0_337__GateII_HBoxData_0,
  hbox_0_338__GateII_HBoxData_0,
  hbox_0_339__GateII_HBoxData_0,
  hbox_0_340__GateII_HBoxData_0,
  hbox_0_341__GateII_HBoxData_0,
  hbox_0_342__GateII_HBoxData_0,
  hbox_0_343__GateII_HBoxData_0,
  hbox_0_344__GateII_HBoxData_0,
  hbox_0_345__GateII_HBoxData_0,
  hbox_0_346__GateII_HBoxData_0,
  hbox_0_347__GateII_HBoxData_0,
  hbox_0_348__GateII_HBoxData_0,
  hbox_0_349__GateII_HBoxData_0,
  hbox_0_350__GateII_HBoxData_0,
  hbox_0_351__GateII_HBoxData_0,
  hbox_0_352__GateII_HBoxData_0,
  hbox_0_353__GateII_HBoxData_0,
  hbox_0_354__GateII_HBoxData_0,
  hbox_0_355__GateII_HBoxData_0,
  hbox_0_356__GateII_HBoxData_0,
  hbox_0_357__GateII_HBoxData_0,
  hbox_0_358__GateII_HBoxData_0,
  hbox_0_359__GateII_HBoxData_0,
  hbox_0_360__GateII_HBoxData_0,
  hbox_0_361__GateII_HBoxData_0,
  hbox_0_362__GateII_HBoxData_0,
  hbox_0_363__GateII_HBoxData_0,
  hbox_0_364__GateII_HBoxData_0,
  hbox_0_365__GateII_HBoxData_0,
  hbox_0_366__GateII_HBoxData_0,
  hbox_0_367__GateII_HBoxData_0,
  hbox_0_368__GateII_HBoxData_0,
  hbox_0_369__GateII_HBoxData_0,
  hbox_0_370__GateII_HBoxData_0,
  hbox_0_371__GateII_HBoxData_0,
  hbox_0_372__GateII_HBoxData_0,
  hbox_0_373__GateII_HBoxData_0,
  hbox_0_374__GateII_HBoxData_0,
  hbox_0_375__GateII_HBoxData_0,
  hbox_0_376__GateII_HBoxData_0,
  hbox_0_377__GateII_HBoxData_0,
  hbox_0_378__GateII_HBoxData_0,
  hbox_0_379__GateII_HBoxData_0,
  hbox_0_380__GateII_HBoxData_0,
  hbox_0_381__GateII_HBoxData_0,
  hbox_0_382__GateII_HBoxData_0,
  hbox_0_383__GateII_HBoxData_0,
  hbox_0_384__GateII_HBoxData_0,
  hbox_0_385__GateII_HBoxData_0,
  hbox_0_386__GateII_HBoxData_0,
  hbox_0_387__GateII_HBoxData_0,
  hbox_0_388__GateII_HBoxData_0,
  hbox_0_389__GateII_HBoxData_0,
  hbox_0_390__GateII_HBoxData_0,
  hbox_0_391__GateII_HBoxData_0,
  hbox_0_392__GateII_HBoxData_0,
  hbox_0_393__GateII_HBoxData_0,
  hbox_0_394__GateII_HBoxData_0,
  hbox_0_395__GateII_HBoxData_0,
  hbox_0_396__GateII_HBoxData_0,
  hbox_0_397__GateII_HBoxData_0,
  hbox_0_398__GateII_HBoxData_0,
  hbox_0_399__GateII_HBoxData_0,
  hbox_0_400__GateII_HBoxData_0,
  hbox_0_401__GateII_HBoxData_0,
  hbox_0_402__GateII_HBoxData_0,
  hbox_0_403__GateII_HBoxData_0,
  hbox_0_404__GateII_HBoxData_0,
  hbox_0_405__GateII_HBoxData_0,
  hbox_0_406__GateII_HBoxData_0,
  hbox_0_407__GateII_HBoxData_0,
  hbox_0_408__GateII_HBoxData_0,
  hbox_0_409__GateII_HBoxData_0,
  hbox_0_410__GateII_HBoxData_0,
  hbox_0_411__GateII_HBoxData_0,
  hbox_0_412__GateII_HBoxData_0,
  hbox_0_413__GateII_HBoxData_0,
  hbox_0_414__GateII_HBoxData_0,
  hbox_0_415__GateII_HBoxData_0,
  hbox_0_416__GateII_HBoxData_0,
  hbox_0_417__GateII_HBoxData_0,
  hbox_0_418__GateII_HBoxData_0,
  hbox_0_419__GateII_HBoxData_0,
  hbox_0_420__GateII_HBoxData_0,
  hbox_0_421__GateII_HBoxData_0,
  hbox_0_422__GateII_HBoxData_0,
  hbox_0_423__GateII_HBoxData_0,
  hbox_0_424__GateII_HBoxData_0,
  hbox_0_425__GateII_HBoxData_0,
  hbox_0_426__GateII_HBoxData_0,
  hbox_0_427__GateII_HBoxData_0,
  hbox_0_428__GateII_HBoxData_0,
  hbox_0_429__GateII_HBoxData_0,
  hbox_0_430__GateII_HBoxData_0,
  hbox_0_431__GateII_HBoxData_0,
  hbox_0_432__GateII_HBoxData_0,
  hbox_0_433__GateII_HBoxData_0,
  hbox_0_434__GateII_HBoxData_0,
  hbox_0_435__GateII_HBoxData_0,
  hbox_0_436__GateII_HBoxData_0,
  hbox_0_437__GateII_HBoxData_0,
  hbox_0_438__GateII_HBoxData_0,
  hbox_0_439__GateII_HBoxData_0,
  hbox_0_440__GateII_HBoxData_0,
  hbox_0_441__GateII_HBoxData_0,
  hbox_0_442__GateII_HBoxData_0,
  hbox_0_443__GateII_HBoxData_0,
  hbox_0_444__GateII_HBoxData_0,
  hbox_0_445__GateII_HBoxData_0,
  hbox_0_446__GateII_HBoxData_0,
  hbox_0_447__GateII_HBoxData_0,
  hbox_0_448__GateII_HBoxData_0,
  hbox_0_449__GateII_HBoxData_0,
  hbox_0_450__GateII_HBoxData_0,
  hbox_0_451__GateII_HBoxData_0,
  hbox_0_452__GateII_HBoxData_0,
  hbox_0_453__GateII_HBoxData_0,
  hbox_0_454__GateII_HBoxData_0,
  hbox_0_455__GateII_HBoxData_0,
  hbox_0_456__GateII_HBoxData_0,
  hbox_0_457__GateII_HBoxData_0,
  hbox_0_458__GateII_HBoxData_0,
  hbox_0_459__GateII_HBoxData_0,
  hbox_0_460__GateII_HBoxData_0,
  hbox_0_461__GateII_HBoxData_0,
  hbox_0_462__GateII_HBoxData_0,
  hbox_0_463__GateII_HBoxData_0,
  hbox_0_464__GateII_HBoxData_0,
  hbox_0_465__GateII_HBoxData_0,
  hbox_0_466__GateII_HBoxData_0,
  hbox_0_467__GateII_HBoxData_0,
  hbox_0_468__GateII_HBoxData_0,
  hbox_0_469__GateII_HBoxData_0,
  hbox_0_470__GateII_HBoxData_0,
  hbox_0_471__GateII_HBoxData_0,
  hbox_0_472__GateII_HBoxData_0,
  hbox_0_473__GateII_HBoxData_0,
  hbox_0_474__GateII_HBoxData_0,
  hbox_0_475__GateII_HBoxData_0,
  hbox_0_476__GateII_HBoxData_0,
  hbox_0_477__GateII_HBoxData_0,
  hbox_0_478__GateII_HBoxData_0,
  hbox_0_479__GateII_HBoxData_0,
  hbox_0_480__GateII_HBoxData_0,
  hbox_0_481__GateII_HBoxData_0,
  hbox_0_482__GateII_HBoxData_0,
  hbox_0_483__GateII_HBoxData_0,
  hbox_0_484__GateII_HBoxData_0,
  hbox_0_485__GateII_HBoxData_0,
  hbox_0_486__GateII_HBoxData_0,
  hbox_0_487__GateII_HBoxData_0,
  hbox_0_488__GateII_HBoxData_0,
  hbox_0_489__GateII_HBoxData_0,
  hbox_0_490__GateII_HBoxData_0,
  hbox_0_491__GateII_HBoxData_0,
  hbox_0_492__GateII_HBoxData_0,
  hbox_0_493__GateII_HBoxData_0,
  hbox_0_494__GateII_HBoxData_0,
  hbox_0_495__GateII_HBoxData_0,
  hbox_0_496__GateII_HBoxData_0,
  hbox_0_497__GateII_HBoxData_0,
  hbox_0_498__GateII_HBoxData_0,
  hbox_0_499__GateII_HBoxData_0,
  hbox_0_500__GateII_HBoxData_0,
  hbox_0_501__GateII_HBoxData_0,
  hbox_0_502__GateII_HBoxData_0,
  hbox_0_503__GateII_HBoxData_0,
  hbox_0_504__GateII_HBoxData_0,
  hbox_0_505__GateII_HBoxData_0,
  hbox_0_506__GateII_HBoxData_0,
  hbox_0_507__GateII_HBoxData_0,
  hbox_0_508__GateII_HBoxData_0,
  hbox_0_509__GateII_HBoxData_0,
  hbox_0_510__GateII_HBoxData_0,
  hbox_0_511__GateII_HBoxData_0,
  hbox_0_512__GateII_HBoxData_0,
  hbox_0_513__GateII_HBoxData_0,
  hbox_0_514__GateII_HBoxData_0,
  hbox_0_515__GateII_HBoxData_0,
  hbox_0_516__GateII_HBoxData_0,
  hbox_0_517__GateII_HBoxData_0,
  hbox_0_518__GateII_HBoxData_0,
  hbox_0_519__GateII_HBoxData_0,
  hbox_0_520__GateII_HBoxData_0,
  hbox_0_521__GateII_HBoxData_0,
  hbox_0_522__GateII_HBoxData_0,
  hbox_0_523__GateII_HBoxData_0,
  hbox_0_524__GateII_HBoxData_0,
  hbox_0_525__GateII_HBoxData_0,
  hbox_0_526__GateII_HBoxData_0,
  hbox_0_527__GateII_HBoxData_0,
  hbox_0_528__GateII_HBoxData_0,
  hbox_0_529__GateII_HBoxData_0,
  hbox_0_530__GateII_HBoxData_0,
  hbox_0_531__GateII_HBoxData_0,
  hbox_0_532__GateII_HBoxData_0,
  hbox_0_533__GateII_HBoxData_0,
  hbox_0_534__GateII_HBoxData_0,
  hbox_0_535__GateII_HBoxData_0,
  hbox_0_536__GateII_HBoxData_0,
  hbox_0_537__GateII_HBoxData_0,
  hbox_0_538__GateII_HBoxData_0,
  hbox_0_539__GateII_HBoxData_0,
  hbox_0_540__GateII_HBoxData_0,
  hbox_0_541__GateII_HBoxData_0,
  hbox_0_542__GateII_HBoxData_0,
  hbox_0_543__GateII_HBoxData_0,
  hbox_0_544__GateII_HBoxData_0,
  hbox_0_545__GateII_HBoxData_0,
  hbox_0_546__GateII_HBoxData_0,
  hbox_0_547__GateII_HBoxData_0,
  hbox_0_548__GateII_HBoxData_0,
  hbox_0_549__GateII_HBoxData_0,
  hbox_0_550__GateII_HBoxData_0,
  hbox_0_551__GateII_HBoxData_0,
  hbox_0_552__GateII_HBoxData_0,
  hbox_0_553__GateII_HBoxData_0,
  hbox_0_554__GateII_HBoxData_0,
  hbox_0_555__GateII_HBoxData_0,
  hbox_0_556__GateII_HBoxData_0,
  hbox_0_557__GateII_HBoxData_0,
  hbox_0_558__GateII_HBoxData_0,
  hbox_0_559__GateII_HBoxData_0,
  hbox_0_560__GateII_HBoxData_0,
  hbox_0_561__GateII_HBoxData_0,
  hbox_0_562__GateII_HBoxData_0,
  hbox_0_563__GateII_HBoxData_0,
  hbox_0_564__GateII_HBoxData_0,
  hbox_0_565__GateII_HBoxData_0,
  hbox_0_566__GateII_HBoxData_0,
  hbox_0_567__GateII_HBoxData_0,
  hbox_0_568__GateII_HBoxData_0,
  hbox_0_569__GateII_HBoxData_0,
  hbox_0_570__GateII_HBoxData_0,
  hbox_0_571__GateII_HBoxData_0,
  hbox_0_572__GateII_HBoxData_0,
  hbox_0_573__GateII_HBoxData_0,
  hbox_0_574__GateII_HBoxData_0,
  hbox_0_575__GateII_HBoxData_0,
  hbox_0_576__GateII_HBoxData_0,
  hbox_0_577__GateII_HBoxData_0,
  hbox_0_578__GateII_HBoxData_0,
  hbox_0_579__GateII_HBoxData_0,
  hbox_0_580__GateII_HBoxData_0,
  hbox_0_581__GateII_HBoxData_0,
  hbox_0_582__GateII_HBoxData_0,
  hbox_0_583__GateII_HBoxData_0,
  hbox_0_584__GateII_HBoxData_0,
  hbox_0_585__GateII_HBoxData_0,
  hbox_0_586__GateII_HBoxData_0,
  hbox_0_587__GateII_HBoxData_0,
  hbox_0_588__GateII_HBoxData_0,
  hbox_0_589__GateII_HBoxData_0,
  hbox_0_590__GateII_HBoxData_0,
  hbox_0_591__GateII_HBoxData_0,
  hbox_0_592__GateII_HBoxData_0,
  hbox_0_593__GateII_HBoxData_0,
  hbox_0_594__GateII_HBoxData_0,
  hbox_0_595__GateII_HBoxData_0,
  hbox_0_596__GateII_HBoxData_0,
  hbox_0_597__GateII_HBoxData_0,
  hbox_0_598__GateII_HBoxData_0,
  hbox_0_599__GateII_HBoxData_0,
  hbox_0_600__GateII_HBoxData_0,
  hbox_0_601__GateII_HBoxData_0,
  hbox_0_602__GateII_HBoxData_0,
  hbox_0_603__GateII_HBoxData_0,
  hbox_0_604__GateII_HBoxData_0,
  hbox_0_605__GateII_HBoxData_0,
  hbox_0_606__GateII_HBoxData_0,
  hbox_0_607__GateII_HBoxData_0,
  hbox_0_608__GateII_HBoxData_0,
  hbox_0_609__GateII_HBoxData_0,
  hbox_0_610__GateII_HBoxData_0,
  hbox_0_611__GateII_HBoxData_0,
  hbox_0_612__GateII_HBoxData_0,
  hbox_0_613__GateII_HBoxData_0,
  hbox_0_614__GateII_HBoxData_0,
  hbox_0_615__GateII_HBoxData_0,
  hbox_0_616__GateII_HBoxData_0,
  hbox_0_617__GateII_HBoxData_0,
  hbox_0_618__GateII_HBoxData_0,
  hbox_0_619__GateII_HBoxData_0,
  hbox_0_620__GateII_HBoxData_0,
  hbox_0_621__GateII_HBoxData_0,
  hbox_0_622__GateII_HBoxData_0,
  hbox_0_623__GateII_HBoxData_0,
  hbox_0_624__GateII_HBoxData_0,
  hbox_0_625__GateII_HBoxData_0,
  hbox_0_626__GateII_HBoxData_0,
  hbox_0_627__GateII_HBoxData_0,
  hbox_0_628__GateII_HBoxData_0,
  hbox_0_629__GateII_HBoxData_0,
  hbox_0_630__GateII_HBoxData_0,
  hbox_0_631__GateII_HBoxData_0,
  hbox_0_632__GateII_HBoxData_0,
  hbox_0_633__GateII_HBoxData_0,
  hbox_0_634__GateII_HBoxData_0,
  hbox_0_635__GateII_HBoxData_0,
  hbox_0_636__GateII_HBoxData_0,
  hbox_0_637__GateII_HBoxData_0,
  hbox_0_638__GateII_HBoxData_0,
  hbox_0_639__GateII_HBoxData_0,
  hbox_0_640__GateII_HBoxData_0,
  hbox_0_641__GateII_HBoxData_0,
  hbox_0_642__GateII_HBoxData_0,
  hbox_0_643__GateII_HBoxData_0,
  hbox_0_644__GateII_HBoxData_0,
  hbox_0_645__GateII_HBoxData_0,
  hbox_0_646__GateII_HBoxData_0,
  hbox_0_647__GateII_HBoxData_0,
  hbox_0_648__GateII_HBoxData_0,
  hbox_0_649__GateII_HBoxData_0,
  hbox_0_650__GateII_HBoxData_0,
  hbox_0_651__GateII_HBoxData_0,
  hbox_0_652__GateII_HBoxData_0,
  hbox_0_653__GateII_HBoxData_0,
  hbox_0_654__GateII_HBoxData_0,
  hbox_0_655__GateII_HBoxData_0,
  hbox_0_656__GateII_HBoxData_0,
  hbox_0_657__GateII_HBoxData_0,
  hbox_0_658__GateII_HBoxData_0,
  hbox_0_659__GateII_HBoxData_0,
  hbox_0_660__GateII_HBoxData_0,
  hbox_0_661__GateII_HBoxData_0,
  hbox_0_662__GateII_HBoxData_0,
  hbox_0_663__GateII_HBoxData_0,
  hbox_0_664__GateII_HBoxData_0,
  hbox_0_665__GateII_HBoxData_0,
  hbox_0_666__GateII_HBoxData_0,
  hbox_0_667__GateII_HBoxData_0,
  hbox_0_668__GateII_HBoxData_0,
  hbox_0_669__GateII_HBoxData_0,
  hbox_0_670__GateII_HBoxData_0,
  hbox_0_671__GateII_HBoxData_0,
  hbox_0_672__GateII_HBoxData_0,
  hbox_0_673__GateII_HBoxData_0,
  hbox_0_674__GateII_HBoxData_0,
  hbox_0_675__GateII_HBoxData_0,
  hbox_0_676__GateII_HBoxData_0,
  hbox_0_677__GateII_HBoxData_0,
  hbox_0_678__GateII_HBoxData_0,
  hbox_0_679__GateII_HBoxData_0,
  hbox_0_680__GateII_HBoxData_0,
  hbox_0_681__GateII_HBoxData_0,
  hbox_0_682__GateII_HBoxData_0,
  hbox_0_683__GateII_HBoxData_0,
  hbox_0_684__GateII_HBoxData_0,
  hbox_0_685__GateII_HBoxData_0,
  hbox_0_686__GateII_HBoxData_0,
  hbox_0_687__GateII_HBoxData_0,
  hbox_0_688__GateII_HBoxData_0,
  hbox_0_689__GateII_HBoxData_0,
  hbox_0_690__GateII_HBoxData_0,
  hbox_0_691__GateII_HBoxData_0,
  hbox_0_692__GateII_HBoxData_0,
  hbox_0_693__GateII_HBoxData_0,
  hbox_0_694__GateII_HBoxData_0,
  hbox_0_695__GateII_HBoxData_0,
  hbox_0_696__GateII_HBoxData_0,
  hbox_0_697__GateII_HBoxData_0,
  hbox_0_698__GateII_HBoxData_0,
  hbox_0_699__GateII_HBoxData_0,
  hbox_0_700__GateII_HBoxData_0,
  hbox_0_701__GateII_HBoxData_0,
  hbox_0_702__GateII_HBoxData_0,
  hbox_0_703__GateII_HBoxData_0,
  hbox_0_704__GateII_HBoxData_0,
  hbox_0_705__GateII_HBoxData_0,
  hbox_0_706__GateII_HBoxData_0,
  hbox_0_707__GateII_HBoxData_0,
  hbox_0_708__GateII_HBoxData_0,
  hbox_0_709__GateII_HBoxData_0,
  hbox_0_710__GateII_HBoxData_0,
  hbox_0_711__GateII_HBoxData_0,
  hbox_0_712__GateII_HBoxData_0,
  hbox_0_713__GateII_HBoxData_0,
  hbox_0_714__GateII_HBoxData_0,
  hbox_0_715__GateII_HBoxData_0,
  hbox_0_716__GateII_HBoxData_0,
  hbox_0_717__GateII_HBoxData_0,
  hbox_0_718__GateII_HBoxData_0,
  hbox_0_719__GateII_HBoxData_0,
  hbox_0_720__GateII_HBoxData_0,
  hbox_0_721__GateII_HBoxData_0,
  hbox_0_722__GateII_HBoxData_0,
  hbox_0_723__GateII_HBoxData_0,
  hbox_0_724__GateII_HBoxData_0,
  hbox_0_725__GateII_HBoxData_0,
  hbox_0_726__GateII_HBoxData_0,
  hbox_0_727__GateII_HBoxData_0,
  hbox_0_728__GateII_HBoxData_0,
  hbox_0_729__GateII_HBoxData_0,
  hbox_0_730__GateII_HBoxData_0,
  hbox_0_731__GateII_HBoxData_0,
  hbox_0_732__GateII_HBoxData_0,
  hbox_0_733__GateII_HBoxData_0,
  hbox_0_734__GateII_HBoxData_0,
  hbox_0_735__GateII_HBoxData_0,
  hbox_0_736__GateII_HBoxData_0,
  hbox_0_737__GateII_HBoxData_0,
  hbox_0_738__GateII_HBoxData_0,
  hbox_0_739__GateII_HBoxData_0,
  hbox_0_740__GateII_HBoxData_0,
  hbox_0_741__GateII_HBoxData_0,
  hbox_0_742__GateII_HBoxData_0,
  hbox_0_743__GateII_HBoxData_0,
  hbox_0_744__GateII_HBoxData_0,
  hbox_0_745__GateII_HBoxData_0,
  hbox_0_746__GateII_HBoxData_0,
  hbox_0_747__GateII_HBoxData_0,
  hbox_0_748__GateII_HBoxData_0,
  hbox_0_749__GateII_HBoxData_0,
  hbox_0_750__GateII_HBoxData_0,
  hbox_0_751__GateII_HBoxData_0,
  hbox_0_752__GateII_HBoxData_0,
  hbox_0_753__GateII_HBoxData_0,
  hbox_0_754__GateII_HBoxData_0,
  hbox_0_755__GateII_HBoxData_0,
  hbox_0_756__GateII_HBoxData_0,
  hbox_0_757__GateII_HBoxData_0,
  hbox_0_758__GateII_HBoxData_0,
  hbox_0_759__GateII_HBoxData_0,
  hbox_0_760__GateII_HBoxData_0,
  hbox_0_761__GateII_HBoxData_0,
  hbox_0_762__GateII_HBoxData_0,
  hbox_0_763__GateII_HBoxData_0,
  hbox_0_764__GateII_HBoxData_0,
  hbox_0_765__GateII_HBoxData_0,
  hbox_0_766__GateII_HBoxData_0,
  hbox_0_767__GateII_HBoxData_0,
  hbox_0_768__GateII_HBoxData_0,
  hbox_0_769__GateII_HBoxData_0,
  hbox_0_770__GateII_HBoxData_0,
  hbox_0_771__GateII_HBoxData_0,
  hbox_0_772__GateII_HBoxData_0,
  hbox_0_773__GateII_HBoxData_0,
  hbox_0_774__GateII_HBoxData_0,
  hbox_0_775__GateII_HBoxData_0,
  hbox_0_776__GateII_HBoxData_0,
  hbox_0_777__GateII_HBoxData_0,
  hbox_0_778__GateII_HBoxData_0,
  hbox_0_779__GateII_HBoxData_0,
  hbox_0_780__GateII_HBoxData_0,
  hbox_0_781__GateII_HBoxData_0,
  hbox_0_782__GateII_HBoxData_0,
  hbox_0_783__GateII_HBoxData_0,
  hbox_0_784__GateII_HBoxData_0,
  hbox_0_785__GateII_HBoxData_0,
  hbox_0_786__GateII_HBoxData_0,
  hbox_0_787__GateII_HBoxData_0,
  hbox_0_788__GateII_HBoxData_0,
  hbox_0_789__GateII_HBoxData_0,
  hbox_0_790__GateII_HBoxData_0,
  hbox_0_791__GateII_HBoxData_0,
  hbox_0_792__GateII_HBoxData_0,
  hbox_0_793__GateII_HBoxData_0,
  hbox_0_794__GateII_HBoxData_0,
  hbox_0_795__GateII_HBoxData_0,
  hbox_0_796__GateII_HBoxData_0,
  hbox_0_797__GateII_HBoxData_0,
  hbox_0_798__GateII_HBoxData_0,
  hbox_0_799__GateII_HBoxData_0,
  hbox_0_800__GateII_HBoxData_0,
  hbox_0_801__GateII_HBoxData_0,
  hbox_0_802__GateII_HBoxData_0,
  hbox_0_803__GateII_HBoxData_0,
  hbox_0_804__GateII_HBoxData_0,
  hbox_0_805__GateII_HBoxData_0,
  hbox_0_806__GateII_HBoxData_0,
  hbox_0_807__GateII_HBoxData_0,
  hbox_0_808__GateII_HBoxData_0,
  hbox_0_809__GateII_HBoxData_0,
  hbox_0_810__GateII_HBoxData_0,
  hbox_0_811__GateII_HBoxData_0,
  hbox_0_812__GateII_HBoxData_0,
  hbox_0_813__GateII_HBoxData_0,
  hbox_0_814__GateII_HBoxData_0,
  hbox_0_815__GateII_HBoxData_0,
  hbox_0_816__GateII_HBoxData_0,
  hbox_0_817__GateII_HBoxData_0,
  hbox_0_818__GateII_HBoxData_0,
  hbox_0_819__GateII_HBoxData_0,
  hbox_0_820__GateII_HBoxData_0,
  hbox_0_821__GateII_HBoxData_0,
  hbox_0_822__GateII_HBoxData_0,
  hbox_0_823__GateII_HBoxData_0,
  hbox_0_824__GateII_HBoxData_0,
  hbox_0_825__GateII_HBoxData_0,
  hbox_0_826__GateII_HBoxData_0,
  hbox_0_827__GateII_HBoxData_0,
  hbox_0_828__GateII_HBoxData_0,
  hbox_0_829__GateII_HBoxData_0,
  hbox_0_830__GateII_HBoxData_0,
  hbox_0_831__GateII_HBoxData_0,
  hbox_0_832__GateII_HBoxData_0,
  hbox_0_833__GateII_HBoxData_0,
  hbox_0_834__GateII_HBoxData_0,
  hbox_0_835__GateII_HBoxData_0,
  hbox_0_836__GateII_HBoxData_0,
  hbox_0_837__GateII_HBoxData_0,
  hbox_0_838__GateII_HBoxData_0,
  hbox_0_839__GateII_HBoxData_0,
  hbox_0_840__GateII_HBoxData_0,
  hbox_0_841__GateII_HBoxData_0,
  hbox_0_842__GateII_HBoxData_0,
  hbox_0_843__GateII_HBoxData_0,
  hbox_0_844__GateII_HBoxData_0,
  hbox_0_845__GateII_HBoxData_0,
  hbox_0_846__GateII_HBoxData_0,
  hbox_0_847__GateII_HBoxData_0,
  hbox_0_848__GateII_HBoxData_0,
  hbox_0_849__GateII_HBoxData_0,
  hbox_0_850__GateII_HBoxData_0,
  hbox_0_851__GateII_HBoxData_0,
  hbox_0_852__GateII_HBoxData_0,
  hbox_0_853__GateII_HBoxData_0,
  hbox_0_854__GateII_HBoxData_0,
  hbox_0_855__GateII_HBoxData_0,
  hbox_0_856__GateII_HBoxData_0,
  hbox_0_857__GateII_HBoxData_0,
  hbox_0_858__GateII_HBoxData_0,
  hbox_0_859__GateII_HBoxData_0,
  hbox_0_860__GateII_HBoxData_0,
  hbox_0_861__GateII_HBoxData_0,
  hbox_0_862__GateII_HBoxData_0,
  hbox_0_863__GateII_HBoxData_0,
  hbox_0_864__GateII_HBoxData_0,
  hbox_0_865__GateII_HBoxData_0,
  hbox_0_866__GateII_HBoxData_0,
  hbox_0_867__GateII_HBoxData_0,
  hbox_0_868__GateII_HBoxData_0,
  hbox_0_869__GateII_HBoxData_0,
  hbox_0_870__GateII_HBoxData_0,
  hbox_0_871__GateII_HBoxData_0,
  hbox_0_872__GateII_HBoxData_0,
  hbox_0_873__GateII_HBoxData_0,
  hbox_0_874__GateII_HBoxData_0,
  hbox_0_875__GateII_HBoxData_0,
  hbox_0_876__GateII_HBoxData_0,
  hbox_0_877__GateII_HBoxData_0,
  hbox_0_878__GateII_HBoxData_0,
  hbox_0_879__GateII_HBoxData_0,
  hbox_0_880__GateII_HBoxData_0,
  hbox_0_881__GateII_HBoxData_0,
  hbox_0_882__GateII_HBoxData_0,
  hbox_0_883__GateII_HBoxData_0,
  hbox_0_884__GateII_HBoxData_0,
  hbox_0_885__GateII_HBoxData_0,
  hbox_0_886__GateII_HBoxData_0,
  hbox_0_887__GateII_HBoxData_0,
  hbox_0_888__GateII_HBoxData_0,
  hbox_0_889__GateII_HBoxData_0,
  hbox_0_890__GateII_HBoxData_0,
  hbox_0_891__GateII_HBoxData_0,
  hbox_0_892__GateII_HBoxData_0,
  hbox_0_893__GateII_HBoxData_0,
  hbox_0_894__GateII_HBoxData_0,
  hbox_0_895__GateII_HBoxData_0,
  hbox_0_896__GateII_HBoxData_0,
  hbox_0_897__GateII_HBoxData_0,
  hbox_0_898__GateII_HBoxData_0,
  hbox_0_899__GateII_HBoxData_0,
  hbox_0_900__GateII_HBoxData_0,
  hbox_0_901__GateII_HBoxData_0,
  hbox_0_902__GateII_HBoxData_0,
  hbox_0_903__GateII_HBoxData_0,
  hbox_0_904__GateII_HBoxData_0,
  hbox_0_905__GateII_HBoxData_0,
  hbox_0_906__GateII_HBoxData_0,
  hbox_0_907__GateII_HBoxData_0,
  hbox_0_908__GateII_HBoxData_0,
  hbox_0_909__GateII_HBoxData_0,
  hbox_0_910__GateII_HBoxData_0,
  hbox_0_911__GateII_HBoxData_0,
  hbox_0_912__GateII_HBoxData_0,
  hbox_0_913__GateII_HBoxData_0,
  hbox_0_914__GateII_HBoxData_0,
  hbox_0_915__GateII_HBoxData_0,
  hbox_0_916__GateII_HBoxData_0,
  hbox_0_917__GateII_HBoxData_0,
  hbox_0_918__GateII_HBoxData_0,
  hbox_0_919__GateII_HBoxData_0,
  hbox_0_920__GateII_HBoxData_0,
  hbox_0_921__GateII_HBoxData_0,
  hbox_0_922__GateII_HBoxData_0,
  hbox_0_923__GateII_HBoxData_0,
  hbox_0_924__GateII_HBoxData_0,
  hbox_0_925__GateII_HBoxData_0,
  hbox_0_926__GateII_HBoxData_0,
  hbox_0_927__GateII_HBoxData_0,
  hbox_0_928__GateII_HBoxData_0,
  hbox_0_929__GateII_HBoxData_0,
  hbox_0_930__GateII_HBoxData_0,
  hbox_0_931__GateII_HBoxData_0,
  hbox_0_932__GateII_HBoxData_0,
  hbox_0_933__GateII_HBoxData_0,
  hbox_0_934__GateII_HBoxData_0,
  hbox_0_935__GateII_HBoxData_0,
  hbox_0_936__GateII_HBoxData_0,
  hbox_0_937__GateII_HBoxData_0,
  hbox_0_938__GateII_HBoxData_0,
  hbox_0_939__GateII_HBoxData_0,
  hbox_0_940__GateII_HBoxData_0,
  hbox_0_941__GateII_HBoxData_0,
  hbox_0_942__GateII_HBoxData_0,
  hbox_0_943__GateII_HBoxData_0,
  hbox_0_944__GateII_HBoxData_0,
  hbox_0_945__GateII_HBoxData_0,
  hbox_0_946__GateII_HBoxData_0,
  hbox_0_947__GateII_HBoxData_0,
  hbox_0_948__GateII_HBoxData_0,
  hbox_0_949__GateII_HBoxData_0,
  hbox_0_950__GateII_HBoxData_0,
  hbox_0_951__GateII_HBoxData_0,
  hbox_0_952__GateII_HBoxData_0,
  hbox_0_953__GateII_HBoxData_0,
  hbox_0_954__GateII_HBoxData_0,
  hbox_0_955__GateII_HBoxData_0,
  hbox_0_956__GateII_HBoxData_0,
  hbox_0_957__GateII_HBoxData_0,
  hbox_0_958__GateII_HBoxData_0,
  hbox_0_959__GateII_HBoxData_0,
  hbox_0_960__GateII_HBoxData_0,
  hbox_0_961__GateII_HBoxData_0,
  hbox_0_962__GateII_HBoxData_0,
  hbox_0_963__GateII_HBoxData_0,
  hbox_0_964__GateII_HBoxData_0,
  hbox_0_965__GateII_HBoxData_0,
  hbox_0_966__GateII_HBoxData_0,
  hbox_0_967__GateII_HBoxData_0,
  hbox_0_968__GateII_HBoxData_0,
  hbox_0_969__GateII_HBoxData_0,
  hbox_0_970__GateII_HBoxData_0,
  hbox_0_971__GateII_HBoxData_0,
  hbox_0_972__GateII_HBoxData_0,
  hbox_0_973__GateII_HBoxData_0,
  hbox_0_974__GateII_HBoxData_0,
  hbox_0_975__GateII_HBoxData_0,
  hbox_0_976__GateII_HBoxData_0,
  hbox_0_977__GateII_HBoxData_0,
  hbox_0_978__GateII_HBoxData_0,
  hbox_0_979__GateII_HBoxData_0,
  hbox_0_980__GateII_HBoxData_0,
  hbox_0_981__GateII_HBoxData_0,
  hbox_0_982__GateII_HBoxData_0,
  hbox_0_983__GateII_HBoxData_0,
  hbox_0_984__GateII_HBoxData_0,
  hbox_0_985__GateII_HBoxData_0,
  hbox_0_986__GateII_HBoxData_0,
  hbox_0_987__GateII_HBoxData_0,
  hbox_0_988__GateII_HBoxData_0,
  hbox_0_989__GateII_HBoxData_0,
  hbox_0_990__GateII_HBoxData_0,
  hbox_0_991__GateII_HBoxData_0,
  hbox_0_992__GateII_HBoxData_0,
  hbox_0_993__GateII_HBoxData_0,
  hbox_0_994__GateII_HBoxData_0,
  hbox_0_995__GateII_HBoxData_0,
  hbox_0_996__GateII_HBoxData_0,
  hbox_0_997__GateII_HBoxData_0,
  hbox_0_998__GateII_HBoxData_0,
  hbox_0_999__GateII_HBoxData_0,
  hbox_0_1000__GateII_HBoxData_0,
  hbox_0_1001__GateII_HBoxData_0,
  hbox_0_1002__GateII_HBoxData_0,
  hbox_0_1003__GateII_HBoxData_0,
  hbox_0_1004__GateII_HBoxData_0,
  hbox_0_1005__GateII_HBoxData_0,
  hbox_0_1006__GateII_HBoxData_0,
  hbox_0_1007__GateII_HBoxData_0,
  hbox_0_1008__GateII_HBoxData_0,
  hbox_0_1009__GateII_HBoxData_0,
  hbox_0_1010__GateII_HBoxData_0,
  hbox_0_1011__GateII_HBoxData_0,
  hbox_0_1012__GateII_HBoxData_0,
  hbox_0_1013__GateII_HBoxData_0,
  hbox_0_1014__GateII_HBoxData_0,
  hbox_0_1015__GateII_HBoxData_0,
  hbox_0_1016__GateII_HBoxData_0,
  hbox_0_1017__GateII_HBoxData_0,
  hbox_0_1018__GateII_HBoxData_0,
  hbox_0_1019__GateII_HBoxData_0,
  hbox_0_1020__GateII_HBoxData_0,
  hbox_0_1021__GateII_HBoxData_0,
  hbox_0_1022__GateII_HBoxData_0,
  hbox_0_1023__GateII_HBoxData_0,
  hbox_0_1024__GateII_HBoxData_0,
  hbox_0_1025__GateII_HBoxData_0,
  hbox_0_1026__GateII_HBoxData_0,
  hbox_0_1027__GateII_HBoxData_0,
  hbox_0_1028__GateII_HBoxData_0,
  hbox_0_1029__GateII_HBoxData_0,
  hbox_0_1030__GateII_HBoxData_0,
  hbox_0_1031__GateII_HBoxData_0,
  hbox_0_1032__GateII_HBoxData_0,
  hbox_0_1033__GateII_HBoxData_0,
  hbox_0_1034__GateII_HBoxData_0,
  hbox_0_1035__GateII_HBoxData_0,
  hbox_0_1036__GateII_HBoxData_0,
  hbox_0_1037__GateII_HBoxData_0,
  hbox_0_1038__GateII_HBoxData_0,
  hbox_0_1039__GateII_HBoxData_0,
  hbox_0_1040__GateII_HBoxData_0,
  hbox_0_1041__GateII_HBoxData_0,
  hbox_0_1042__GateII_HBoxData_0,
  hbox_0_1043__GateII_HBoxData_0,
  hbox_0_1044__GateII_HBoxData_0,
  hbox_0_1045__GateII_HBoxData_0,
  hbox_0_1046__GateII_HBoxData_0,
  hbox_0_1047__GateII_HBoxData_0,
  hbox_0_1048__GateII_HBoxData_0,
  hbox_0_1049__GateII_HBoxData_0,
  hbox_0_1050__GateII_HBoxData_0,
  hbox_0_1051__GateII_HBoxData_0,
  hbox_0_1052__GateII_HBoxData_0,
  hbox_0_1053__GateII_HBoxData_0,
  hbox_0_1054__GateII_HBoxData_0,
  hbox_0_1055__GateII_HBoxData_0,
  hbox_0_1056__GateII_HBoxData_0,
  hbox_0_1057__GateII_HBoxData_0,
  hbox_0_1058__GateII_HBoxData_0,
  hbox_0_1059__GateII_HBoxData_0,
  hbox_0_1060__GateII_HBoxData_0,
  hbox_0_1061__GateII_HBoxData_0,
  hbox_0_1062__GateII_HBoxData_0,
  hbox_0_1063__GateII_HBoxData_0,
  hbox_0_1064__GateII_HBoxData_0,
  hbox_0_1065__GateII_HBoxData_0,
  hbox_0_1066__GateII_HBoxData_0,
  hbox_0_1067__GateII_HBoxData_0,
  hbox_0_1068__GateII_HBoxData_0,
  hbox_0_1069__GateII_HBoxData_0,
  hbox_0_1070__GateII_HBoxData_0,
  hbox_0_1071__GateII_HBoxData_0,
  hbox_0_1072__GateII_HBoxData_0,
  hbox_0_1073__GateII_HBoxData_0,
  hbox_0_1074__GateII_HBoxData_0,
  hbox_0_1075__GateII_HBoxData_0,
  hbox_0_1076__GateII_HBoxData_0,
  hbox_0_1077__GateII_HBoxData_0,
  hbox_0_1078__GateII_HBoxData_0,
  hbox_0_1079__GateII_HBoxData_0,
  hbox_0_1080__GateII_HBoxData_0,
  hbox_0_1081__GateII_HBoxData_0,
  hbox_0_1082__GateII_HBoxData_0,
  hbox_0_1083__GateII_HBoxData_0,
  hbox_0_1084__GateII_HBoxData_0,
  hbox_0_1085__GateII_HBoxData_0,
  hbox_0_1086__GateII_HBoxData_0,
  hbox_0_1087__GateII_HBoxData_0,
  hbox_0_1088__GateII_HBoxData_0,
  hbox_0_1089__GateII_HBoxData_0,
  hbox_0_1090__GateII_HBoxData_0,
  hbox_0_1091__GateII_HBoxData_0,
  hbox_0_1092__GateII_HBoxData_0,
  hbox_0_1093__GateII_HBoxData_0,
  hbox_0_1094__GateII_HBoxData_0,
  hbox_0_1095__GateII_HBoxData_0,
  hbox_0_1096__GateII_HBoxData_0,
  hbox_0_1097__GateII_HBoxData_0,
  hbox_0_1098__GateII_HBoxData_0,
  hbox_0_1099__GateII_HBoxData_0,
  hbox_0_1100__GateII_HBoxData_0,
  hbox_0_1101__GateII_HBoxData_0,
  hbox_0_1102__GateII_HBoxData_0,
  hbox_0_1103__GateII_HBoxData_0,
  hbox_0_1104__GateII_HBoxData_0,
  hbox_0_1105__GateII_HBoxData_0,
  hbox_0_1106__GateII_HBoxData_0,
  hbox_0_1107__GateII_HBoxData_0,
  hbox_0_1108__GateII_HBoxData_0,
  hbox_0_1109__GateII_HBoxData_0,
  hbox_0_1110__GateII_HBoxData_0,
  hbox_0_1111__GateII_HBoxData_0,
  hbox_0_1112__GateII_HBoxData_0,
  hbox_0_1113__GateII_HBoxData_0,
  hbox_0_1114__GateII_HBoxData_0,
  hbox_0_1115__GateII_HBoxData_0,
  hbox_0_1116__GateII_HBoxData_0,
  hbox_0_1117__GateII_HBoxData_0,
  hbox_0_1118__GateII_HBoxData_0,
  hbox_0_1119__GateII_HBoxData_0,
  hbox_0_1120__GateII_HBoxData_0,
  hbox_0_1121__GateII_HBoxData_0,
  hbox_0_1122__GateII_HBoxData_0,
  hbox_0_1123__GateII_HBoxData_0,
  hbox_0_1124__GateII_HBoxData_0,
  hbox_0_1125__GateII_HBoxData_0,
  hbox_0_1126__GateII_HBoxData_0,
  hbox_0_1127__GateII_HBoxData_0,
  hbox_0_1128__GateII_HBoxData_0,
  hbox_0_1129__GateII_HBoxData_0,
  hbox_0_1130__GateII_HBoxData_0,
  hbox_0_1131__GateII_HBoxData_0,
  hbox_0_1132__GateII_HBoxData_0,
  hbox_0_1133__GateII_HBoxData_0,
  hbox_0_1134__GateII_HBoxData_0,
  hbox_0_1135__GateII_HBoxData_0,
  hbox_0_1136__GateII_HBoxData_0,
  hbox_0_1137__GateII_HBoxData_0,
  hbox_0_1138__GateII_HBoxData_0,
  hbox_0_1139__GateII_HBoxData_0,
  hbox_0_1140__GateII_HBoxData_0,
  hbox_0_1141__GateII_HBoxData_0,
  hbox_0_1142__GateII_HBoxData_0,
  hbox_0_1143__GateII_HBoxData_0,
  hbox_0_1144__GateII_HBoxData_0,
  hbox_0_1145__GateII_HBoxData_0,
  hbox_0_1146__GateII_HBoxData_0,
  hbox_0_1147__GateII_HBoxData_0,
  hbox_0_1148__GateII_HBoxData_0,
  hbox_0_1149__GateII_HBoxData_0,
  hbox_0_1150__GateII_HBoxData_0,
  hbox_0_1151__GateII_HBoxData_0,
  hbox_0_1152__GateII_HBoxData_0,
  hbox_0_1153__GateII_HBoxData_0,
  hbox_0_1154__GateII_HBoxData_0,
  hbox_0_1155__GateII_HBoxData_0,
  hbox_0_1156__GateII_HBoxData_0,
  hbox_0_1157__GateII_HBoxData_0,
  hbox_0_1158__GateII_HBoxData_0,
  hbox_0_1159__GateII_HBoxData_0,
  hbox_0_1160__GateII_HBoxData_0,
  hbox_0_1161__GateII_HBoxData_0,
  hbox_0_1162__GateII_HBoxData_0,
  hbox_0_1163__GateII_HBoxData_0,
  hbox_0_1164__GateII_HBoxData_0,
  hbox_0_1165__GateII_HBoxData_0,
  hbox_0_1166__GateII_HBoxData_0,
  hbox_0_1167__GateII_HBoxData_0,
  hbox_0_1168__GateII_HBoxData_0,
  hbox_0_1169__GateII_HBoxData_0,
  hbox_0_1170__GateII_HBoxData_0,
  hbox_0_1171__GateII_HBoxData_0,
  hbox_0_1172__GateII_HBoxData_0,
  hbox_0_1173__GateII_HBoxData_0,
  hbox_0_1174__GateII_HBoxData_0,
  hbox_0_1175__GateII_HBoxData_0,
  hbox_0_1176__GateII_HBoxData_0,
  hbox_0_1177__GateII_HBoxData_0,
  hbox_0_1178__GateII_HBoxData_0,
  hbox_0_1179__GateII_HBoxData_0,
  hbox_0_1180__GateII_HBoxData_0,
  hbox_0_1181__GateII_HBoxData_0,
  hbox_0_1182__GateII_HBoxData_0,
  hbox_0_1183__GateII_HBoxData_0,
  hbox_0_1184__GateII_HBoxData_0,
  hbox_0_1185__GateII_HBoxData_0,
  hbox_0_1186__GateII_HBoxData_0,
  hbox_0_1187__GateII_HBoxData_0,
  hbox_0_1188__GateII_HBoxData_0,
  hbox_0_1189__GateII_HBoxData_0,
  hbox_0_1190__GateII_HBoxData_0,
  hbox_0_1191__GateII_HBoxData_0,
  hbox_0_1192__GateII_HBoxData_0,
  hbox_0_1193__GateII_HBoxData_0,
  hbox_0_1194__GateII_HBoxData_0,
  hbox_0_1195__GateII_HBoxData_0,
  hbox_0_1196__GateII_HBoxData_0,
  hbox_0_1197__GateII_HBoxData_0,
  hbox_0_1198__GateII_HBoxData_0,
  hbox_0_1199__GateII_HBoxData_0,
  hbox_0_1200__GateII_HBoxData_0,
  hbox_0_1201__GateII_HBoxData_0,
  hbox_0_1202__GateII_HBoxData_0,
  hbox_0_1203__GateII_HBoxData_0,
  hbox_0_1204__GateII_HBoxData_0,
  hbox_0_1205__GateII_HBoxData_0,
  hbox_0_1206__GateII_HBoxData_0,
  hbox_0_1207__GateII_HBoxData_0,
  hbox_0_1208__GateII_HBoxData_0,
  hbox_0_1209__GateII_HBoxData_0,
  hbox_0_1210__GateII_HBoxData_0,
  hbox_0_1211__GateII_HBoxData_0,
  hbox_0_1212__GateII_HBoxData_0,
  hbox_0_1213__GateII_HBoxData_0,
  hbox_0_1214__GateII_HBoxData_0,
  hbox_0_1215__GateII_HBoxData_0,
  hbox_0_1216__GateII_HBoxData_0,
  hbox_0_1217__GateII_HBoxData_0,
  hbox_0_1218__GateII_HBoxData_0,
  hbox_0_1219__GateII_HBoxData_0,
  hbox_0_1220__GateII_HBoxData_0,
  hbox_0_1221__GateII_HBoxData_0,
  hbox_0_1222__GateII_HBoxData_0,
  hbox_0_1223__GateII_HBoxData_0,
  hbox_0_1224__GateII_HBoxData_0,
  hbox_0_1225__GateII_HBoxData_0,
  hbox_0_1226__GateII_HBoxData_0,
  hbox_0_1227__GateII_HBoxData_0,
  hbox_0_1228__GateII_HBoxData_0,
  hbox_0_1229__GateII_HBoxData_0,
  hbox_0_1230__GateII_HBoxData_0,
  hbox_0_1231__GateII_HBoxData_0,
  hbox_0_1232__GateII_HBoxData_0,
  hbox_0_1233__GateII_HBoxData_0,
  hbox_0_1234__GateII_HBoxData_0,
  hbox_0_1235__GateII_HBoxData_0,
  hbox_0_1236__GateII_HBoxData_0,
  hbox_0_1237__GateII_HBoxData_0,
  hbox_0_1238__GateII_HBoxData_0,
  hbox_0_1239__GateII_HBoxData_0,
  hbox_0_1240__GateII_HBoxData_0,
  hbox_0_1241__GateII_HBoxData_0,
  hbox_0_1242__GateII_HBoxData_0,
  hbox_0_1243__GateII_HBoxData_0,
  hbox_0_1244__GateII_HBoxData_0,
  hbox_0_1245__GateII_HBoxData_0,
  hbox_0_1246__GateII_HBoxData_0,
  hbox_0_1247__GateII_HBoxData_0,
  hbox_0_1248__GateII_HBoxData_0,
  hbox_0_1249__GateII_HBoxData_0,
  hbox_0_1250__GateII_HBoxData_0,
  hbox_0_1251__GateII_HBoxData_0,
  hbox_0_1252__GateII_HBoxData_0,
  hbox_0_1253__GateII_HBoxData_0,
  hbox_0_1254__GateII_HBoxData_0,
  hbox_0_1255__GateII_HBoxData_0,
  hbox_0_1256__GateII_HBoxData_0,
  hbox_0_1257__GateII_HBoxData_0,
  hbox_0_1258__GateII_HBoxData_0,
  hbox_0_1259__GateII_HBoxData_0,
  hbox_0_1260__GateII_HBoxData_0,
  hbox_0_1261__GateII_HBoxData_0,
  hbox_0_1262__GateII_HBoxData_0,
  hbox_0_1263__GateII_HBoxData_0,
  hbox_0_1264__GateII_HBoxData_0,
  hbox_0_1265__GateII_HBoxData_0,
  hbox_0_1266__GateII_HBoxData_0,
  hbox_0_1267__GateII_HBoxData_0,
  hbox_0_1268__GateII_HBoxData_0,
  hbox_0_1269__GateII_HBoxData_0,
  hbox_0_1270__GateII_HBoxData_0,
  hbox_0_1271__GateII_HBoxData_0,
  hbox_0_1272__GateII_HBoxData_0,
  hbox_0_1273__GateII_HBoxData_0,
  hbox_0_1274__GateII_HBoxData_0,
  hbox_0_1275__GateII_HBoxData_0,
  hbox_0_1276__GateII_HBoxData_0,
  hbox_0_1277__GateII_HBoxData_0,
  hbox_0_1278__GateII_HBoxData_0,
  hbox_0_1279__GateII_HBoxData_0,
  hbox_0_1280__GateII_HBoxData_0,
  hbox_0_1281__GateII_HBoxData_0,
  hbox_0_1282__GateII_HBoxData_0,
  hbox_0_1283__GateII_HBoxData_0,
  hbox_0_1284__GateII_HBoxData_0,
  hbox_0_1285__GateII_HBoxData_0,
  hbox_0_1286__GateII_HBoxData_0,
  hbox_0_1287__GateII_HBoxData_0,
  hbox_0_1288__GateII_HBoxData_0,
  hbox_0_1289__GateII_HBoxData_0,
  hbox_0_1290__GateII_HBoxData_0,
  hbox_0_1291__GateII_HBoxData_0,
  hbox_0_1292__GateII_HBoxData_0,
  hbox_0_1293__GateII_HBoxData_0,
  hbox_0_1294__GateII_HBoxData_0,
  hbox_0_1295__GateII_HBoxData_0,
  hbox_0_1296__GateII_HBoxData_0,
  hbox_0_1297__GateII_HBoxData_0,
  hbox_0_1298__GateII_HBoxData_0,
  hbox_0_1299__GateII_HBoxData_0,
  hbox_0_1300__GateII_HBoxData_0,
  hbox_0_1301__GateII_HBoxData_0,
  hbox_0_1302__GateII_HBoxData_0,
  hbox_0_1303__GateII_HBoxData_0,
  hbox_0_1304__GateII_HBoxData_0,
  hbox_0_1305__GateII_HBoxData_0,
  hbox_0_1306__GateII_HBoxData_0,
  hbox_0_1307__GateII_HBoxData_0,
  hbox_0_1308__GateII_HBoxData_0,
  hbox_0_1309__GateII_HBoxData_0,
  hbox_0_1310__GateII_HBoxData_0,
  hbox_0_1311__GateII_HBoxData_0,
  hbox_0_1312__GateII_HBoxData_0,
  hbox_0_1313__GateII_HBoxData_0,
  hbox_0_1314__GateII_HBoxData_0,
  hbox_0_1315__GateII_HBoxData_0,
  hbox_0_1316__GateII_HBoxData_0,
  hbox_0_1317__GateII_HBoxData_0,
  hbox_0_1318__GateII_HBoxData_0,
  hbox_0_1319__GateII_HBoxData_0,
  hbox_0_1320__GateII_HBoxData_0,
  hbox_0_1321__GateII_HBoxData_0,
  hbox_0_1322__GateII_HBoxData_0,
  hbox_0_1323__GateII_HBoxData_0,
  hbox_0_1324__GateII_HBoxData_0,
  hbox_0_1325__GateII_HBoxData_0,
  hbox_0_1326__GateII_HBoxData_0,
  hbox_0_1327__GateII_HBoxData_0,
  hbox_0_1328__GateII_HBoxData_0,
  hbox_0_1329__GateII_HBoxData_0,
  hbox_0_1330__GateII_HBoxData_0,
  hbox_0_1331__GateII_HBoxData_0,
  hbox_0_1332__GateII_HBoxData_0,
  hbox_0_1333__GateII_HBoxData_0,
  hbox_0_1334__GateII_HBoxData_0,
  hbox_0_1335__GateII_HBoxData_0,
  hbox_0_1336__GateII_HBoxData_0,
  hbox_0_1337__GateII_HBoxData_0,
  hbox_0_1338__GateII_HBoxData_0,
  hbox_0_1339__GateII_HBoxData_0,
  hbox_0_1340__GateII_HBoxData_0,
  hbox_0_1341__GateII_HBoxData_0,
  hbox_0_1342__GateII_HBoxData_0,
  hbox_0_1343__GateII_HBoxData_0,
  hbox_0_1344__GateII_HBoxData_0,
  hbox_0_1345__GateII_HBoxData_0,
  hbox_0_1346__GateII_HBoxData_0,
  hbox_0_1347__GateII_HBoxData_0,
  hbox_0_1348__GateII_HBoxData_0,
  hbox_0_1349__GateII_HBoxData_0,
  hbox_0_1350__GateII_HBoxData_0,
  hbox_0_1351__GateII_HBoxData_0,
  hbox_0_1352__GateII_HBoxData_0,
  hbox_0_1353__GateII_HBoxData_0,
  hbox_0_1354__GateII_HBoxData_0,
  hbox_0_1355__GateII_HBoxData_0,
  hbox_0_1356__GateII_HBoxData_0,
  hbox_0_1357__GateII_HBoxData_0,
  hbox_0_1358__GateII_HBoxData_0,
  hbox_0_1359__GateII_HBoxData_0,
  hbox_0_1360__GateII_HBoxData_0,
  hbox_0_1361__GateII_HBoxData_0,
  hbox_0_1362__GateII_HBoxData_0,
  hbox_0_1363__GateII_HBoxData_0,
  hbox_0_1364__GateII_HBoxData_0,
  hbox_0_1365__GateII_HBoxData_0,
  hbox_0_1366__GateII_HBoxData_0,
  hbox_0_1367__GateII_HBoxData_0,
  hbox_0_1368__GateII_HBoxData_0,
  hbox_0_1369__GateII_HBoxData_0,
  hbox_0_1370__GateII_HBoxData_0,
  hbox_0_1371__GateII_HBoxData_0,
  hbox_0_1372__GateII_HBoxData_0,
  hbox_0_1373__GateII_HBoxData_0,
  hbox_0_1374__GateII_HBoxData_0,
  hbox_0_1375__GateII_HBoxData_0,
  hbox_0_1376__GateII_HBoxData_0,
  hbox_0_1377__GateII_HBoxData_0,
  hbox_0_1378__GateII_HBoxData_0,
  hbox_0_1379__GateII_HBoxData_0,
  hbox_0_1380__GateII_HBoxData_0,
  hbox_0_1381__GateII_HBoxData_0,
  hbox_0_1382__GateII_HBoxData_0,
  hbox_0_1383__GateII_HBoxData_0,
  hbox_0_1384__GateII_HBoxData_0,
  hbox_0_1385__GateII_HBoxData_0,
  hbox_0_1386__GateII_HBoxData_0,
  hbox_0_1387__GateII_HBoxData_0,
  hbox_0_1388__GateII_HBoxData_0,
  hbox_0_1389__GateII_HBoxData_0,
  hbox_0_1390__GateII_HBoxData_0,
  hbox_0_1391__GateII_HBoxData_0,
  hbox_0_1392__GateII_HBoxData_0,
  hbox_0_1393__GateII_HBoxData_0,
  hbox_0_1394__GateII_HBoxData_0,
  hbox_0_1395__GateII_HBoxData_0,
  hbox_0_1396__GateII_HBoxData_0,
  hbox_0_1397__GateII_HBoxData_0,
  hbox_0_1398__GateII_HBoxData_0,
  hbox_0_1399__GateII_HBoxData_0,
  hbox_0_1400__GateII_HBoxData_0,
  hbox_0_1401__GateII_HBoxData_0,
  hbox_0_1402__GateII_HBoxData_0,
  hbox_0_1403__GateII_HBoxData_0,
  hbox_0_1404__GateII_HBoxData_0,
  hbox_0_1405__GateII_HBoxData_0,
  hbox_0_1406__GateII_HBoxData_0,
  hbox_0_1407__GateII_HBoxData_0,
  hbox_0_1408__GateII_HBoxData_0,
  hbox_0_1409__GateII_HBoxData_0,
  hbox_0_1410__GateII_HBoxData_0,
  hbox_0_1411__GateII_HBoxData_0,
  hbox_0_1412__GateII_HBoxData_0,
  hbox_0_1413__GateII_HBoxData_0,
  hbox_0_1414__GateII_HBoxData_0,
  hbox_0_1415__GateII_HBoxData_0,
  hbox_0_1416__GateII_HBoxData_0,
  hbox_0_1417__GateII_HBoxData_0,
  hbox_0_1418__GateII_HBoxData_0,
  hbox_0_1419__GateII_HBoxData_0,
  hbox_0_1420__GateII_HBoxData_0,
  hbox_0_1421__GateII_HBoxData_0,
  hbox_0_1422__GateII_HBoxData_0,
  hbox_0_1423__GateII_HBoxData_0,
  hbox_0_1424__GateII_HBoxData_0,
  hbox_0_1425__GateII_HBoxData_0,
  hbox_0_1426__GateII_HBoxData_0,
  hbox_0_1427__GateII_HBoxData_0,
  hbox_0_1428__GateII_HBoxData_0,
  hbox_0_1429__GateII_HBoxData_0,
  hbox_0_1430__GateII_HBoxData_0,
  hbox_0_1431__GateII_HBoxData_0,
  hbox_0_1432__GateII_HBoxData_0,
  hbox_0_1433__GateII_HBoxData_0,
  hbox_0_1434__GateII_HBoxData_0,
  hbox_0_1435__GateII_HBoxData_0,
  hbox_0_1436__GateII_HBoxData_0,
  hbox_0_1437__GateII_HBoxData_0,
  hbox_0_1438__GateII_HBoxData_0,
  hbox_0_1439__GateII_HBoxData_0,
  hbox_0_1440__GateII_HBoxData_0,
  hbox_0_1441__GateII_HBoxData_0,
  hbox_0_1442__GateII_HBoxData_0,
  hbox_0_1443__GateII_HBoxData_0,
  hbox_0_1444__GateII_HBoxData_0,
  hbox_0_1445__GateII_HBoxData_0,
  hbox_0_1446__GateII_HBoxData_0,
  hbox_0_1447__GateII_HBoxData_0,
  hbox_0_1448__GateII_HBoxData_0,
  hbox_0_1449__GateII_HBoxData_0,
  hbox_0_1450__GateII_HBoxData_0,
  hbox_0_1451__GateII_HBoxData_0,
  hbox_0_1452__GateII_HBoxData_0,
  hbox_0_1453__GateII_HBoxData_0,
  hbox_0_1454__GateII_HBoxData_0,
  hbox_0_1455__GateII_HBoxData_0,
  hbox_0_1456__GateII_HBoxData_0,
  hbox_0_1457__GateII_HBoxData_0,
  hbox_0_1458__GateII_HBoxData_0,
  hbox_0_1459__GateII_HBoxData_0,
  hbox_0_1460__GateII_HBoxData_0,
  hbox_0_1461__GateII_HBoxData_0,
  hbox_0_1462__GateII_HBoxData_0,
  hbox_0_1463__GateII_HBoxData_0,
  hbox_0_1464__GateII_HBoxData_0,
  hbox_0_1465__GateII_HBoxData_0,
  hbox_0_1466__GateII_HBoxData_0,
  hbox_0_1467__GateII_HBoxData_0,
  hbox_0_1468__GateII_HBoxData_0,
  hbox_0_1469__GateII_HBoxData_0,
  hbox_0_1470__GateII_HBoxData_0,
  hbox_0_1471__GateII_HBoxData_0,
  hbox_0_1472__GateII_HBoxData_0,
  hbox_0_1473__GateII_HBoxData_0,
  hbox_0_1474__GateII_HBoxData_0,
  hbox_0_1475__GateII_HBoxData_0,
  hbox_0_1476__GateII_HBoxData_0,
  hbox_0_1477__GateII_HBoxData_0,
  hbox_0_1478__GateII_HBoxData_0,
  hbox_0_1479__GateII_HBoxData_0,
  hbox_0_1480__GateII_HBoxData_0,
  hbox_0_1481__GateII_HBoxData_0,
  hbox_0_1482__GateII_HBoxData_0,
  hbox_0_1483__GateII_HBoxData_0,
  hbox_0_1484__GateII_HBoxData_0,
  hbox_0_1485__GateII_HBoxData_0,
  hbox_0_1486__GateII_HBoxData_0,
  hbox_0_1487__GateII_HBoxData_0,
  hbox_0_1488__GateII_HBoxData_0,
  hbox_0_1489__GateII_HBoxData_0,
  hbox_0_1490__GateII_HBoxData_0,
  hbox_0_1491__GateII_HBoxData_0,
  hbox_0_1492__GateII_HBoxData_0,
  hbox_0_1493__GateII_HBoxData_0,
  hbox_0_1494__GateII_HBoxData_0,
  hbox_0_1495__GateII_HBoxData_0,
  hbox_0_1496__GateII_HBoxData_0,
  hbox_0_1497__GateII_HBoxData_0,
  hbox_0_1498__GateII_HBoxData_0,
  hbox_0_1499__GateII_HBoxData_0,
  hbox_0_1500__GateII_HBoxData_0,
  hbox_0_1501__GateII_HBoxData_0,
  hbox_0_1502__GateII_HBoxData_0,
  hbox_0_1503__GateII_HBoxData_0,
  hbox_0_1504__GateII_HBoxData_0,
  hbox_0_1505__GateII_HBoxData_0,
  hbox_0_1506__GateII_HBoxData_0,
  hbox_0_1507__GateII_HBoxData_0,
  hbox_0_1508__GateII_HBoxData_0,
  hbox_0_1509__GateII_HBoxData_0,
  hbox_0_1510__GateII_HBoxData_0,
  hbox_0_1511__GateII_HBoxData_0,
  hbox_0_1512__GateII_HBoxData_0,
  hbox_0_1513__GateII_HBoxData_0,
  hbox_0_1514__GateII_HBoxData_0,
  hbox_0_1515__GateII_HBoxData_0,
  hbox_0_1516__GateII_HBoxData_0,
  hbox_0_1517__GateII_HBoxData_0,
  hbox_0_1518__GateII_HBoxData_0,
  hbox_0_1519__GateII_HBoxData_0,
  hbox_0_1520__GateII_HBoxData_0,
  hbox_0_1521__GateII_HBoxData_0,
  hbox_0_1522__GateII_HBoxData_0,
  hbox_0_1523__GateII_HBoxData_0,
  hbox_0_1524__GateII_HBoxData_0,
  hbox_0_1525__GateII_HBoxData_0,
  hbox_0_1526__GateII_HBoxData_0,
  hbox_0_1527__GateII_HBoxData_0,
  hbox_0_1528__GateII_HBoxData_0,
  hbox_0_1529__GateII_HBoxData_0,
  hbox_0_1530__GateII_HBoxData_0,
  hbox_0_1531__GateII_HBoxData_0,
  hbox_0_1532__GateII_HBoxData_0,
  hbox_0_1533__GateII_HBoxData_0,
  hbox_0_1534__GateII_HBoxData_0,
  hbox_0_1535__GateII_HBoxData_0,
  hbox_0_1536__GateII_HBoxData_0,
  hbox_0_1537__GateII_HBoxData_0,
  hbox_0_1538__GateII_HBoxData_0,
  hbox_0_1539__GateII_HBoxData_0,
  hbox_0_1540__GateII_HBoxData_0,
  hbox_0_1541__GateII_HBoxData_0,
  hbox_0_1542__GateII_HBoxData_0,
  hbox_0_1543__GateII_HBoxData_0,
  hbox_0_1544__GateII_HBoxData_0,
  hbox_0_1545__GateII_HBoxData_0,
  hbox_0_1546__GateII_HBoxData_0,
  hbox_0_1547__GateII_HBoxData_0,
  hbox_0_1548__GateII_HBoxData_0,
  hbox_0_1549__GateII_HBoxData_0,
  hbox_0_1550__GateII_HBoxData_0,
  hbox_0_1551__GateII_HBoxData_0,
  hbox_0_1552__GateII_HBoxData_0,
  hbox_0_1553__GateII_HBoxData_0,
  hbox_0_1554__GateII_HBoxData_0,
  hbox_0_1555__GateII_HBoxData_0,
  hbox_0_1556__GateII_HBoxData_0,
  hbox_0_1557__GateII_HBoxData_0,
  hbox_0_1558__GateII_HBoxData_0,
  hbox_0_1559__GateII_HBoxData_0,
  hbox_0_1560__GateII_HBoxData_0,
  hbox_0_1561__GateII_HBoxData_0,
  hbox_0_1562__GateII_HBoxData_0,
  hbox_0_1563__GateII_HBoxData_0,
  hbox_0_1564__GateII_HBoxData_0,
  hbox_0_1565__GateII_HBoxData_0,
  hbox_0_1566__GateII_HBoxData_0,
  hbox_0_1567__GateII_HBoxData_0,
  hbox_0_1568__GateII_HBoxData_0,
  hbox_0_1569__GateII_HBoxData_0,
  hbox_0_1570__GateII_HBoxData_0,
  hbox_0_1571__GateII_HBoxData_0,
  hbox_0_1572__GateII_HBoxData_0,
  hbox_0_1573__GateII_HBoxData_0,
  hbox_0_1574__GateII_HBoxData_0,
  hbox_0_1575__GateII_HBoxData_0,
  hbox_0_1576__GateII_HBoxData_0,
  hbox_0_1577__GateII_HBoxData_0,
  hbox_0_1578__GateII_HBoxData_0,
  hbox_0_1579__GateII_HBoxData_0,
  hbox_0_1580__GateII_HBoxData_0,
  hbox_0_1581__GateII_HBoxData_0,
  hbox_0_1582__GateII_HBoxData_0,
  hbox_0_1583__GateII_HBoxData_0,
  hbox_0_1584__GateII_HBoxData_0,
  hbox_0_1585__GateII_HBoxData_0,
  hbox_0_1586__GateII_HBoxData_0,
  hbox_0_1587__GateII_HBoxData_0,
  hbox_0_1588__GateII_HBoxData_0,
  hbox_0_1589__GateII_HBoxData_0,
  hbox_0_1590__GateII_HBoxData_0,
  hbox_0_1591__GateII_HBoxData_0,
  hbox_0_1592__GateII_HBoxData_0,
  hbox_0_1593__GateII_HBoxData_0,
  hbox_0_1594__GateII_HBoxData_0,
  hbox_0_1595__GateII_HBoxData_0,
  hbox_0_1596__GateII_HBoxData_0,
  hbox_0_1597__GateII_HBoxData_0,
  hbox_0_1598__GateII_HBoxData_0,
  hbox_0_1599__GateII_HBoxData_0,
  hbox_0_1600__GateII_HBoxData_0,
  hbox_0_1601__GateII_HBoxData_0,
  hbox_0_1602__GateII_HBoxData_0,
  hbox_0_1603__GateII_HBoxData_0,
  hbox_0_1604__GateII_HBoxData_0,
  hbox_0_1605__GateII_HBoxData_0,
  hbox_0_1606__GateII_HBoxData_0,
  hbox_0_1607__GateII_HBoxData_0,
  hbox_0_1608__GateII_HBoxData_0,
  hbox_0_1609__GateII_HBoxData_0,
  hbox_0_1610__GateII_HBoxData_0,
  hbox_0_1611__GateII_HBoxData_0,
  hbox_0_1612__GateII_HBoxData_0,
  hbox_0_1613__GateII_HBoxData_0,
  hbox_0_1614__GateII_HBoxData_0,
  hbox_0_1615__GateII_HBoxData_0,
  hbox_0_1616__GateII_HBoxData_0,
  hbox_0_1617__GateII_HBoxData_0,
  hbox_0_1618__GateII_HBoxData_0,
  hbox_0_1619__GateII_HBoxData_0,
  hbox_0_1620__GateII_HBoxData_0,
  hbox_0_1621__GateII_HBoxData_0,
  hbox_0_1622__GateII_HBoxData_0,
  hbox_0_1623__GateII_HBoxData_0,
  hbox_0_1624__GateII_HBoxData_0,
  hbox_0_1625__GateII_HBoxData_0,
  hbox_0_1626__GateII_HBoxData_0,
  hbox_0_1627__GateII_HBoxData_0,
  hbox_0_1628__GateII_HBoxData_0,
  hbox_0_1629__GateII_HBoxData_0,
  hbox_0_1630__GateII_HBoxData_0,
  hbox_0_1631__GateII_HBoxData_0,
  hbox_0_1632__GateII_HBoxData_0,
  hbox_0_1633__GateII_HBoxData_0,
  hbox_0_1634__GateII_HBoxData_0,
  hbox_0_1635__GateII_HBoxData_0,
  hbox_0_1636__GateII_HBoxData_0,
  hbox_0_1637__GateII_HBoxData_0,
  hbox_0_1638__GateII_HBoxData_0,
  hbox_0_1639__GateII_HBoxData_0,
  hbox_0_1640__GateII_HBoxData_0,
  hbox_0_1641__GateII_HBoxData_0,
  hbox_0_1642__GateII_HBoxData_0,
  hbox_0_1643__GateII_HBoxData_0,
  hbox_0_1644__GateII_HBoxData_0,
  hbox_0_1645__GateII_HBoxData_0,
  hbox_0_1646__GateII_HBoxData_0,
  hbox_0_1647__GateII_HBoxData_0,
  hbox_0_1648__GateII_HBoxData_0,
  hbox_0_1649__GateII_HBoxData_0,
  hbox_0_1650__GateII_HBoxData_0,
  hbox_0_1651__GateII_HBoxData_0,
  hbox_0_1652__GateII_HBoxData_0,
  hbox_0_1653__GateII_HBoxData_0,
  hbox_0_1654__GateII_HBoxData_0,
  hbox_0_1655__GateII_HBoxData_0,
  hbox_0_1656__GateII_HBoxData_0,
  hbox_0_1657__GateII_HBoxData_0,
  hbox_0_1658__GateII_HBoxData_0,
  hbox_0_1659__GateII_HBoxData_0,
  hbox_0_1660__GateII_HBoxData_0,
  hbox_0_1661__GateII_HBoxData_0,
  hbox_0_1662__GateII_HBoxData_0,
  hbox_0_1663__GateII_HBoxData_0,
  hbox_0_1664__GateII_HBoxData_0,
  hbox_0_1665__GateII_HBoxData_0,
  hbox_0_1666__GateII_HBoxData_0,
  hbox_0_1667__GateII_HBoxData_0,
  hbox_0_1668__GateII_HBoxData_0,
  hbox_0_1669__GateII_HBoxData_0,
  hbox_0_1670__GateII_HBoxData_0,
  hbox_0_1671__GateII_HBoxData_0,
  hbox_0_1672__GateII_HBoxData_0,
  hbox_0_1673__GateII_HBoxData_0,
  hbox_0_1674__GateII_HBoxData_0,
  hbox_0_1675__GateII_HBoxData_0,
  hbox_0_1676__GateII_HBoxData_0,
  hbox_0_1677__GateII_HBoxData_0,
  hbox_0_1678__GateII_HBoxData_0,
  hbox_0_1679__GateII_HBoxData_0,
  hbox_0_1680__GateII_HBoxData_0,
  hbox_0_1681__GateII_HBoxData_0,
  hbox_0_1682__GateII_HBoxData_0,
  hbox_0_1683__GateII_HBoxData_0,
  hbox_0_1684__GateII_HBoxData_0,
  hbox_0_1685__GateII_HBoxData_0,
  hbox_0_1686__GateII_HBoxData_0,
  hbox_0_1687__GateII_HBoxData_0,
  hbox_0_1688__GateII_HBoxData_0,
  hbox_0_1689__GateII_HBoxData_0,
  hbox_0_1690__GateII_HBoxData_0,
  hbox_0_1691__GateII_HBoxData_0,
  hbox_0_1692__GateII_HBoxData_0,
  hbox_0_1693__GateII_HBoxData_0,
  hbox_0_1694__GateII_HBoxData_0,
  hbox_0_1695__GateII_HBoxData_0,
  hbox_0_1696__GateII_HBoxData_0,
  hbox_0_1697__GateII_HBoxData_0,
  hbox_0_1698__GateII_HBoxData_0,
  hbox_0_1699__GateII_HBoxData_0,
  hbox_0_1700__GateII_HBoxData_0,
  hbox_0_1701__GateII_HBoxData_0,
  hbox_0_1702__GateII_HBoxData_0,
  hbox_0_1703__GateII_HBoxData_0,
  hbox_0_1704__GateII_HBoxData_0,
  hbox_0_1705__GateII_HBoxData_0,
  hbox_0_1706__GateII_HBoxData_0,
  hbox_0_1707__GateII_HBoxData_0,
  hbox_0_1708__GateII_HBoxData_0,
  hbox_0_1709__GateII_HBoxData_0,
  hbox_0_1710__GateII_HBoxData_0,
  hbox_0_1711__GateII_HBoxData_0,
  hbox_0_1712__GateII_HBoxData_0,
  hbox_0_1713__GateII_HBoxData_0,
  hbox_0_1714__GateII_HBoxData_0,
  hbox_0_1715__GateII_HBoxData_0,
  hbox_0_1716__GateII_HBoxData_0,
  hbox_0_1717__GateII_HBoxData_0,
  hbox_0_1718__GateII_HBoxData_0,
  hbox_0_1719__GateII_HBoxData_0,
  hbox_0_1720__GateII_HBoxData_0,
  hbox_0_1721__GateII_HBoxData_0,
  hbox_0_1722__GateII_HBoxData_0,
  hbox_0_1723__GateII_HBoxData_0,
  hbox_0_1724__GateII_HBoxData_0,
  hbox_0_1725__GateII_HBoxData_0,
  hbox_0_1726__GateII_HBoxData_0,
  hbox_0_1727__GateII_HBoxData_0,
  hbox_0_1728__GateII_HBoxData_0,
  hbox_0_1729__GateII_HBoxData_0,
  hbox_0_1730__GateII_HBoxData_0,
  hbox_0_1731__GateII_HBoxData_0,
  hbox_0_1732__GateII_HBoxData_0,
  hbox_0_1733__GateII_HBoxData_0,
  hbox_0_1734__GateII_HBoxData_0,
  hbox_0_1735__GateII_HBoxData_0,
  hbox_0_1736__GateII_HBoxData_0,
  hbox_0_1737__GateII_HBoxData_0,
  hbox_0_1738__GateII_HBoxData_0,
  hbox_0_1739__GateII_HBoxData_0,
  hbox_0_1740__GateII_HBoxData_0,
  hbox_0_1741__GateII_HBoxData_0,
  hbox_0_1742__GateII_HBoxData_0,
  hbox_0_1743__GateII_HBoxData_0,
  hbox_0_1744__GateII_HBoxData_0,
  hbox_0_1745__GateII_HBoxData_0,
  hbox_0_1746__GateII_HBoxData_0,
  hbox_0_1747__GateII_HBoxData_0,
  hbox_0_1748__GateII_HBoxData_0,
  hbox_0_1749__GateII_HBoxData_0,
  hbox_0_1750__GateII_HBoxData_0,
  hbox_0_1751__GateII_HBoxData_0,
  hbox_0_1752__GateII_HBoxData_0,
  hbox_0_1753__GateII_HBoxData_0,
  hbox_0_1754__GateII_HBoxData_0,
  hbox_0_1755__GateII_HBoxData_0,
  hbox_0_1756__GateII_HBoxData_0,
  hbox_0_1757__GateII_HBoxData_0,
  hbox_0_1758__GateII_HBoxData_0,
  hbox_0_1759__GateII_HBoxData_0,
  hbox_0_1760__GateII_HBoxData_0,
  hbox_0_1761__GateII_HBoxData_0,
  hbox_0_1762__GateII_HBoxData_0,
  hbox_0_1763__GateII_HBoxData_0,
  hbox_0_1764__GateII_HBoxData_0,
  hbox_0_1765__GateII_HBoxData_0,
  hbox_0_1766__GateII_HBoxData_0,
  hbox_0_1767__GateII_HBoxData_0,
  hbox_0_1768__GateII_HBoxData_0,
  hbox_0_1769__GateII_HBoxData_0,
  hbox_0_1770__GateII_HBoxData_0,
  hbox_0_1771__GateII_HBoxData_0,
  hbox_0_1772__GateII_HBoxData_0,
  hbox_0_1773__GateII_HBoxData_0,
  hbox_0_1774__GateII_HBoxData_0,
  hbox_0_1775__GateII_HBoxData_0,
  hbox_0_1776__GateII_HBoxData_0,
  hbox_0_1777__GateII_HBoxData_0,
  hbox_0_1778__GateII_HBoxData_0,
  hbox_0_1779__GateII_HBoxData_0,
  hbox_0_1780__GateII_HBoxData_0,
  hbox_0_1781__GateII_HBoxData_0,
  hbox_0_1782__GateII_HBoxData_0,
  hbox_0_1783__GateII_HBoxData_0,
  hbox_0_1784__GateII_HBoxData_0,
  hbox_0_1785__GateII_HBoxData_0,
  hbox_0_1786__GateII_HBoxData_0,
  hbox_0_1787__GateII_HBoxData_0,
  hbox_0_1788__GateII_HBoxData_0,
  hbox_0_1789__GateII_HBoxData_0,
  hbox_0_1790__GateII_HBoxData_0,
  hbox_0_1791__GateII_HBoxData_0,
  hbox_0_1792__GateII_HBoxData_0,
  hbox_0_1793__GateII_HBoxData_0,
  hbox_0_1794__GateII_HBoxData_0,
  hbox_0_1795__GateII_HBoxData_0,
  hbox_0_1796__GateII_HBoxData_0,
  hbox_0_1797__GateII_HBoxData_0,
  hbox_0_1798__GateII_HBoxData_0,
  hbox_0_1799__GateII_HBoxData_0,
  hbox_0_1800__GateII_HBoxData_0,
  hbox_0_1801__GateII_HBoxData_0,
  hbox_0_1802__GateII_HBoxData_0,
  hbox_0_1803__GateII_HBoxData_0,
  hbox_0_1804__GateII_HBoxData_0,
  hbox_0_1805__GateII_HBoxData_0,
  hbox_0_1806__GateII_HBoxData_0,
  hbox_0_1807__GateII_HBoxData_0,
  hbox_0_1808__GateII_HBoxData_0,
  hbox_0_1809__GateII_HBoxData_0,
  hbox_0_1810__GateII_HBoxData_0,
  hbox_0_1811__GateII_HBoxData_0,
  hbox_0_1812__GateII_HBoxData_0,
  hbox_0_1813__GateII_HBoxData_0,
  hbox_0_1814__GateII_HBoxData_0,
  hbox_0_1815__GateII_HBoxData_0,
  hbox_0_1816__GateII_HBoxData_0,
  hbox_0_1817__GateII_HBoxData_0,
  hbox_0_1818__GateII_HBoxData_0,
  hbox_0_1819__GateII_HBoxData_0,
  hbox_0_1820__GateII_HBoxData_0,
  hbox_0_1821__GateII_HBoxData_0,
  hbox_0_1822__GateII_HBoxData_0,
  hbox_0_1823__GateII_HBoxData_0,
  hbox_0_1824__GateII_HBoxData_0,
  hbox_0_1825__GateII_HBoxData_0,
  hbox_0_1826__GateII_HBoxData_0,
  hbox_0_1827__GateII_HBoxData_0,
  hbox_0_1828__GateII_HBoxData_0,
  hbox_0_1829__GateII_HBoxData_0,
  hbox_0_1830__GateII_HBoxData_0,
  hbox_0_1831__GateII_HBoxData_0,
  hbox_0_1832__GateII_HBoxData_0,
  hbox_0_1833__GateII_HBoxData_0,
  hbox_0_1834__GateII_HBoxData_0,
  hbox_0_1835__GateII_HBoxData_0,
  hbox_0_1836__GateII_HBoxData_0,
  hbox_0_1837__GateII_HBoxData_0,
  hbox_0_1838__GateII_HBoxData_0,
  hbox_0_1839__GateII_HBoxData_0,
  hbox_0_1840__GateII_HBoxData_0,
  hbox_0_1841__GateII_HBoxData_0,
  hbox_0_1842__GateII_HBoxData_0,
  hbox_0_1843__GateII_HBoxData_0,
  hbox_0_1844__GateII_HBoxData_0,
  hbox_0_1845__GateII_HBoxData_0,
  hbox_0_1846__GateII_HBoxData_0,
  hbox_0_1847__GateII_HBoxData_0,
  hbox_0_1848__GateII_HBoxData_0,
  hbox_0_1849__GateII_HBoxData_0,
  hbox_0_1850__GateII_HBoxData_0,
  hbox_0_1851__GateII_HBoxData_0,
  hbox_0_1852__GateII_HBoxData_0,
  hbox_0_1853__GateII_HBoxData_0,
  hbox_0_1854__GateII_HBoxData_0,
  hbox_0_1855__GateII_HBoxData_0,
  hbox_0_1856__GateII_HBoxData_0,
  hbox_0_1857__GateII_HBoxData_0,
  hbox_0_1858__GateII_HBoxData_0,
  hbox_0_1859__GateII_HBoxData_0,
  hbox_0_1860__GateII_HBoxData_0,
  hbox_0_1861__GateII_HBoxData_0,
  hbox_0_1862__GateII_HBoxData_0,
  hbox_0_1863__GateII_HBoxData_0,
  hbox_0_1864__GateII_HBoxData_0,
  hbox_0_1865__GateII_HBoxData_0,
  hbox_0_1866__GateII_HBoxData_0,
  hbox_0_1867__GateII_HBoxData_0,
  hbox_0_1868__GateII_HBoxData_0,
  hbox_0_1869__GateII_HBoxData_0,
  hbox_0_1870__GateII_HBoxData_0,
  hbox_0_1871__GateII_HBoxData_0,
  hbox_0_1872__GateII_HBoxData_0,
  hbox_0_1873__GateII_HBoxData_0,
  hbox_0_1874__GateII_HBoxData_0,
  hbox_0_1875__GateII_HBoxData_0,
  hbox_0_1876__GateII_HBoxData_0,
  hbox_0_1877__GateII_HBoxData_0,
  hbox_0_1878__GateII_HBoxData_0,
  hbox_0_1879__GateII_HBoxData_0,
  hbox_0_1880__GateII_HBoxData_0,
  hbox_0_1881__GateII_HBoxData_0,
  hbox_0_1882__GateII_HBoxData_0,
  hbox_0_1883__GateII_HBoxData_0,
  hbox_0_1884__GateII_HBoxData_0,
  hbox_0_1885__GateII_HBoxData_0,
  hbox_0_1886__GateII_HBoxData_0,
  hbox_0_1887__GateII_HBoxData_0,
  hbox_0_1888__GateII_HBoxData_0,
  hbox_0_1889__GateII_HBoxData_0,
  hbox_0_1890__GateII_HBoxData_0,
  hbox_0_1891__GateII_HBoxData_0,
  hbox_0_1892__GateII_HBoxData_0,
  hbox_0_1893__GateII_HBoxData_0,
  hbox_0_1894__GateII_HBoxData_0,
  hbox_0_1895__GateII_HBoxData_0,
  hbox_0_1896__GateII_HBoxData_0,
  hbox_0_1897__GateII_HBoxData_0,
  hbox_0_1898__GateII_HBoxData_0,
  hbox_0_1899__GateII_HBoxData_0,
  hbox_0_1900__GateII_HBoxData_0,
  hbox_0_1901__GateII_HBoxData_0,
  hbox_0_1902__GateII_HBoxData_0,
  hbox_0_1903__GateII_HBoxData_0,
  hbox_0_1904__GateII_HBoxData_0,
  hbox_0_1905__GateII_HBoxData_0,
  hbox_0_1906__GateII_HBoxData_0,
  hbox_0_1907__GateII_HBoxData_0,
  hbox_0_1908__GateII_HBoxData_0,
  hbox_0_1909__GateII_HBoxData_0,
  hbox_0_1910__GateII_HBoxData_0,
  hbox_0_1911__GateII_HBoxData_0,
  hbox_0_1912__GateII_HBoxData_0,
  hbox_0_1913__GateII_HBoxData_0,
  hbox_0_1914__GateII_HBoxData_0,
  hbox_0_1915__GateII_HBoxData_0,
  hbox_0_1916__GateII_HBoxData_0,
  hbox_0_1917__GateII_HBoxData_0,
  hbox_0_1918__GateII_HBoxData_0,
  hbox_0_1919__GateII_HBoxData_0,
  hbox_0_1920__GateII_HBoxData_0,
  hbox_0_1921__GateII_HBoxData_0,
  hbox_0_1922__GateII_HBoxData_0,
  hbox_0_1923__GateII_HBoxData_0,
  hbox_0_1924__GateII_HBoxData_0,
  hbox_0_1925__GateII_HBoxData_0,
  hbox_0_1926__GateII_HBoxData_0,
  hbox_0_1927__GateII_HBoxData_0,
  hbox_0_1928__GateII_HBoxData_0,
  hbox_0_1929__GateII_HBoxData_0,
  hbox_0_1930__GateII_HBoxData_0,
  hbox_0_1931__GateII_HBoxData_0,
  hbox_0_1932__GateII_HBoxData_0,
  hbox_0_1933__GateII_HBoxData_0,
  hbox_0_1934__GateII_HBoxData_0,
  hbox_0_1935__GateII_HBoxData_0,
  hbox_0_1936__GateII_HBoxData_0,
  hbox_0_1937__GateII_HBoxData_0,
  hbox_0_1938__GateII_HBoxData_0,
  hbox_0_1939__GateII_HBoxData_0,
  hbox_0_1940__GateII_HBoxData_0,
  hbox_0_1941__GateII_HBoxData_0,
  hbox_0_1942__GateII_HBoxData_0,
  hbox_0_1943__GateII_HBoxData_0,
  hbox_0_1944__GateII_HBoxData_0,
  hbox_0_1945__GateII_HBoxData_0,
  hbox_0_1946__GateII_HBoxData_0,
  hbox_0_1947__GateII_HBoxData_0,
  hbox_0_1948__GateII_HBoxData_0,
  hbox_0_1949__GateII_HBoxData_0,
  hbox_0_1950__GateII_HBoxData_0,
  hbox_0_1951__GateII_HBoxData_0,
  hbox_0_1952__GateII_HBoxData_0,
  hbox_0_1953__GateII_HBoxData_0,
  hbox_0_1954__GateII_HBoxData_0,
  hbox_0_1955__GateII_HBoxData_0,
  hbox_0_1956__GateII_HBoxData_0,
  hbox_0_1957__GateII_HBoxData_0,
  hbox_0_1958__GateII_HBoxData_0,
  hbox_0_1959__GateII_HBoxData_0,
  hbox_0_1960__GateII_HBoxData_0,
  hbox_0_1961__GateII_HBoxData_0,
  hbox_0_1962__GateII_HBoxData_0,
  hbox_0_1963__GateII_HBoxData_0,
  hbox_0_1964__GateII_HBoxData_0,
  hbox_0_1965__GateII_HBoxData_0,
  hbox_0_1966__GateII_HBoxData_0,
  hbox_0_1967__GateII_HBoxData_0,
  hbox_0_1968__GateII_HBoxData_0,
  hbox_0_1969__GateII_HBoxData_0,
  hbox_0_1970__GateII_HBoxData_0,
  hbox_0_1971__GateII_HBoxData_0,
  hbox_0_1972__GateII_HBoxData_0,
  hbox_0_1973__GateII_HBoxData_0,
  hbox_0_1974__GateII_HBoxData_0,
  hbox_0_1975__GateII_HBoxData_0,
  hbox_0_1976__GateII_HBoxData_0,
  hbox_0_1977__GateII_HBoxData_0,
  hbox_0_1978__GateII_HBoxData_0,
  hbox_0_1979__GateII_HBoxData_0,
  hbox_0_1980__GateII_HBoxData_0,
  hbox_0_1981__GateII_HBoxData_0,
  hbox_0_1982__GateII_HBoxData_0,
  hbox_0_1983__GateII_HBoxData_0,
  hbox_0_1984__GateII_HBoxData_0,
  hbox_0_1985__GateII_HBoxData_0,
  hbox_0_1986__GateII_HBoxData_0,
  hbox_0_1987__GateII_HBoxData_0,
  hbox_0_1988__GateII_HBoxData_0,
  hbox_0_1989__GateII_HBoxData_0,
  hbox_0_1990__GateII_HBoxData_0,
  hbox_0_1991__GateII_HBoxData_0,
  hbox_0_1992__GateII_HBoxData_0,
  hbox_0_1993__GateII_HBoxData_0,
  hbox_0_1994__GateII_HBoxData_0,
  hbox_0_1995__GateII_HBoxData_0,
  hbox_0_1996__GateII_HBoxData_0,
  hbox_0_1997__GateII_HBoxData_0,
  hbox_0_1998__GateII_HBoxData_0,
  hbox_0_1999__GateII_HBoxData_0,
]

end RHLean.GateII.HBoxDataChunk



end Inline_GateII_HBoxData_0
