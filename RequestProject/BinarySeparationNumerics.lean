import RequestProject.ProofImports

/-!
# An explicit cofinal choice of parameters for binary separation

Only infinitude is needed. The generous choice `L = 2^m + 2`, `B = 64*m + 8`,
for `m ≥ 64`, makes both the walk inequality and a uniform finite union bound
straightforward. The larger budget avoids estimating a geometric series of
period-dependent probabilities.
-/

namespace AneVsAn.BinarySeparation

set_option autoImplicit false

def familyLength (m : ℕ) : ℕ := 2 ^ m + 2

def goodnessBudget (m : ℕ) : ℕ := 64 * m + 8

theorem cube_succ_le_double {m : ℕ} (hm : 4 ≤ m) :
    (m + 1) ^ 3 ≤ 2 * m ^ 3 := by
  have hs : 4 * m ≤ m ^ 2 := by nlinarith [Nat.mul_le_mul_left m hm]
  have hc : 4 * m ^ 2 ≤ m ^ 3 := by nlinarith [Nat.mul_le_mul_left (m * m) hm]
  nlinarith

theorem exp_dominates_cubic {m : ℕ} (hm : 64 ≤ m) :
    1048576 * m ^ 3 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hc := cube_succ_le_double (by omega : 4 ≤ m)
    calc
      1048576 * (m + 1) ^ 3 ≤ 1048576 * (2 * m ^ 3) := Nat.mul_le_mul_left _ hc
      _ = 2 * (1048576 * m ^ 3) := by ring
      _ < 2 * 2 ^ m := Nat.mul_lt_mul_of_pos_left ih (by decide)
      _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

theorem budget_cube_lt_exp {m : ℕ} (hm : 64 ≤ m) :
    goodnessBudget m ^ 3 < 2 ^ m := by
  have hb : goodnessBudget m ≤ 65 * m := by unfold goodnessBudget; omega
  calc
    goodnessBudget m ^ 3 ≤ (65 * m) ^ 3 := Nat.pow_le_pow_left hb 3
    _ = 274625 * m ^ 3 := by ring
    _ ≤ 1048576 * m ^ 3 := Nat.mul_le_mul_right _ (by decide)
    _ < 2 ^ m := exp_dominates_cubic hm

theorem fourth_succ_le_double {m : ℕ} (hm : 8 ≤ m) :
    (m + 1) ^ 4 ≤ 2 * m ^ 4 := by
  have hs : 8 * m ≤ m ^ 2 := by nlinarith [Nat.mul_le_mul_left m hm]
  have hc : 8 * m ^ 2 ≤ m ^ 3 := by nlinarith [Nat.mul_le_mul_left (m * m) hm]
  have hq : 8 * m ^ 3 ≤ m ^ 4 := by nlinarith [Nat.mul_le_mul_left (m ^ 3) hm]
  nlinarith

theorem exp_dominates_fourth {m : ℕ} (hm : 64 ≤ m) :
    33554432 * m ^ 4 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hc := fourth_succ_le_double (by omega : 8 ≤ m)
    calc
      33554432 * (m + 1) ^ 4 ≤ 33554432 * (2 * m ^ 4) := Nat.mul_le_mul_left _ hc
      _ = 2 * (33554432 * m ^ 4) := by ring
      _ < 2 * 2 ^ m := Nat.mul_lt_mul_of_pos_left ih (by decide)
      _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

theorem budget_fourth_lt_exp {m : ℕ} (hm : 64 ≤ m) :
    goodnessBudget m ^ 4 < 2 ^ m := by
  have hb : goodnessBudget m ≤ 65 * m := by unfold goodnessBudget; omega
  calc
    goodnessBudget m ^ 4 ≤ (65 * m) ^ 4 := Nat.pow_le_pow_left hb 4
    _ = 17850625 * m ^ 4 := by ring
    _ ≤ 33554432 * m ^ 4 := Nat.mul_le_mul_right _ (by decide)
    _ < 2 ^ m := exp_dominates_fourth hm

theorem familyLength_ge_six {m : ℕ} (hm : 64 ≤ m) : 6 ≤ familyLength m := by
  have he := budget_cube_lt_exp hm
  have hb : 8 ≤ goodnessBudget m := by unfold goodnessBudget; omega
  have hpow := Nat.pow_le_pow_left hb 3
  unfold familyLength
  norm_num at hpow
  omega

theorem budget_ge_three (m : ℕ) : 3 ≤ goodnessBudget m := by
  unfold goodnessBudget
  omega

theorem budget_le_length_sub_two {m : ℕ} (hm : 64 ≤ m) :
    goodnessBudget m ≤ familyLength m - 2 := by
  have he := budget_cube_lt_exp hm
  have hb := budget_ge_three m
  have hp : goodnessBudget m ≤ goodnessBudget m ^ 3 := Nat.le_self_pow (by decide) _
  unfold familyLength
  omega

theorem familyLength_mod_four {m : ℕ} (hm : 64 ≤ m) : familyLength m % 4 = 2 := by
  unfold familyLength
  conv_lhs => rw [show m = (m - 2) + 2 by omega, pow_add]
  simp [Nat.add_mod]

theorem walk_numeric_bound {m : ℕ} (hm : 64 ≤ m) :
    (goodnessBudget m - 1) *
      (8 + (goodnessBudget m - 2) * (goodnessBudget m - 3)) <
      4 * (familyLength m + 2) := by
  have hb := budget_ge_three m
  have h1 : goodnessBudget m - 1 ≤ goodnessBudget m := Nat.sub_le _ _
  have h2 : 8 + (goodnessBudget m - 2) * (goodnessBudget m - 3) ≤
      goodnessBudget m ^ 2 := by
    have hsub2 := Nat.sub_add_cancel (by omega : 2 ≤ goodnessBudget m)
    have hsub3 := Nat.sub_add_cancel hb
    nlinarith
  have hmul := Nat.mul_le_mul h1 h2
  have he := budget_cube_lt_exp hm
  unfold familyLength
  nlinarith

/-- A deliberately weaker surplus estimate in the walk proof is also sufficient
for this choice of parameters. -/
theorem walk_numeric_bound_loose {m : ℕ} (hm : 64 ≤ m) :
    2 * (goodnessBudget m - 1) * (goodnessBudget m ^ 3 + 4) <
      4 * (familyLength m + 2) := by
  have hb := budget_ge_three m
  have he := budget_fourth_lt_exp hm
  have hcube : 4 ≤ goodnessBudget m ^ 3 := by
    have h := Nat.pow_le_pow_left hb 3
    norm_num at h
    omega
  have hpow : 4 * goodnessBudget m ≤ goodnessBudget m ^ 4 := by
    calc
      _ ≤ goodnessBudget m ^ 3 * goodnessBudget m :=
        Nat.mul_le_mul_right _ hcube
      _ = _ := by ring
  calc
    _ ≤ 2 * goodnessBudget m * (goodnessBudget m ^ 3 + 4) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    _ = 2 * goodnessBudget m ^ 4 + 8 * goodnessBudget m := by ring
    _ ≤ 4 * goodnessBudget m ^ 4 := by omega
    _ < 4 * (familyLength m + 2) := by unfold familyLength; omega

theorem seed_length_ge_rank {m : ℕ} (hm : 64 ≤ m) :
    8 * m ≤ familyLength m - 2 := by
  have hb := budget_le_length_sub_two hm
  unfold goodnessBudget at hb
  omega

theorem matching_rank_budget (m : ℕ) :
    8 * (8 * m) ≤ goodnessBudget m - 3 := by
  unfold goodnessBudget
  omega

theorem window_count_lt_pow_rank_sub_three {m : ℕ} (hm : 64 ≤ m) :
    (3 * familyLength m + 2) ^ 3 < 2 ^ (8 * m - 3) := by
  have he := budget_cube_lt_exp hm
  have hb : 8 ≤ goodnessBudget m := by unfold goodnessBudget; omega
  have hp : 8 ≤ 2 ^ m := by
    have h := Nat.le_self_pow (by decide : 3 ≠ 0) (goodnessBudget m)
    omega
  have hn : 3 * familyLength m + 2 ≤ 4 * 2 ^ m := by
    unfold familyLength
    omega
  have hs := Nat.pow_le_pow_left hn 3
  have hid : (4 * 2 ^ m) ^ 3 = 2 ^ (3 * m + 6) := by
    rw [pow_add, Nat.mul_comm 3 m, pow_mul]
    ring
  have hstrict : 2 ^ (3 * m + 6) < 2 ^ (8 * m - 3) := by
    exact Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega)
  omega

theorem window_count_lt_pow_rank {m : ℕ} (hm : 64 ≤ m) :
    (3 * familyLength m + 2) ^ 3 < 2 ^ (8 * m) := by
  have h := window_count_lt_pow_rank_sub_three hm
  have hp : 2 ^ (8 * m - 3) ≤ 2 ^ (8 * m) :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  omega

theorem familyLength_strictMono : StrictMono familyLength := by
  intro a b hab
  unfold familyLength
  have hp := Nat.pow_lt_pow_right (by omega : 1 < 2) hab
  omega

end AneVsAn.BinarySeparation
