import RequestProject.GenericLoops

/-! # Saturation and backward edges around a long loop -/

namespace AneVsAn.Generic

set_option autoImplicit false

variable {n : ℕ} {Λ S : Type} [DecidableEq S] {x : ℕ → Λ} {c : ℕ → S}

/-- If the injective prefix already uses the state budget, every state occurs there. -/
theorem loop_prefix_cover (huaw : IsUAWalk x n c) {a r : ℕ}
    (hl : LoopBlock n c a r) (hc : (walkStates n c).card ≤ a + 1) :
    ∀ t, t ≤ n → ∃ i, i ≤ a ∧ c i = c t := by
  have hr := hl.1
  have hn := hl.2.1
  let P := (Finset.range (a + 1)).image c
  have hsub : P ⊆ walkStates n c :=
    Finset.image_subset_image (Finset.range_mono (by omega))
  have hpcard : P.card = a + 1 := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj he
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      exact loop_prefix_injective huaw hl (by omega) (by omega) he
  have heq : P = walkStates n c :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro t ht
  have hm : c t ∈ P := by
    rw [heq]
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
  have hi' := Finset.mem_range.mp hi
  exact ⟨i, by omega, he⟩

/-- The analogous saturation statement for the injective suffix. -/
theorem loop_suffix_cover (huaw : IsUAWalk x n c) {a r : ℕ}
    (hl : LoopBlock n c a r) (hc : (walkStates n c).card ≤ n - (a + r) + 1) :
    ∀ t, t ≤ n → ∃ i, a + r ≤ i ∧ i ≤ n ∧ c i = c t := by
  have hr := hl.1
  have hn := hl.2.1
  let f : ℕ → S := fun j => c (a + r + j)
  let P := (Finset.range (n - (a + r) + 1)).image f
  have hsub : P ⊆ walkStates n c := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    have hj' := Finset.mem_range.mp hj
    exact Finset.mem_image.mpr ⟨a + r + j, Finset.mem_range.mpr (by omega), rfl⟩
  have hpcard : P.card = n - (a + r) + 1 := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj he
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      have hh := loop_suffix_injective huaw hl
        (show a + r ≤ a + r + i by omega) (show a + r ≤ a + r + j by omega)
        (by omega) (by omega) he
      omega
  have heq : P = walkStates n c :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro t ht
  have hm : c t ∈ P := by
    rw [heq]
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
  have hi' := Finset.mem_range.mp hi
  exact ⟨a + r + i, by omega, by omega, he⟩

omit [DecidableEq S] in
/-- A backward edge between prefix states closes a cycle avoiding the loop. -/
theorem loop_backedge_span (huaw : IsUAWalk x n c) {a r s t θ : ℕ}
    (hl : LoopBlock n c a r) (hst : s < t) (hta : t < a) (hθ : θ < n)
    (hfrom : c θ = c t) (hto : c (θ + 1) = c s) : r < t - s + 1 := by
  have hr := hl.1
  have hn := hl.2.1
  have hleft := segW c (show s ≤ t by omega) (show t ≤ n by omega)
  have hright : Seg n c (c t) (c s) 1 (fun j => θ + j) := by
    have hh := segW c (show θ ≤ θ + 1 by omega) (show θ + 1 ≤ n by omega)
    simpa only [Nat.add_sub_cancel_left, hfrom, hto] using hh
  have hpath := seg_cat hleft hright
  apply loop_min_closed huaw hl (by omega) hpath
  intro j hj he
  by_cases hj' : j < t - s
  · rw [cat_lt hj'] at he
    have hstate : c (s + j) = c a := congrArg Prod.fst he
    have hb := (hl.2.2 (s + j) (by omega)).1 hstate
    omega
  · rw [cat_ge hj', show j - (t - s) = 0 by omega, Nat.add_zero] at he
    have hstate : c t = c a := hfrom.symm.trans (congrArg Prod.fst he)
    have hb := (hl.2.2 t (by omega)).1 hstate
    omega

end AneVsAn.Generic
