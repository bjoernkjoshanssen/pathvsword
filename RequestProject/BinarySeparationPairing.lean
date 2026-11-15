import RequestProject.BinarySeparationConfigurations

/-! # Pairing the two outside intervals in the two-cycle case -/

namespace AneVsAn.BinarySeparation

open AneVsAn.Generic

set_option autoImplicit false

variable {L : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

/-- The normalized matching between the two outside intervals. -/
structure CrossPairing (L : ℕ) (c : ℕ → S) (f : ℕ → ℕ) : Prop where
  bounded : ∀ s, s < L → f s < L
  injective : ∀ s, s < L → ∀ t, t < L → f s = f t → s = t
  surjective : ∀ t, t < L → ∃ s, s < L ∧ f s = t
  paired : ∀ s, s < L → c s = c (2 * L + 2 + f s)
  left_injective : ∀ s, s < L → ∀ t, t < L → c s = c t → s = t
  right_injective : ∀ s, s < L → ∀ t, t < L →
    c (2 * L + 2 + s) = c (2 * L + 2 + t) → s = t
  visits : ∀ s, s < L → ∀ t, t ≤ 3 * L + 1 →
    c t = c s → t = s ∨ t = 2 * L + 2 + f s

theorem two_cycle_cluster_card (hL : 1 ≤ L) (htwo : ConfinedTwoCycle L c)
    (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2) : (cluster L c).card = 2 := by
  have hmem0 : c L ∈ cluster L c := by
    apply mem_cluster_iff.mpr
    refine ⟨mem_states (by simp only [times, Finset.mem_range]; omega), ?_⟩
    exact fun t ht he => htwo.2.1 t ht (Or.inl he)
  have hmem1 : c (L + 1) ∈ cluster L c := by
    apply mem_cluster_iff.mpr
    refine ⟨mem_states (by simp only [times, Finset.mem_range]; omega), ?_⟩
    exact fun t ht he => htwo.2.1 t ht (Or.inr he)
  have hlo : 2 ≤ (cluster L c).card := by
    have hh := Finset.card_le_card
      (show ({c L, c (L + 1)} : Finset S) ⊆ cluster L c from by
        intro s hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl <;> assumption)
    simpa [htwo.1] using hh
  have hhi := cluster_card_le houter hcard
  omega

theorem outside_state_twice (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2)
    (hc : (cluster L c).card = 2) {t : ℕ} (ht : t ≤ 3 * L + 1)
    (hout : t < L ∨ 2 * L + 1 < t) : c t ∈ twiceSet L c := by
  have hs : c t ∈ states L c := mem_states (by simp only [times, Finset.mem_range]; omega)
  have hp : 1 ≤ (nvis L c (c t)).card :=
    Finset.card_pos.mpr ⟨t, mem_nvis_iff.mpr ⟨ht, hout, rfl⟩⟩
  have hle := nvis_card_le_two houter (c t)
  have hbudget := cluster_two_budget houter hcard hc
  have hne : (nvis L c (c t)).card ≠ 1 := by
    intro he
    have hm : c t ∈ onceSet L c := Finset.mem_filter.mpr ⟨hs, he⟩
    have hh := Finset.card_pos.mpr ⟨c t, hm⟩
    omega
  exact Finset.mem_filter.mpr ⟨hs, by omega⟩

theorem twice_no_three {s : S} (hs : s ∈ twiceSet L c)
    {a b d : ℕ} (ha : a ∈ nvis L c s) (hb : b ∈ nvis L c s) (hd : d ∈ nvis L c s)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) : False := by
  have hc : (nvis L c s).card = 2 := (Finset.mem_filter.mp hs).2
  have hg := Finset.two_lt_card_iff.mpr ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩
  omega

theorem exists_cross_pairing (hL : 1 ≤ L) (htwo : ConfinedTwoCycle L c)
    (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2)
    (hno : ∀ a b s t, a < b → b < L → 2 * L + 1 < s → s < t →
      t ≤ 3 * L + 1 → c a = c b → c s = c t → False) :
    ∃ f, CrossPairing L c f := by
  classical
  have hc := two_cycle_cluster_card hL htwo houter hcard
  have hTcard : (twiceSet L c).card = L := (cluster_two_budget houter hcard hc).2.2.2.1
  let A := (Finset.range L).image c
  let B := (Finset.range L).image (fun j => c (2 * L + 2 + j))
  have hA : A ⊆ twiceSet L c := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    have hi' := Finset.mem_range.mp hi
    exact outside_state_twice houter hcard hc (by omega) (Or.inl hi')
  have hB : B ⊆ twiceSet L c := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    have hi' := Finset.mem_range.mp hi
    exact outside_state_twice houter hcard hc (by omega) (Or.inr (by omega))
  have hAcov (hi : ∀ s, s < L → ∀ t, t < L → c s = c t → s = t) :
      A = twiceSet L c := by
    apply Finset.eq_of_subset_of_card_le hA
    have hca : A.card = L := by
      rw [Finset.card_image_of_injOn]
      · simp
      · intro s hs t ht he
        exact hi s (Finset.mem_range.mp hs) t (Finset.mem_range.mp ht) he
    omega
  have hBcov (hi : ∀ s, s < L → ∀ t, t < L →
      c (2 * L + 2 + s) = c (2 * L + 2 + t) → s = t) : B = twiceSet L c := by
    apply Finset.eq_of_subset_of_card_le hB
    have hcb : B.card = L := by
      rw [Finset.card_image_of_injOn]
      · simp
      · intro s hs t ht he
        exact hi s (Finset.mem_range.mp hs) t (Finset.mem_range.mp ht) he
    omega
  have hinj : (∀ s, s < L → ∀ t, t < L → c s = c t → s = t) ∧
      (∀ s, s < L → ∀ t, t < L →
        c (2 * L + 2 + s) = c (2 * L + 2 + t) → s = t) := by
    by_cases hiA : ∀ s, s < L → ∀ t, t < L → c s = c t → s = t
    · refine ⟨hiA, ?_⟩
      intro s hs t ht he
      by_contra hst
      have hmem : c (2 * L + 2 + s) ∈ A := by
        rw [hAcov hiA]
        exact outside_state_twice houter hcard hc (by omega) (Or.inr (by omega))
      obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp hmem
      have hi' := Finset.mem_range.mp hi
      have hm := outside_state_twice houter hcard hc (t := i) (by omega) (Or.inl hi')
      apply twice_no_three hm (a := i) (b := 2 * L + 2 + s) (d := 2 * L + 2 + t)
      · exact mem_nvis_iff.mpr ⟨by omega, Or.inl hi', rfl⟩
      · exact mem_nvis_iff.mpr ⟨by omega, Or.inr (by omega), hie.symm⟩
      · exact mem_nvis_iff.mpr ⟨by omega, Or.inr (by omega), he.symm.trans hie.symm⟩
      all_goals omega
    · push_neg at hiA
      obtain ⟨a, ha, b, hb, he, hne⟩ := hiA
      have hileft : ∃ a b, a < b ∧ b < L ∧ c a = c b := by
        rcases lt_or_gt_of_ne hne with h | h
        · exact ⟨a, b, h, hb, he⟩
        · exact ⟨b, a, h, ha, he.symm⟩
      obtain ⟨a, b, hab, hb, heab⟩ := hileft
      have hiB : ∀ s, s < L → ∀ t, t < L →
          c (2 * L + 2 + s) = c (2 * L + 2 + t) → s = t := by
        intro s hs t ht he
        by_contra hst
        rcases lt_or_gt_of_ne hst with hst | hst
        · exact hno a b (2 * L + 2 + s) (2 * L + 2 + t) hab hb
            (by omega) (by omega) (by omega) heab he
        · exact hno a b (2 * L + 2 + t) (2 * L + 2 + s) hab hb
            (by omega) (by omega) (by omega) heab he.symm
      have hmem : c a ∈ B := by
        rw [hBcov hiB]
        exact outside_state_twice houter hcard hc (by omega) (Or.inl (by omega))
      obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hmem
      have hj' := Finset.mem_range.mp hj
      have hm := outside_state_twice houter hcard hc (t := a) (by omega) (Or.inl (by omega))
      exfalso
      apply twice_no_three hm (a := a) (b := b) (d := 2 * L + 2 + j)
      · exact mem_nvis_iff.mpr ⟨by omega, Or.inl (by omega), rfl⟩
      · exact mem_nvis_iff.mpr ⟨by omega, Or.inl hb, heab.symm⟩
      · exact mem_nvis_iff.mpr ⟨by omega, Or.inr (by omega), hje⟩
      all_goals omega
  have hreturn (s : ℕ) (hs : s < L) : ∃ j, j < L ∧ c s = c (2 * L + 2 + j) := by
    have hm : c s ∈ B := by
      rw [hBcov hinj.2]
      exact outside_state_twice houter hcard hc (by omega) (Or.inl hs)
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hm
    exact ⟨j, Finset.mem_range.mp hj, he.symm⟩
  let f : ℕ → ℕ := fun s => if hs : s < L then (hreturn s hs).choose else 0
  have hf (s : ℕ) (hs : s < L) : f s < L ∧ c s = c (2 * L + 2 + f s) := by
    simpa only [f, dif_pos hs] using (hreturn s hs).choose_spec
  refine ⟨f, ⟨fun s hs => (hf s hs).1, ?_, ?_, fun s hs => (hf s hs).2,
    hinj.1, hinj.2, ?_⟩⟩
  · intro s hs t ht he
    exact hinj.1 s hs t ht ((hf s hs).2.trans (by rw [he]; exact (hf t ht).2.symm))
  · intro t ht
    have hm : c (2 * L + 2 + t) ∈ A := by
      rw [hAcov hinj.1]
      exact outside_state_twice houter hcard hc (by omega) (Or.inr (by omega))
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hm
    have hs' := Finset.mem_range.mp hs
    exact ⟨s, hs', hinj.2 (f s) (hf s hs').1 t ht ((hf s hs').2.symm.trans he)⟩
  · intro s hs t ht he
    have hm := outside_state_twice houter hcard hc (t := s) (by omega) (Or.inl hs)
    have hnv : (nvis L c (c s)).card = 2 := (Finset.mem_filter.mp hm).2
    have hrv := rvis_eq_zero_of_twice houter hm
    have hout : t < L ∨ 2 * L + 1 < t := by
      by_contra hn
      have hr : 0 < (rvis L c (c s)).card :=
        Finset.card_pos.mpr ⟨t, mem_rvis_iff.mpr ⟨by omega, by omega, he⟩⟩
      omega
    have hset : nvis L c (c s) = {s, 2 * L + 2 + f s} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact mem_nvis_iff.mpr ⟨by omega, Or.inl hs, rfl⟩
        · exact mem_nvis_iff.mpr ⟨by have := (hf s hs).1; omega,
            Or.inr (by omega), (hf s hs).2.symm⟩
      · simp [hnv, show s ≠ 2 * L + 2 + f s by omega]
    have hmem : t ∈ nvis L c (c s) := mem_nvis_iff.mpr ⟨ht, hout, he⟩
    simpa only [hset, Finset.mem_insert, Finset.mem_singleton] using hmem

end AneVsAn.BinarySeparation
