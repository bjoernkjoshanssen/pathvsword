import RequestProject.BinarySeparationDefs
import RequestProject.BinarySeparationLoopTools

/-!
# Excluding the interior long-loop configuration

For infinitude it suffices to use seeds beginning with `00`. This makes the
A2 endgame substantially shorter: the first two indices of the second visit
order force one of three explicit path surgeries.
-/

namespace AneVsAn.BinarySeparation

open AneVsAn.Generic

set_option autoImplicit false

/-- The three visit-order patterns used by the A2 surgeries. -/
def A2Pattern (L : ℕ) (idx : ℕ → ℕ) : Prop :=
  (idx 0 = 0 ∧ ∃ i, i < L ∧ idx i = L ∧ idx (i + 1) = 1) ∨
  (∃ j i, j + 1 < i ∧ i ≤ L ∧ idx j = L - 1 ∧ idx (j + 1) = 0 ∧ idx i = L) ∨
  (idx 0 = 1 ∧ idx (L - 2) = L ∧ idx L = 2)

/-- A finite permutation with only the three possible long descents, whose first
step skips a value, has one of the three surgery patterns. -/
theorem a2_permutation_pattern {L : ℕ} (hL : 6 ≤ L) (idx : ℕ → ℕ)
    (hbound : ∀ j, j ≤ L → idx j ≤ L)
    (hinj : ∀ j k, j ≤ L → k ≤ L → idx j = idx k → j = k)
    (hsurj : ∀ k, k ≤ L → ∃ j, j ≤ L ∧ idx j = k)
    (hlag : ∀ j, j ≤ L → idx j ≤ j + 2)
    (hdesc : ∀ j, j < L → idx (j + 1) < idx j →
      (idx j = L - 1 ∧ idx (j + 1) = 0) ∨
      (idx j = L ∧ idx (j + 1) = 0) ∨ (idx j = L ∧ idx (j + 1) = 1))
    (hinit : (idx 0 = 0 ∧ 2 ≤ idx 1) ∨ (idx 0 = 1 ∧ idx 1 = 3)) :
    A2Pattern L idx := by
  rcases hinit with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · obtain ⟨k, hk, hik⟩ := hsurj 1 (by omega)
    have hk2 : 2 ≤ k := by
      by_contra h
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> omega
    have hp0 : idx (k - 1) ≠ 0 := by
      intro h
      have := hinj (k - 1) 0 (by omega) (by omega) (h.trans h0.symm)
      omega
    have hp1 : idx (k - 1) ≠ 1 := by
      intro h
      have := hinj (k - 1) k (by omega) hk (h.trans hik.symm)
      omega
    have hd := hdesc (k - 1) (by omega) (by rw [show k - 1 + 1 = k by omega, hik]; omega)
    rw [show k - 1 + 1 = k by omega] at hd
    refine Or.inl ⟨h0, k - 1, by omega, ?_, ?_⟩
    · rcases hd with h | h | h <;> omega
    · simpa only [show k - 1 + 1 = k by omega] using hik
  · obtain ⟨k, hk, hik⟩ := hsurj 0 (by omega)
    have hk2 : 2 ≤ k := by
      by_contra h
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> omega
    have hp0 : idx (k - 1) ≠ 0 := by
      intro h
      have := hinj (k - 1) k (by omega) hk (h.trans hik.symm)
      omega
    have hd := hdesc (k - 1) (by omega) (by rw [show k - 1 + 1 = k by omega, hik]; omega)
    rw [show k - 1 + 1 = k by omega] at hd
    have hp : idx (k - 1) = L - 1 ∨ idx (k - 1) = L := by
      rcases hd with h | h | h <;> omega
    rcases hp with hp | hp
    · obtain ⟨i, hi, hii⟩ := hsurj L le_rfl
      have hki : k < i := by
        by_contra h
        have hi' : i < k - 1 := by
          have hne0 : i ≠ k := by intro h; subst i; omega
          have hne1 : i ≠ k - 1 := by intro h; subst i; omega
          omega
        have hnext : idx (i + 1) < idx i := by
          have hb := hbound (i + 1) (by omega)
          have hne : idx (i + 1) ≠ idx i := by
            intro he
            have := hinj (i + 1) i (by omega) hi he
            omega
          omega
        have hd' := hdesc i (by omega) hnext
        have hh : idx (i + 1) = 0 ∨ idx (i + 1) = 1 := by
          rcases hd' with h | h | h <;> omega
        rcases hh with hh | hh
        · have := hinj (i + 1) k (by omega) hk (hh.trans hik.symm)
          omega
        · have := hinj (i + 1) 0 (by omega) (by omega) (hh.trans h0.symm)
          omega
      exact Or.inr (Or.inl ⟨k - 1, i, by omega, hi, hp,
        by simpa only [show k - 1 + 1 = k by omega] using hik, hii⟩)
    · obtain ⟨j, hj, hij⟩ := hsurj 2 (by omega)
      have hj2 : 2 ≤ j := by
        by_contra h
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> omega
      have hp2 : idx (j - 1) ≠ 2 := by
        intro h
        have := hinj (j - 1) j (by omega) hj (h.trans hij.symm)
        omega
      have hp1 : idx (j - 1) ≠ 1 := by
        intro h
        have := hinj (j - 1) 0 (by omega) (by omega) (h.trans h0.symm)
        omega
      have hpj : idx (j - 1) = 0 := by
        by_contra h
        have hlt : idx (j - 1 + 1) < idx (j - 1) := by
          rw [show j - 1 + 1 = j by omega, hij]
          omega
        have hd' := hdesc (j - 1) (by omega) hlt
        rw [show j - 1 + 1 = j by omega, hij] at hd'
        rcases hd' with h | h | h <;> omega
      have hjk : j - 1 = k := hinj (j - 1) k (by omega) hk (hpj.trans hik.symm)
      have hlag' := hlag (k - 1) (by omega)
      have hkL : k = L - 1 := by omega
      have hjL : j = L := by omega
      refine Or.inr (Or.inr ⟨h0, ?_, ?_⟩)
      · simpa only [hkL, show L - 1 - 1 = L - 2 by omega] using hp
      · simpa only [hjL] using hij

section Walk

variable {L : ℕ} {S : Type} [DecidableEq S] {u : ℕ → Bool} {c : ℕ → S}

omit [DecidableEq S] in
/-- The surgery for a second-pass descent from `L` to `1`, starting at `0`. -/
theorem a2_surgery_L_one (hL : 6 ≤ L)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (hl : LoopBlock (3 * L + 1) c (L + 1) (L - 1))
    {i : ℕ} (hi : i < L) (hfirst : c (2 * L + 1) = c 0)
    (hfrom : c (2 * L + 1 + i) = c L)
    (hto : c (2 * L + 1 + (i + 1)) = c 1) : False := by
  have hlast : c (2 * L) = c (L + 1) := (hl.2.2 (2 * L) (by omega)).2 ⟨by omega, by omega⟩
  have hp0 := segW c (show 2 * L + 1 ≤ 2 * L + 1 + i by omega) (show 2 * L + 1 + i ≤ 3 * L + 1 by omega)
  rw [hfirst, hfrom] at hp0
  have hin := segW c (show L ≤ L + 1 by omega) (show L + 1 ≤ 3 * L + 1 by omega)
  have hpre := seg_cat hp0 hin
  have hout := segW c (show 2 * L ≤ 2 * L + 1 by omega) (show 2 * L + 1 ≤ 3 * L + 1 by omega)
  rw [hlast, hfirst] at hout
  have h01 := segW c (show 0 ≤ 1 by omega) (show 1 ≤ 3 * L + 1 by omega)
  have hsuffix := segW c (show 2 * L + 1 + (i + 1) ≤ 3 * L + 1 by omega) (show 3 * L + 1 ≤ 3 * L + 1 by rfl)
  rw [hto] at hsuffix
  have hpost := seg_cat (seg_cat hout h01) hsuffix
  have hh := loop_insert_bound huaw hl hpre hpost (m := 2 * L - 1) (by omega)
  omega

omit [DecidableEq S] in
/-- The surgery for a descent from `L-1` to `0` preceding the visit to `L`. -/
theorem a2_surgery_pred_zero (hL : 6 ≤ L)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (hl : LoopBlock (3 * L + 1) c (L + 1) (L - 1))
    {j i : ℕ} (hji : j + 1 < i) (hi : i ≤ L)
    (hfrom : c (2 * L + 1 + j) = c (L - 1))
    (hto : c (2 * L + 1 + (j + 1)) = c 0)
    (hLpos : c (2 * L + 1 + i) = c L) : False := by
  have hlast : c (2 * L) = c (L + 1) := (hl.2.2 (2 * L) (by omega)).2 ⟨by omega, by omega⟩
  have hp0 := segW c (show 2 * L + 1 + (j + 1) ≤ 2 * L + 1 + i by omega)
    (show 2 * L + 1 + i ≤ 3 * L + 1 by omega)
  rw [hto, hLpos] at hp0
  have hin := segW c (show L ≤ L + 1 by omega) (show L + 1 ≤ 3 * L + 1 by omega)
  have hpre := seg_cat hp0 hin
  have hout := segW c (show 2 * L ≤ 2 * L + 1 by omega) (show 2 * L + 1 ≤ 3 * L + 1 by omega)
  rw [hlast] at hout
  have hmid := segW c (show 2 * L + 1 ≤ 2 * L + 1 + j by omega)
    (show 2 * L + 1 + j ≤ 3 * L + 1 by omega)
  rw [hfrom] at hmid
  have hback := segW c (show L - 1 ≤ L by omega) (show L ≤ 3 * L + 1 by omega)
  have hsuffix := segW c (show 2 * L + 1 + i ≤ 3 * L + 1 by omega)
    (show 3 * L + 1 ≤ 3 * L + 1 by rfl)
  rw [hLpos] at hsuffix
  have hpost := seg_cat (seg_cat (seg_cat hout hmid) hback) hsuffix
  have hh := loop_insert_bound huaw hl hpre hpost (m := 2 * L - 1) (by omega)
  omega

omit [DecidableEq S] in
/-- The surgery for the exceptional tail `L,0,2`, with first index `1`. -/
theorem a2_surgery_tail_two (hL : 6 ≤ L)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (hl : LoopBlock (3 * L + 1) c (L + 1) (L - 1))
    (hfirst : c (2 * L + 1) = c 1)
    (hLpos : c (2 * L + 1 + (L - 2)) = c L)
    (hfinal : c (3 * L + 1) = c 2) : False := by
  have hlast : c (2 * L) = c (L + 1) := (hl.2.2 (2 * L) (by omega)).2 ⟨by omega, by omega⟩
  have h01 := segW c (show 0 ≤ 1 by omega) (show 1 ≤ 3 * L + 1 by omega)
  have hp0 := segW c (show 2 * L + 1 ≤ 2 * L + 1 + (L - 2) by omega)
    (show 2 * L + 1 + (L - 2) ≤ 3 * L + 1 by omega)
  rw [hfirst, hLpos] at hp0
  have hin := segW c (show L ≤ L + 1 by omega) (show L + 1 ≤ 3 * L + 1 by omega)
  have hpre := seg_cat (seg_cat h01 hp0) hin
  have hout := segW c (show 2 * L ≤ 2 * L + 1 by omega) (show 2 * L + 1 ≤ 3 * L + 1 by omega)
  rw [hlast, hfirst] at hout
  have h12 := segW c (show 1 ≤ 2 by omega) (show 2 ≤ 3 * L + 1 by omega)
  rw [← hfinal] at h12
  have hpost := seg_cat hout h12
  have hh := loop_insert_bound huaw hl hpre hpost (m := 2 * L - 1) (by omega)
  omega

/-- A seed beginning with `00` rules out the interior loop of length `L-1`.
No goodness or parity assumption is needed for this configuration. -/
theorem no_a2_loop (hL : 6 ≤ L)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (hl : LoopBlock (3 * L + 1) c (L + 1) (L - 1))
    (hc : (walkStates (3 * L + 1) c).card ≤ L + 2)
    (hu1 : u 1 = false) (hu2 : u 2 = false) : False := by
  classical
  have hprefix : ∀ j, j ≤ L → ∃ i, i ≤ L ∧ c (2 * L + 1 + j) = c i := by
    intro j hj
    obtain ⟨i, hi, he⟩ := loop_prefix_cover huaw hl (by omega) (2 * L + 1 + j) (by omega)
    have hi' : i ≤ L := by
      by_contra h
      have hei : i = L + 1 := by omega
      have hb := (hl.2.2 (2 * L + 1 + j) (by omega)).1 (he.symm.trans (by rw [hei]))
      omega
    exact ⟨i, hi', he.symm⟩
  let idx : ℕ → ℕ := fun j => if hj : j ≤ L then Classical.choose (hprefix j hj) else 0
  have hidx (j : ℕ) (hj : j ≤ L) : idx j ≤ L ∧ c (2 * L + 1 + j) = c (idx j) := by
    simpa only [idx, dif_pos hj] using Classical.choose_spec (hprefix j hj)
  have hinj (j k : ℕ) (hj : j ≤ L) (hk : k ≤ L) (he : idx j = idx k) : j = k := by
    have hcc : c (2 * L + 1 + j) = c (2 * L + 1 + k) := by
      rw [(hidx j hj).2, (hidx k hk).2, he]
    have hh := loop_suffix_injective huaw hl
      (show L + 1 + (L - 1) ≤ 2 * L + 1 + j by omega)
      (show L + 1 + (L - 1) ≤ 2 * L + 1 + k by omega) (by omega) (by omega) hcc
    omega
  have hsurj (k : ℕ) (hk : k ≤ L) : ∃ j, j ≤ L ∧ idx j = k := by
    obtain ⟨i, hi, hin, he⟩ := loop_suffix_cover huaw hl (by omega) k (by omega)
    have hi' : 2 * L + 1 ≤ i := by
      by_contra h
      have hiLoop : c i = c (L + 1) := (hl.2.2 i hin).2 ⟨by omega, by omega⟩
      have hb := (hl.2.2 k (by omega)).1 (he.symm.trans hiLoop)
      omega
    have hj : i - (2 * L + 1) ≤ L := by omega
    have hstate := (hidx (i - (2 * L + 1)) hj).2
    rw [show 2 * L + 1 + (i - (2 * L + 1)) = i by omega] at hstate
    refine ⟨i - (2 * L + 1), hj, ?_⟩
    exact loop_prefix_injective huaw hl (by have := (hidx _ hj).1; omega) (by omega)
      (hstate.symm.trans he)
  have hlag (j : ℕ) (hj : j ≤ L) : idx j ≤ j + 2 := by
    have hij := (hidx j hj).1
    have hh := loop_chord_span huaw hl (show idx j < L + 1 by omega)
      (show L + 1 + (L - 1) < 2 * L + 1 + j by omega) (by omega) (hidx j hj).2.symm
    omega
  have hdesc (j : ℕ) (hj : j < L) (hd : idx (j + 1) < idx j) :
      (idx j = L - 1 ∧ idx (j + 1) = 0) ∨
      (idx j = L ∧ idx (j + 1) = 0) ∨ (idx j = L ∧ idx (j + 1) = 1) := by
    have hjb := (hidx j (by omega)).1
    have hjb' := (hidx (j + 1) (by omega)).1
    have hto : c (2 * L + 1 + j + 1) = c (idx (j + 1)) := by
      simpa only [Nat.add_assoc] using (hidx (j + 1) (by omega)).2
    have hh := loop_backedge_span huaw hl hd (show idx j < L + 1 by omega)
      (show 2 * L + 1 + j < 3 * L + 1 by omega) (hidx j (by omega)).2 hto
    omega
  have hsmall : ∀ s, s ≤ 2 → word L u s = false := by
    intro s hs
    rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl
    · exact word_zero L u
    · rw [word_left (by omega) (by omega) (by omega)]
      exact hu1
    · rw [word_left (by omega) (by omega) (by omega)]
      exact hu2
  have h0b := hlag 0 (by omega)
  have h1b := hlag 1 (by omega)
  have h01ne : idx 0 ≠ idx 1 := by
    intro he
    have := hinj 0 1 (by omega) (by omega) he
    omega
  have h01lt : idx 0 < idx 1 := by
    by_contra h
    have hd := hdesc 0 (by omega) (show idx 1 < idx 0 by omega)
    simp only [Nat.zero_add] at hd
    rcases hd with h | h | h <;> omega
  have hskip : idx 1 ≠ idx 0 + 1 := by
    intro he
    have hfrom : c (idx 0) = c (2 * L + 1) := by
      simpa only [Nat.add_zero] using (hidx 0 (by omega)).2.symm
    have hto : c (idx 0 + 1) = c (2 * L + 1 + 1) := by
      rw [← he]
      exact (hidx 1 (by omega)).2.symm
    have heq := single_label huaw (show idx 0 < 3 * L + 1 by omega) (by omega) hfrom hto
    rw [hsmall _ (by omega), word_right_delimiter (by omega)] at heq
    contradiction
  have hinit : (idx 0 = 0 ∧ 2 ≤ idx 1) ∨ (idx 0 = 1 ∧ idx 1 = 3) := by omega
  have hpat := a2_permutation_pattern hL idx (fun j hj => (hidx j hj).1) hinj hsurj hlag hdesc hinit
  rcases hpat with ⟨hfirst, i, hi, hfrom, hto⟩ | ⟨j, i, hji, hi, hfrom, hto, hLpos⟩ | ⟨hfirst, hLpos, hfinal⟩
  · apply a2_surgery_L_one hL huaw hl hi
    · simpa only [Nat.add_zero, hfirst] using (hidx 0 (by omega)).2
    · simpa only [hfrom] using (hidx i (by omega)).2
    · simpa only [hto] using (hidx (i + 1) (by omega)).2
  · apply a2_surgery_pred_zero hL huaw hl hji hi
    · simpa only [hfrom] using (hidx j (by omega)).2
    · simpa only [hto] using (hidx (j + 1) (by omega)).2
    · simpa only [hLpos] using (hidx i hi).2
  · apply a2_surgery_tail_two hL huaw hl
    · simpa only [Nat.add_zero, hfirst] using (hidx 0 (by omega)).2
    · simpa only [hLpos] using (hidx (L - 2) (by omega)).2
    · simpa only [show 2 * L + 1 + L = 3 * L + 1 by omega, hfinal] using (hidx L le_rfl).2

end Walk
end AneVsAn.BinarySeparation
