import RequestProject.BinarySeparationDefs
import RequestProject.BinarySeparationLoopTools

/-! # Excluding a loop occupying the complete central run -/

namespace AneVsAn.BinarySeparation

open AneVsAn.Generic

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {L : ℕ} {S : Type} [DecidableEq S] {u : ℕ → Bool} {c : ℕ → S}

/-- In configuration A0 the paired outer states force a shift by `2L+3`.
The two prescribed seed positions already contradict that shift. -/
theorem no_loop_A0 (hL : 6 ≤ L) (hu1 : u 1 = false) (hu3 : u 3 = true)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2)
    (hl : LoopBlock (3 * L + 1) c L (L + 1)) : False := by
  classical
  let T := Finset.Icc (2 * L + 1) (3 * L + 1)
  let P := T.image c
  have hTinj : Set.InjOn c (↑T : Set ℕ) := by
    intro i hi j hj heq
    have hi' : 2 * L + 1 ≤ i ∧ i ≤ 3 * L + 1 := by simpa [T] using hi
    have hj' : 2 * L + 1 ≤ j ∧ j ≤ 3 * L + 1 := by simpa [T] using hj
    exact loop_suffix_injective huaw hl (by omega) (by omega) hi'.2 hj'.2 heq
  have hPcard : P.card = L + 1 := by
    rw [Finset.card_image_of_injOn hTinj]
    simp only [T, Nat.card_Icc]
    omega
  have hPsub : P ⊆ walkStates (3 * L + 1) c := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    have ht' := Finset.mem_Icc.mp ht
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
  have hlast_not : c (L - 1) ∉ P := by
    intro hmem
    obtain ⟨t, ht, hct⟩ := Finset.mem_image.mp hmem
    have ht' := Finset.mem_Icc.mp ht
    have hchord : c (L - 1) = c t := hct.symm
    have hspan := loop_chord_span huaw hl (show L - 1 < L by omega)
      (show L + (L + 1) < t by
        by_contra hn
        have htval : t = L + (L + 1) := by omega
        have hloop : c t = c L := (hl.2.2 t ht'.2).2 ⟨by omega, by omega⟩
        have hbad := (hl.2.2 (L - 1) (by omega)).1 (hchord.trans hloop)
        omega) ht'.2 hchord
    omega
  have hcover : insert (c (L - 1)) P = walkStates (3 * L + 1) c := by
    apply Finset.eq_of_subset_of_card_le
    · apply Finset.insert_subset
      · exact Finset.mem_image.mpr ⟨L - 1, Finset.mem_range.mpr (by omega), rfl⟩
      · exact hPsub
    · rw [Finset.card_insert_of_notMem hlast_not, hPcard]
      omega
  have hpaired (s : ℕ) (hs : s ≤ L - 2) :
      ∃ t, s + (2 * L + 3) ≤ t ∧ t ≤ 3 * L + 1 ∧ c s = c t := by
    have hmem : c s ∈ insert (c (L - 1)) P := by
      rw [hcover]
      exact Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr (by omega), rfl⟩
    rcases Finset.mem_insert.mp hmem with heq | hmem
    · have hh := loop_prefix_injective huaw hl (by omega : s ≤ L)
        (by omega : L - 1 ≤ L) heq
      omega
    · obtain ⟨t, ht, hct⟩ := Finset.mem_image.mp hmem
      have ht' := Finset.mem_Icc.mp ht
      have hchord : c s = c t := hct.symm
      have hstrict : L + (L + 1) < t := by
        by_contra hn
        have hloop : c t = c L := (hl.2.2 t ht'.2).2 ⟨by omega, by omega⟩
        have hbad := (hl.2.2 s (by omega)).1 (hchord.trans hloop)
        omega
      have hspan := loop_chord_span huaw hl (by omega : s < L) hstrict ht'.2 hchord
      exact ⟨t, by omega, ht'.2, hchord⟩
  have hreverse : ∀ k, k ≤ L - 2 →
      c (L - 2 - k) = c (L - 2 - k + (2 * L + 3)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      obtain ⟨t, htlo, hthi, hct⟩ := hpaired (L - 2 - k) (by omega)
      by_cases hteq : t = L - 2 - k + (2 * L + 3)
      · simpa only [hteq] using hct
      · let j := t - (2 * L + 3)
        have hjlo : L - 2 - k < j := by dsimp [j]; omega
        have hjhi : j ≤ L - 2 := by dsimp [j]; omega
        have hdist : L - 2 - j < k := by omega
        have hprev := ih (L - 2 - j) hdist (by omega)
        rw [show L - 2 - (L - 2 - j) = j by omega,
          show j + (2 * L + 3) = t by dsimp [j]; omega] at hprev
        have heq : c (L - 2 - k) = c j := hct.trans hprev.symm
        have hh := loop_prefix_injective huaw hl (by omega : L - 2 - k ≤ L)
          (by omega : j ≤ L) heq
        omega
  have hshift (s : ℕ) (hs : s ≤ L - 2) : c s = c (s + (2 * L + 3)) := by
    have hh := hreverse (L - 2 - s) (by omega)
    simpa only [show L - 2 - (L - 2 - s) = s by omega] using hh
  have hc1 : c 1 = c (2 * L + 4) := by
    simpa only [show 1 + (2 * L + 3) = 2 * L + 4 by omega] using hshift 1 (by omega)
  have hc2 : c (1 + 1) = c (2 * L + 4 + 1) := by
    simpa only [show 2 + (2 * L + 3) = 2 * L + 4 + 1 by omega] using hshift 2 (by omega)
  have hword := single_label huaw (by omega : 1 < 3 * L + 1)
    (by omega : 2 * L + 4 < 3 * L + 1) hc1 hc2
  rw [word_left (by omega) (by omega) (by omega),
    show 2 * L + 4 = 2 * L + 1 + 3 by omega,
    word_right (by omega) (by omega) (by omega), hu1, hu3] at hword
  cases hword

end AneVsAn.BinarySeparation
