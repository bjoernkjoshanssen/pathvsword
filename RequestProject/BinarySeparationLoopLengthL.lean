import RequestProject.BinarySeparationDefs
import RequestProject.BinarySeparationLoopTools
import RequestProject.BinarySeparationPermutation

/-! # A loop of length `L` forces the seed to be zero -/

namespace AneVsAn.Generic

set_option autoImplicit false

variable {n : ℕ} {Λ S : Type} [DecidableEq S] {x : ℕ → Λ} {c : ℕ → S}

/-- A saturated injective prefix together with one new state covers the walk. -/
theorem loop_prefix_cover_or (huaw : IsUAWalk x n c) {a r : ℕ}
    (hl : LoopBlock n c a r) (hc : (walkStates n c).card ≤ a + 2)
    (z : S) (hz : z ∈ walkStates n c) (hne : ∀ i, i ≤ a → z ≠ c i) :
    ∀ t, t ≤ n → c t = z ∨ ∃ i, i ≤ a ∧ c t = c i := by
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
  have hzP : z ∉ P := by
    intro hzP
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hzP
    exact hne i (by have := Finset.mem_range.mp hi; omega) he.symm
  have hcard : (insert z P).card = a + 2 := by
    rw [Finset.card_insert_of_notMem hzP, hpcard]
  have heq : insert z P = walkStates n c :=
    Finset.eq_of_subset_of_card_le (Finset.insert_subset hz hsub) (by omega)
  intro t ht
  have hm : c t ∈ insert z P := by
    rw [heq]
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
  rcases Finset.mem_insert.mp hm with he | he
  · exact Or.inl he
  · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp he
    exact Or.inr ⟨i, by have := Finset.mem_range.mp hi; omega, he.symm⟩

end AneVsAn.Generic

namespace AneVsAn.BinarySeparation

open AneVsAn.Generic

set_option autoImplicit false

variable {L : ℕ} {S : Type} [DecidableEq S] {u : ℕ → Bool} {c : ℕ → S}

/-- A loop at times `L,…,2L`, with at most `L+2` states, forces the entire seed to zero. -/
theorem length_L_loop_seed_zero (hL : 6 ≤ L)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (hl : LoopBlock (3 * L + 1) c L L)
    (hc : (walkStates (3 * L + 1) c).card ≤ L + 2) :
    ∀ t, 1 ≤ t → t ≤ L - 2 → u t = false := by
  classical
  have htail_no_loop (j : ℕ) (hj : j ≤ L) : c (2 * L + 1 + j) ≠ c L := by
    intro he
    have hb := (hl.2.2 (2 * L + 1 + j) (by omega)).1 he
    omega
  have htail_inj (j k : ℕ) (hj : j ≤ L) (hk : k ≤ L)
      (he : c (2 * L + 1 + j) = c (2 * L + 1 + k)) : j = k := by
    have hh := loop_suffix_injective huaw hl (show L + L ≤ 2 * L + 1 + j by omega)
      (show L + L ≤ 2 * L + 1 + k by omega) (by omega) (by omega) he
    omega
  have hpair_bound {i j : ℕ} (hi : i < L) (hj : j ≤ L)
      (he : c (2 * L + 1 + j) = c i) : i ≤ j := by
    have hh := loop_chord_span huaw hl hi (show L + L < 2 * L + 1 + j by omega)
      (by omega) he.symm
    omega
  have hextra : ∃ k, k ≤ 1 ∧ (k = 1 → c (2 * L + 1) = c 0) ∧
      ∀ i, i ≤ L → c (2 * L + 1 + k) ≠ c i := by
    by_cases h0 : ∀ i, i ≤ L → c (2 * L + 1) ≠ c i
    · exact ⟨0, by omega, by omega, by simpa only [Nat.add_zero] using h0⟩
    · push_neg at h0
      obtain ⟨i, hi, hei⟩ := h0
      have hi' : i < L := by
        have hne : i ≠ L := by intro he; subst i; exact htail_no_loop 0 (by omega) (by simpa using hei)
        omega
      have hi0 : i = 0 := by have := hpair_bound hi' (show 0 ≤ L by omega) (by simpa using hei); omega
      have hfirst : c (2 * L + 1) = c 0 := by simpa only [hi0] using hei
      refine ⟨1, le_rfl, fun _ => hfirst, ?_⟩
      intro j hj he
      have hj' : j < L := by
        have hne : j ≠ L := by intro he'; subst j; exact htail_no_loop 1 (by omega) he
        omega
      have hj1 : j ≤ 1 := hpair_bound hj' (by omega) he
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · have hh := htail_inj 1 0 (by omega) (by omega) (by simpa only [Nat.add_zero] using he.trans hfirst.symm)
        omega
      · have hlabel := single_label huaw (show 0 < 3 * L + 1 by omega)
          (show 2 * L + 1 < 3 * L + 1 by omega) hfirst.symm he.symm
        rw [word_zero, word_right_delimiter (by omega)] at hlabel
        contradiction
  obtain ⟨k, hk, hkfirst, hkextra⟩ := hextra
  let z := c (2 * L + 1 + k)
  have hz : z ∈ walkStates (3 * L + 1) c :=
    Finset.mem_image.mpr ⟨2 * L + 1 + k, Finset.mem_range.mpr (by omega), rfl⟩
  have hcover := loop_prefix_cover_or huaw hl hc z hz hkextra
  have hindices : ∀ s, k ≤ s → s ≤ L - 1 →
      ∃ i, k ≤ i ∧ i ≤ L - 1 ∧ c (2 * L + 1 + (s + 1)) = c i := by
    intro s hks hs
    rcases hcover (2 * L + 1 + (s + 1)) (by omega) with he | ⟨i, hi, he⟩
    · have hh := htail_inj (s + 1) k (by omega) (by omega) he
      omega
    · have hi' : i < L := by
        have hne : i ≠ L := by intro he'; subst i; exact htail_no_loop (s + 1) (by omega) he
        omega
      have hki : k ≤ i := by
        by_contra h
        have hk1 : k = 1 := by omega
        have hi0 : i = 0 := by omega
        have hfirst := hkfirst hk1
        have he' : c (2 * L + 1 + (s + 1)) = c 0 := by simpa only [hi0] using he
        have hh := htail_inj (s + 1) 0 (by omega) (by omega)
          (by simpa only [Nat.add_zero] using he'.trans hfirst.symm)
        omega
      exact ⟨i, hki, by omega, he⟩
  let idx : ℕ → ℕ := fun s => if hs : k ≤ s ∧ s ≤ L - 1 then
    Classical.choose (hindices s hs.1 hs.2) else 0
  have hidx (s : ℕ) (hks : k ≤ s) (hs : s ≤ L - 1) :
      k ≤ idx s ∧ idx s ≤ L - 1 ∧ c (2 * L + 1 + (s + 1)) = c (idx s) := by
    simpa only [idx, dif_pos (show k ≤ s ∧ s ≤ L - 1 from ⟨hks, hs⟩)] using
      Classical.choose_spec (hindices s hks hs)
  have hinc : ∀ s, k ≤ s → s < L - 1 → idx s < idx (s + 1) := by
    intro s hks hs
    have hsi := hidx s hks (by omega)
    have hs1i := hidx (s + 1) (by omega) (by omega)
    have hne : idx s ≠ idx (s + 1) := by
      intro he
      have hcc : c (2 * L + 1 + (s + 1)) = c (2 * L + 1 + (s + 1 + 1)) := by
        rw [hsi.2.2, hs1i.2.2, he]
      have hh := htail_inj (s + 1) (s + 1 + 1) (by omega) (by omega) hcc
      omega
    by_contra hn
    have hd : idx (s + 1) < idx s := by omega
    have hto : c (2 * L + 1 + (s + 1) + 1) = c (idx (s + 1)) := by
      simpa only [Nat.add_assoc] using hs1i.2.2
    have hh := loop_backedge_span huaw hl hd (show idx s < L by omega)
      (show 2 * L + 1 + (s + 1) < 3 * L + 1 by omega) hsi.2.2 hto
    omega
  have hid : ∀ s, k ≤ s → s ≤ L - 1 → idx s = s :=
    increasing_interval_eq idx (hidx k le_rfl (by omega)).1
      (hidx (L - 1) (by omega) le_rfl).2.1 hinc
  have halign (s : ℕ) (hs : 1 ≤ s) (hsL : s ≤ L - 1) :
      c s = c (2 * L + 2 + s) := by
    have hh := (hidx s (by omega) hsL).2.2
    rw [hid s (by omega) hsL] at hh
    convert hh.symm using 1; congr 1; omega
  have hletters (s : ℕ) (hs : 1 ≤ s) (hsL : s ≤ L - 2) :
      word L u s = word L u (2 * L + 2 + s) := by
    apply single_label huaw (by omega) (by omega) (halign s hs (by omega))
    simpa only [Nat.add_assoc] using halign (s + 1) (by omega) (by omega)
  have hend : u (L - 2) = false := by
    have hh := hletters (L - 2) (by omega) le_rfl
    rw [word_left (by omega) le_rfl (by omega),
      show 2 * L + 2 + (L - 2) = 3 * L by omega, word_last (by omega)] at hh
    exact hh
  have hstep (s : ℕ) (hs : 1 ≤ s) (hsL : s < L - 2) : u s = u (s + 1) := by
    have hh := hletters s hs (by omega)
    rw [word_left hs (by omega) (by omega),
      show 2 * L + 2 + s = 2 * L + 1 + (s + 1) by omega,
      word_right (by omega) (by omega) (by omega)] at hh
    exact hh
  have hzeros : ∀ j, j ≤ L - 3 → u (L - 2 - j) = false := by
    intro j
    induction j with
    | zero => intro _; simpa only [Nat.sub_zero] using hend
    | succ j ih =>
      intro hj
      rw [hstep (L - 2 - (j + 1)) (by omega) (by omega),
        show L - 2 - (j + 1) + 1 = L - 2 - j by omega]
      exact ih (by omega)
  intro t ht htL
  have hh := hzeros (L - 2 - t) (by omega)
  rwa [show L - 2 - (L - 2 - t) = t by omega] at hh

/-- A good seed rules out the loop of length `L`; this form is invariant under reversal. -/
theorem no_length_L_loop {B : ℕ} (hL : 6 ≤ L) (hB : B ≤ L - 2) (hg : BGood L B u)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (hl : LoopBlock (3 * L + 1) c L L)
    (hc : (walkStates (3 * L + 1) c).card ≤ L + 2) : False :=
  good_not_all_false (by omega) hB hg (length_L_loop_seed_zero hL huaw hl hc)

end AneVsAn.BinarySeparation
