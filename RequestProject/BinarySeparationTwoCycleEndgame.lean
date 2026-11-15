import RequestProject.BinarySeparationTwoCycleTools
import RequestProject.BinarySeparationPairing

namespace AneVsAn.BinarySeparation

open AneVsAn.Generic

set_option autoImplicit false

variable {L : ℕ} {S : Type} [DecidableEq S] {u : ℕ → Bool} {c : ℕ → S}

omit [DecidableEq S] in
theorem cross_pairing_increasing {f : ℕ → ℕ}
    (huaw : IsUAWalk (word L u) (3 * L + 1) c) (hp : CrossPairing L c f)
    {i j : ℕ} (hij : i < j) (hj : j < L) (hf : f i < f j) :
    f j + i = f i + j := by
  have hi : i < L := by omega
  have hfi := hp.bounded i hi
  have hfj := hp.bounded j hj
  have h := crossing_equal_lengths huaw hij
    (show j < 2 * L + 2 + f i by omega)
    (show 2 * L + 2 + f i < 2 * L + 2 + f j by omega)
    (show 2 * L + 2 + f j ≤ 3 * L + 1 by omega)
    (hp.paired i hi) (hp.paired j hj) (hp.visits j hj)
  omega

omit [DecidableEq S] in
theorem cross_pairing_not_identity (hL : 6 ≤ L) (hu2 : u 2 = false) (hu3 : u 3 = true)
    {f : ℕ → ℕ} (huaw : IsUAWalk (word L u) (3 * L + 1) c)
    (hp : CrossPairing L c f) : ¬∀ i, i < L → f i = i := by
  intro hid
  have hc2 := hp.paired 2 (by omega)
  have hc3 := hp.paired 3 (by omega)
  rw [hid 2 (by omega)] at hc2
  rw [hid 3 (by omega)] at hc3
  have he := single_label huaw (s := 2) (t := 2 * L + 4) (by omega) (by omega)
    (by simpa only [show 2 * L + 2 + 2 = 2 * L + 4 by omega] using hc2)
    (by simpa only [show 2 * L + 2 + 3 = 2 * L + 4 + 1 by omega] using hc3)
  have hl : word L u 2 = u 2 := word_left (by omega) (by omega) (by omega)
  have hr : word L u (2 * L + 4) = u 3 := by
    have h := word_right (u := u) (t := 3) (by omega) (by omega) (by omega : 2 ≤ L)
    simpa only [show 2 * L + 1 + 3 = 2 * L + 4 by omega] using h
  rw [hl, hr, hu2, hu3] at he
  contradiction

theorem cross_pairing_cycle_constraints (hL : 2 ≤ L)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c) (htwo : ConfinedTwoCycle L c)
    {f : ℕ → ℕ} (hp : CrossPairing L c f) {a b : ℕ}
    (hab : a ≤ b) (hb : b < L) (hf : f a = f b + 1) :
    (b - a + 1) % 2 = 1 ∧ L < 2 * (b - a + 1) := by
  have ha : a < L := by omega
  have hfa := hp.bounded a ha
  have hfb := hp.bounded b hb
  let F := 2 * L + 2 + f b
  have hF : F < 3 * L + 1 := by dsimp [F]; omega
  have hstart : c F = c b := (hp.paired b hb).symm
  have hend : c (F + 1) = c a := by
    have hidx : F + 1 = 2 * L + 2 + f a := by dsimp [F]; omega
    rw [hidx]
    exact (hp.paired a ha).symm
  have hedge : Seg (3 * L + 1) c (c b) (c a) 1 (fun _ => F) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro _ _; exact hF
    · intro j hj; omega
    · intro _; exact hstart
    · intro _; exact hend
    · intro h; omega
  have hpath := seg_cat (segW c hab (show b ≤ 3 * L + 1 by omega)) hedge
  have hzero : edgeCount (word L u) c (b - a + 1)
      (cat (b - a) (fun j => a + j) (fun _ => F))
      (edge (word L u) c (L + 1)) = 0 := by
    apply outer_itinerary_count_zero htwo
    · intro j hj
      exact Nat.le_of_lt (hpath.1 j hj)
    · intro j hj
      by_cases hj' : j < b - a
      · rw [cat_lt hj']
        exact Or.inl (by omega)
      · rw [cat_ge hj']
        exact Or.inr (by dsimp [F]; omega)
  exact outer_closed_constraints hL huaw htwo ha (by omega) (by omega) hpath hzero

theorem confined_two_cycle_impossible (hL : 6 ≤ L) (hmod : L % 4 = 2)
    (hu2 : u 2 = false) (hu3 : u 3 = true)
    (huaw : IsUAWalk (word L u) (3 * L + 1) c) (htwo : ConfinedTwoCycle L c)
    (houter : OuterAtMostTwo L c)
    (hcard : (walkStates (3 * L + 1) c).card ≤ L + 2) : False := by
  obtain ⟨f, hp⟩ := exists_cross_pairing (by omega) htwo houter hcard
    (fun _ _ _ _ hab hb hs hst ht habc hstc =>
      no_simultaneous_side_chords (by omega) huaw htwo hab hb hs hst ht habc hstc)
  apply layered_permutation_impossible (L := L) (f := f) (by omega) hmod
    hp.bounded hp.surjective hp.injective
  · intro i j hij hj hf
    exact cross_pairing_increasing huaw hp hij hj hf
  · exact cross_pairing_not_identity hL hu2 hu3 huaw hp
  · intro a b hab hb hf
    exact cross_pairing_cycle_constraints (by omega) huaw htwo hp hab hb hf
  · intro s hs _
    have hfs := hp.bounded s hs
    exact cross_chord_span_large (by omega) (by omega) huaw htwo hs
      (by omega) (by omega) (hp.paired s hs) (hp.visits s hs)

end AneVsAn.BinarySeparation
