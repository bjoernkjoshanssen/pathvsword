import RequestProject.BinarySeparationUpper
import RequestProject.BinarySeparationOuter
import RequestProject.BinarySeparationConfigurations
import RequestProject.BinarySeparationLoopA0
import RequestProject.BinarySeparationLoopA2
import RequestProject.BinarySeparationLoopLengthL
import RequestProject.BinarySeparationTwoCycleEndgame
import RequestProject.BinarySeparationReversal

/-!
# Separation for good binary seeds beginning with 001

This theorem uses a deliberately generous repetition bound. It is sufficient
for infinitude and makes the outer-state counting argument uniform over all
periods. The only residue restriction used in the endgame is `L % 4 = 2`.
-/

namespace AneVsAn.BinarySeparation

open AneVsAn.Generic

set_option autoImplicit false

variable {L B : ℕ} {u : ℕ → Bool}

theorem binary_walk_card_lower (hL : 6 ≤ L) (hB : 3 ≤ B) (hBL : B ≤ L - 2)
    (hmod : L % 4 = 2) (hg : BGood L B u)
    (hnumeric : 2 * (B - 1) * (B ^ 3 + 4) < 4 * (L + 2))
    (hu1 : u 1 = false) (hu2 : u 2 = false) (hu3 : u 3 = true)
    {S : Type} [DecidableEq S] {c : ℕ → S}
    (huaw : IsUAWalk (word L u) (3 * L + 1) c) :
    L + 3 ≤ (walkStates (3 * L + 1) c).card := by
  by_contra hn
  have hc : (walkStates (3 * L + 1) c).card ≤ L + 2 := by omega
  have houter := outer_at_most_two (by omega) hB hg hnumeric huaw hc
  rcases run_configuration hL huaw houter hc with hloop | htwo
  · obtain ⟨a, r, hl, ha, ha', hb, hb'⟩ := hloop
    rcases (show (a = L ∧ r = L + 1) ∨ (a = L ∧ r = L) ∨
        (a = L + 1 ∧ r = L - 1) ∨ (a = L + 1 ∧ r = L) by omega) with
      hcase | hcase | hcase | hcase
    · obtain ⟨hae, hre⟩ := hcase
      subst a r
      exact no_loop_A0 hL hu1 hu3 huaw hc hl
    · obtain ⟨hae, hre⟩ := hcase
      subst a r
      exact no_length_L_loop hL hBL hg huaw hl hc
    · obtain ⟨hae, hre⟩ := hcase
      subst a r
      exact no_a2_loop hL huaw hl hc hu1 hu2
    · obtain ⟨hae, hre⟩ := hcase
      subst a r
      have hrev := reverse_unique_walk (by omega) huaw
      have hgr := hg.reverse (by omega)
      have hlr : LoopBlock (3 * L + 1) (reverseWalk (3 * L + 1) c) L L := by
        convert hl.reverse using 1
        omega
      have hcr : (walkStates (3 * L + 1) (reverseWalk (3 * L + 1) c)).card ≤ L + 2 := by
        simpa only [walkStates_reverse] using hc
      exact no_length_L_loop hL hBL hgr hrev hlr hcr
  · exact confined_two_cycle_impossible hL hmod hu2 hu3 huaw htwo houter hc

theorem binary_AN_lower (hL : 6 ≤ L) (hB : 3 ≤ B) (hBL : B ≤ L - 2)
    (hmod : L % 4 = 2) (hg : BGood L B u)
    (hnumeric : 2 * (B - 1) * (B ^ 3 + 4) < 4 * (L + 2))
    (hu1 : u 1 = false) (hu2 : u 2 = false) (hu3 : u 3 = true) :
    L + 3 ≤ AN (3 * L + 1) (word L u) := by
  apply le_AN _ (uniqueSizes_nonempty (3 * L + 1) (word L u))
  intro q hq
  obtain ⟨step, st, acc, huniq⟩ := hq
  obtain ⟨c, hc⟩ := huniq.1
  have huaw := isUAWalk_of_uniquelyAccepts huniq hc
  have hlo := binary_walk_card_lower hL hB hBL hmod hg hnumeric hu1 hu2 hu3 huaw
  exact hlo.trans (walkStates_card_le_of_fin c)

/-- A good seed with prefix 001 gives a strict binary separation. -/
theorem binary_family_separation (hL : 6 ≤ L) (hB : 3 ≤ B) (hBL : B ≤ L - 2)
    (hmod : L % 4 = 2) (hg : BGood L B u)
    (hnumeric : 2 * (B - 1) * (B ^ 3 + 4) < 4 * (L + 2))
    (hu1 : u 1 = false) (hu2 : u 2 = false) (hu3 : u 3 = true) :
    ANe (3 * L + 1) (word L u) < AN (3 * L + 1) (word L u) := by
  have he := ANe_le (u := u) (by omega : 2 ≤ L)
  have hn := binary_AN_lower hL hB hBL hmod hg hnumeric hu1 hu2 hu3
  omega

end AneVsAn.BinarySeparation
