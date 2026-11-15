import RequestProject.BinarySeparationDefs
import RequestProject.GenericReversal
import RequestProject.GenericLoops

/-! # Reversal symmetry of the binary family and of goodness -/

namespace AneVsAn.BinarySeparation

open AneVsAn.Generic

set_option autoImplicit false

def reverseSeed (L : ℕ) (u : ℕ → Bool) (k : ℕ) : Bool := u (L - 1 - k)

theorem word_reverse {L : ℕ} {u : ℕ → Bool} (hL : 2 ≤ L) {t : ℕ}
    (ht : t < 3 * L + 1) : word L (reverseSeed L u) t = word L u (3 * L - t) := by
  rcases (show t = 0 ∨ (1 ≤ t ∧ t ≤ L - 2) ∨ t = L - 1 ∨
      (L ≤ t ∧ t ≤ 2 * L) ∨ t = 2 * L + 1 ∨
      (2 * L + 2 ≤ t ∧ t < 3 * L) ∨ t = 3 * L by omega) with
    h | h | h | h | h | h | h
  · subst t
    rw [Nat.sub_zero, word_zero, word_last hL]
  · rw [word_left h.1 h.2 hL,
        show 3 * L - t = 2 * L + 1 + (L - 1 - t) by omega,
        word_right (by omega) (by omega) hL]
    rfl
  · subst t
    rw [show 3 * L - (L - 1) = 2 * L + 1 by omega,
      word_left_delimiter hL, word_right_delimiter hL]
  · rw [word_run hL h.1 h.2, word_run hL (by omega) (by omega)]
  · subst t
    rw [show 3 * L - (2 * L + 1) = L - 1 by omega,
      word_right_delimiter hL, word_left_delimiter hL]
  · have he : t = 2 * L + 1 + (t - (2 * L + 1)) := by omega
    conv_lhs => rw [he, word_right (by omega) (by omega) hL]
    rw [word_left (by omega) (by omega) hL]
    unfold reverseSeed
    congr 1
    omega
  · subst t
    rw [Nat.sub_self, word_last hL, word_zero]

theorem BGood.reverse {L B : ℕ} {u : ℕ → Bool} (hL : 2 ≤ L)
    (hgood : BGood L B u) : BGood L B (reverseSeed L u) := by
  intro i j p hp hij hjn hlen hout hper
  have hpj : p < j := by omega
  have hper' : HasPeriod (word L u) (3 * L + 1 - j) (3 * L + 1 - i) p := by
    intro t ht ht'
    have ha : i ≤ 3 * L - (t + p) := by omega
    have hb : 3 * L - (t + p) + p < j := by omega
    have he := hper (3 * L - (t + p)) ha hb
    rw [word_reverse hL (by omega), word_reverse hL (by omega)] at he
    have he1 : 3 * L - (3 * L - (t + p)) = t + p := by omega
    have he2 : 3 * L - (3 * L - (t + p) + p) = t := by omega
    rw [he1, he2] at he
    exact he.symm
  have h := hgood (3 * L + 1 - j) (3 * L + 1 - i) p hp
    (by omega) (by omega) (by omega) (by omega) hper'
  omega

theorem reverse_unique_walk {L : ℕ} {u : ℕ → Bool} {S : Type} {c : ℕ → S}
    (hL : 2 ≤ L) (h : IsUAWalk (word L u) (3 * L + 1) c) :
    IsUAWalk (word L (reverseSeed L u)) (3 * L + 1) (reverseWalk (3 * L + 1) c) := by
  apply h.reverse.congr_word
  intro t ht
  simpa only [reverseWord, show 3 * L + 1 - 1 = 3 * L by omega] using
    (word_reverse hL ht).symm

end AneVsAn.BinarySeparation

namespace AneVsAn.Generic

variable {n a r : ℕ} {S : Type} {c : ℕ → S}

theorem LoopBlock.reverse (h : LoopBlock n c a r) :
    LoopBlock n (reverseWalk n c) (n - (a + r)) r := by
  have hr := h.1
  have hn := h.2.1
  refine ⟨hr, by omega, ?_⟩
  intro t ht
  simp only [reverseWalk, show n - (n - (a + r)) = a + r by omega]
  have har : c (a + r) = c a := (h.2.2 (a + r) hn).2 ⟨by omega, le_rfl⟩
  rw [har, h.2.2 (n - t) (by omega)]
  omega

end AneVsAn.Generic
