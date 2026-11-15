import RequestProject.GenericWalk

/-! # Reversing words and uniquely accepting walks -/

namespace AneVsAn.Generic

set_option autoImplicit false

variable {Λ S : Type} {n : ℕ} {x y : ℕ → Λ} {c : ℕ → S}

def reverseWord (n : ℕ) (x : ℕ → Λ) (t : ℕ) : Λ := x (n - 1 - t)

def reverseWalk (n : ℕ) (c : ℕ → S) (t : ℕ) : S := c (n - t)

theorem IsUAWalk.congr_word (h : IsUAWalk x n c)
    (hxy : ∀ t, t < n → x t = y t) : IsUAWalk y n c := by
  intro z p hp0 hpn hp
  have hp' : IsRun (walkStep x n c) n z p := by
    intro t ht
    obtain ⟨u, hu, h0, h1, h2⟩ := hp t ht
    exact ⟨u, hu, h0, (hxy u hu).trans h1, h2⟩
  obtain ⟨hz, hc⟩ := h z p hp0 hpn hp'
  exact ⟨fun t ht => (hz t ht).trans (hxy t ht), hc⟩

theorem IsUAWalk.reverse (h : IsUAWalk x n c) :
    IsUAWalk (reverseWord n x) n (reverseWalk n c) := by
  exact isUAWalk_reverse h

theorem walkStates_reverse [DecidableEq S] :
    walkStates n (reverseWalk n c) = walkStates n c := by
  ext s
  simp only [walkStates, Finset.mem_image, Finset.mem_range, reverseWalk]
  constructor
  · rintro ⟨t, ht, hs⟩
    exact ⟨n - t, by omega, hs⟩
  · rintro ⟨t, ht, hs⟩
    exact ⟨n - t, by omega, by simpa only [show n - (n - t) = t by omega] using hs⟩

end AneVsAn.Generic
