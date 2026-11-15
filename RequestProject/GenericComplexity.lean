import RequestProject.Defs

/-! # Complexity depends only on the finite word, not on its extension -/

namespace AneVsAn.Generic

set_option autoImplicit false

variable {Λ S : Type} {n : ℕ} {x y : ℕ → Λ}

theorem acc_congr_word {step : S → Λ → S → Prop} {st : S} {acc : S → Prop}
    {p : ℕ → S} (h : IsAcc step st acc n x p) (hxy : ∀ t, t < n → x t = y t) :
    IsAcc step st acc n y p := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro t ht
  rw [← hxy t ht]
  exact h.2.2 t ht

theorem exactlyAccepts_congr_word {step : S → Λ → S → Prop} {st : S} {acc : S → Prop}
    (h : ExactlyAccepts step st acc n x) (hxy : ∀ t, t < n → x t = y t) :
    ExactlyAccepts step st acc n y := by
  obtain ⟨⟨p, hp⟩, hx⟩ := h
  refine ⟨⟨p, acc_congr_word hp hxy⟩, ?_⟩
  intro z q hq t ht
  exact (hx z q hq t ht).trans (hxy t ht)

theorem uniquelyAccepts_congr_word {step : S → Λ → S → Prop} {st : S} {acc : S → Prop}
    (h : UniquelyAccepts step st acc n x) (hxy : ∀ t, t < n → x t = y t) :
    UniquelyAccepts step st acc n y := by
  obtain ⟨⟨p, hp⟩, huniq⟩ := h
  exact ⟨⟨p, acc_congr_word hp hxy⟩, huniq⟩

theorem exactSizes_congr_word (hxy : ∀ t, t < n → x t = y t) :
    ExactSizes n x = ExactSizes n y := by
  ext q
  constructor
  · rintro ⟨step, st, acc, h⟩
    exact ⟨step, st, acc, exactlyAccepts_congr_word h hxy⟩
  · rintro ⟨step, st, acc, h⟩
    exact ⟨step, st, acc, exactlyAccepts_congr_word h (fun t ht => (hxy t ht).symm)⟩

theorem uniqueSizes_congr_word (hxy : ∀ t, t < n → x t = y t) :
    UniqueSizes n x = UniqueSizes n y := by
  ext q
  constructor
  · rintro ⟨step, st, acc, h⟩
    exact ⟨step, st, acc, uniquelyAccepts_congr_word h hxy⟩
  · rintro ⟨step, st, acc, h⟩
    exact ⟨step, st, acc, uniquelyAccepts_congr_word h (fun t ht => (hxy t ht).symm)⟩

theorem ANe_congr_word (hxy : ∀ t, t < n → x t = y t) : ANe n x = ANe n y := by
  unfold ANe
  rw [exactSizes_congr_word hxy]

theorem AN_congr_word (hxy : ∀ t, t < n → x t = y t) : AN n x = AN n y := by
  unfold AN
  rw [uniqueSizes_congr_word hxy]

/-- Turn the relevant prefix of a total word into a finite list. -/
def toList (n : ℕ) (x : ℕ → Λ) : List Λ := List.ofFn (fun i : Fin n => x i)

@[simp] theorem length_toList (n : ℕ) (x : ℕ → Λ) : (toList n x).length = n := by
  simp [toList]

theorem getD_toList {d : Λ} {t : ℕ} (ht : t < n) : (toList n x).getD t d = x t := by
  simp [toList, List.getD, ht]

end AneVsAn.Generic
