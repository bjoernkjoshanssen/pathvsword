import RequestProject.Walk
import RequestProject.UpperUnique
import RequestProject.WalkMain

/-!
# The lower bound `A_N(z_k) ≥ k+6`

This file derives the lower bound of Theorem 1.2 (`thm:main`) of
`anevsanseparationv4.tex` from the statement that every uniquely accepting walk for
`z_k` has at least `k+6` states (`walk_card_lower`, the content of Sections 4–6 of
the source), using the Walk characterization Lemma 2.1 (`lem:walk`).
-/

namespace AneVsAn

set_option autoImplicit false

/-- **Theorem 1.2 (`thm:main`), lower bound**: `A_N(z_k) ≥ k+6` for `k ≥ 3`
with `k ≡ 0 (mod 3)`. -/
theorem AN_lower {k : ℕ} (hk : 3 ≤ k) (hk3 : k % 3 = 0) : k + 6 ≤ AN (wlen k) (zw k) := by
  classical
  refine le_AN (fun q hq => ?_) (uniqueSizes_nonempty hk)
  obtain ⟨step, st, acc, hU⟩ := hq
  obtain ⟨c, hc⟩ := hU.1
  have hwalk : IsUAWalk (zw k) (wlen k) c := isUAWalk_of_uniquelyAccepts hU hc
  have h1 : k + 6 ≤ (walkStates (wlen k) c).card := walk_card_lower hk hk3 c hwalk
  exact h1.trans (walkStates_card_le_of_fin c)

end AneVsAn
