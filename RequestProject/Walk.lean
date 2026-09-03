import RequestProject.Defs

/-!
# Uniquely accepting walks

This file formalizes Section 2 (`sec:prelim`) of `anevsanseparationv4.tex`:
the *walk graph* of a coloring of the positions of a word, the notion of a
*uniquely accepting walk*, and the Walk characterization Lemma 2.1 (`lem:walk`).

Only the direction of Lemma 2.1 that is used for the lower bound is proved here,
namely: from an NFA uniquely accepting `z` one obtains a uniquely accepting walk
whose states are among the states of the NFA.
-/

namespace AneVsAn

set_option autoImplicit false

variable {S : Type}

/-- The *walk graph* `Δ_W = {(c t, z t, c (t+1)) : 0 ≤ t ≤ n-1}` induced by a coloring
`c` of the positions `0,…,n` of the word `z` (Section 2, `sec:prelim`). -/
def walkStep (z : ℕ → Ltr) (n : ℕ) (c : ℕ → S) : S → Ltr → S → Prop :=
  fun s α s' => ∃ t, t < n ∧ c t = s ∧ z t = α ∧ c (t + 1) = s'

/-- `IsUAWalk z n c` says that the coloring `c₀,…,c_n` is a *uniquely accepting walk*
for `z`: the NFA `({c₀,…,c_n}, Σ, Δ_W, c₀, {c_n})` has exactly one path of length `n`
from `c₀` to `c_n` (Section 2, `sec:prelim`). -/
def IsUAWalk (z : ℕ → Ltr) (n : ℕ) (c : ℕ → S) : Prop :=
  ∀ (x : ℕ → Ltr) (p : ℕ → S), p 0 = c 0 → p n = c n → IsRun (walkStep z n c) n x p →
    (∀ t, t < n → x t = z t) ∧ (∀ t, t ≤ n → p t = c t)

/-- The walk itself is a path in its walk graph. -/
theorem isRun_walkStep {z : ℕ → Ltr} {n : ℕ} (c : ℕ → S) :
    IsRun (walkStep z n c) n z c := by
  intro t ht
  exact ⟨t, ht, rfl, rfl, rfl⟩

/-- **Lemma 2.1 (Walk characterization, `lem:walk`), the direction used for the lower
bound.**  If the NFA `(step, st, acc)` uniquely accepts `z` (as a word of length `n`),
and `c` is its unique accepting path, then `c` is a uniquely accepting walk for `z`. -/
theorem isUAWalk_of_uniquelyAccepts {step : S → Ltr → S → Prop} {st : S} {acc : S → Prop}
    {n : ℕ} {z : ℕ → Ltr} (h : UniquelyAccepts step st acc n z)
    {c : ℕ → S} (hc : IsAcc step st acc n z c) :
    IsUAWalk z n c := by
  intro x p hp0 hpn hrun
  have hstep : ∀ t, t < n → step (p t) (x t) (p (t + 1)) := by
    intro t ht
    obtain ⟨u, hu, h1, h2, h3⟩ := hrun t ht
    have := hc.2.2 u hu
    rw [h1, h2, h3] at this
    exact this
  have hacc : IsAcc step st acc n x p := by
    refine ⟨by rw [hp0]; exact hc.1, ?_, hstep⟩
    rw [hpn]; exact hc.2.1
  exact h.2 x p z c hacc hc

/-- The number of states of the walk `c` (as a word of length `n`), i.e. the
cardinality of `{c₀,…,c_n}`. -/
def walkStates [DecidableEq S] (n : ℕ) (c : ℕ → S) : Finset S :=
  (Finset.range (n + 1)).image c

theorem walkStates_card_le_of_fin {q n : ℕ} (c : ℕ → Fin q) :
    (walkStates n c).card ≤ q := by
  classical
  calc (walkStates n c).card ≤ (Finset.univ : Finset (Fin q)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = q := by simp

end AneVsAn
