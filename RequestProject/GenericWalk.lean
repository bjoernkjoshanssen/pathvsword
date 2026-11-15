import RequestProject.Defs

/-!
# Uniquely accepting walks

This file gives word-independent versions of the walk definitions:
the *walk graph* of a coloring of the positions of a word, the notion of a
*uniquely accepting walk*, and the Walk characterization Lemma 2.1 (`lem:walk`).

Only the direction of Lemma 2.1 that is used for the lower bound is proved here,
namely: from an NFA uniquely accepting `z` one obtains a uniquely accepting walk
whose states are among the states of the NFA.
-/

namespace AneVsAn.Generic

set_option autoImplicit false

variable {Λ S : Type}

/-- The *walk graph* `Δ_W = {(c t, z t, c (t+1)) : 0 ≤ t ≤ n-1}` induced by a coloring
`c` of the positions `0,…,n` of the word `z` (Section 2, `sec:prelim`). -/
def walkStep (z : ℕ → Λ) (n : ℕ) (c : ℕ → S) : S → Λ → S → Prop :=
  fun s α s' => ∃ t, t < n ∧ c t = s ∧ z t = α ∧ c (t + 1) = s'

/-- `IsUAWalk z n c` says that the coloring `c₀,…,c_n` is a *uniquely accepting walk*
for `z`: the NFA `({c₀,…,c_n}, Σ, Δ_W, c₀, {c_n})` has exactly one path of length `n`
from `c₀` to `c_n` (Section 2, `sec:prelim`). -/
def IsUAWalk (z : ℕ → Λ) (n : ℕ) (c : ℕ → S) : Prop :=
  ∀ (x : ℕ → Λ) (p : ℕ → S), p 0 = c 0 → p n = c n → IsRun (walkStep z n c) n x p →
    (∀ t, t < n → x t = z t) ∧ (∀ t, t ≤ n → p t = c t)

/-- The walk itself is a path in its walk graph. -/
theorem isRun_walkStep {z : ℕ → Λ} {n : ℕ} (c : ℕ → S) :
    IsRun (walkStep z n c) n z c := by
  intro t ht
  exact ⟨t, ht, rfl, rfl, rfl⟩

/-- **Lemma 2.1 (Walk characterization, `lem:walk`), the direction used for the lower
bound.**  If the NFA `(step, st, acc)` uniquely accepts `z` (as a word of length `n`),
and `c` is its unique accepting path, then `c` is a uniquely accepting walk for `z`. -/
theorem isUAWalk_of_uniquelyAccepts {step : S → Λ → S → Prop} {st : S} {acc : S → Prop}
    {n : ℕ} {z : ℕ → Λ} (h : UniquelyAccepts step st acc n z)
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

end AneVsAn.Generic

namespace AneVsAn.Generic

variable {Λ S : Type} {n : ℕ} {x : ℕ → Λ} {c : ℕ → S}

/-- Reversing a uniquely accepting walk preserves unique acceptance. -/
theorem isUAWalk_reverse (huaw : IsUAWalk x n c) :
    IsUAWalk (fun t => x (n - 1 - t)) n (fun t => c (n - t)) := by
  intro y p hp0 hpn hrun
  let y' : ℕ → Λ := fun t => y (n - 1 - t)
  let p' : ℕ → S := fun t => p (n - t)
  have hp'0 : p' 0 = c 0 := by simpa only [p', Nat.sub_zero, Nat.sub_self] using hpn
  have hp'n : p' n = c n := by simpa only [p', Nat.sub_self, Nat.sub_zero] using hp0
  have hrun' : IsRun (walkStep x n c) n y' p' := by
    intro t ht
    obtain ⟨j, hj, h0, hx, h1⟩ := hrun (n - 1 - t) (by omega)
    refine ⟨n - 1 - j, by omega, ?_, hx, ?_⟩
    · change c (n - 1 - j) = p (n - t)
      convert h1 using 1 <;> congr 1 <;> omega
    · change c (n - 1 - j + 1) = p (n - (t + 1))
      convert h0 using 1 <;> congr 1 <;> omega
  obtain ⟨hy, hp⟩ := huaw y' p' hp'0 hp'n hrun'
  constructor
  · intro t ht
    have hh := hy (n - 1 - t) (by omega)
    change y (n - 1 - (n - 1 - t)) = x (n - 1 - t) at hh
    rwa [show n - 1 - (n - 1 - t) = t by omega] at hh
  · intro t ht
    have hh := hp (n - t) (by omega)
    change p (n - (n - t)) = c (n - t) at hh
    rwa [show n - (n - t) = t by omega] at hh

end AneVsAn.Generic
