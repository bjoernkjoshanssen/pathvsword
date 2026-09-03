import RequestProject.Walk

/-!
# The base cases `k ∈ {3,6,9,12,15}` (Section 7 of `anevsanseparationv4.tex`)

The proof of the lower bound in `anevsanseparationv4.tex` assumes `k ≥ 18` and settles the
five remaining cases `k ∈ {3,6,9,12,15}` by the exhaustive machine search of
Section 7 (`sec:verification`).

This file isolates that search in a single statement, `base_search`, and reduces the
general case to it: `walk_relabel` shows that a uniquely accepting walk with at most `k+5`
states may be recoloured by states in `Fin (k+5)`, so that `base_search` is a statement
about the finitely many colourings `c : {0,…,3k+7} → Fin (k+5)` of the positions of `z_k`.

`base_search` is the **only** finite-search `sorry` of the development: for each of the
five values of `k` it is a property of the `(k+5)^(3k+8)` colourings of the `3k+8`
positions of `z_k` by `k+5` states, each of which can be tested by inspecting the
finitely many paths of length `n` in the resulting walk graph.  (As stated it is not
literally an instance of Lean's `Decidable` class, because a colouring is given as a
function on all of `ℕ` and unique acceptance quantifies over all pairs `(x,p)` of a word
and a path; but both only depend on the restrictions to `{0,…,n}`, so the statement is
equivalent to a finite check, and it is exactly the check performed in Section 7 of the
source.)
-/

namespace AneVsAn

set_option autoImplicit false

/-- **Recolouring.**  A uniquely accepting walk for `z_k` with at most `k+5` states can be
recoloured by states in `Fin (k+5)`: the walk graph only depends on the colouring up to
injective renaming of the colours. -/
theorem walk_relabel {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}
    (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) :
    ∃ c' : ℕ → Fin (k + 5), IsUAWalk (zw k) (3 * k + 7) c' := by
  classical
  set n := 3 * k + 7 with hn
  set A : Finset S := walkStates n c with hA
  have hmemA : ∀ u, u ≤ n → c u ∈ A := by
    intro u hu
    simp only [hA, walkStates, Finset.mem_image]
    exact ⟨u, Finset.mem_range.2 (by omega), rfl⟩
  -- an injective labelling of the states of the walk by `Fin (k+5)`
  set e : S → Fin (k + 5) := fun s =>
    if h : s ∈ A then Fin.castLE hcard (A.equivFin ⟨s, h⟩) else ⟨0, by omega⟩ with he
  have heinj : ∀ s ∈ A, ∀ s' ∈ A, e s = e s' → s = s' := by
    intro s hs s' hs' hss
    simp only [he, dif_pos hs, dif_pos hs'] at hss
    have := Fin.castLE_injective hcard hss
    have := (A.equivFin).injective this
    exact congrArg Subtype.val this
  -- a left inverse of `e` on the states of the walk
  set g : Fin (k + 5) → S := fun y =>
    if h : ∃ s, s ∈ A ∧ e s = y then h.choose else c 0 with hg
  have hge : ∀ s ∈ A, g (e s) = s := by
    intro s hs
    have hex : ∃ s', s' ∈ A ∧ e s' = e s := ⟨s, hs, rfl⟩
    simp only [hg, dif_pos hex]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    exact heinj _ h1 _ hs h2
  refine ⟨fun t => e (c t), ?_⟩
  intro x p' hp0 hpn hrun
  -- transport the path `p'` back to a path of the original walk graph
  set p : ℕ → S := fun t => g (p' t) with hp
  have hstep : ∀ t, t < n → ∃ u, u < n ∧ c u = p t ∧ zw k u = x t ∧ c (u + 1) = p (t + 1) := by
    intro t ht
    obtain ⟨u, hu, h1, h2, h3⟩ := hrun t ht
    refine ⟨u, hu, ?_, h2, ?_⟩
    · simp only [hp, ← h1, hge (c u) (hmemA u (by omega))]
    · simp only [hp, ← h3, hge (c (u + 1)) (hmemA (u + 1) (by omega))]
  have hp0' : p 0 = c 0 := by
    simp only [hp, hp0, hge (c 0) (hmemA 0 (by omega))]
  have hpn' : p n = c n := by
    simp only [hp, hpn, hge (c n) (hmemA n (by omega))]
  obtain ⟨hx, hpc⟩ := huaw x p hp0' hpn' (fun t ht => by
    obtain ⟨u, hu, h1, h2, h3⟩ := hstep t ht
    exact ⟨u, hu, h1, h2, h3⟩)
  refine ⟨hx, fun t ht => ?_⟩
  rcases Nat.lt_or_ge t n with hlt | hge'
  · obtain ⟨u', hu', h1', _, _⟩ := hrun t hlt
    -- `p' t = e (c u')`, and `p t = c u' = c t`
    have hpt : g (p' t) = c t := hpc t (by omega)
    have hcu : c u' = c t := by
      rw [← h1'] at hpt
      rwa [hge (c u') (hmemA u' (by omega))] at hpt
    rw [← h1']
    show e (c u') = e (c t)
    rw [hcu]
  · have : t = n := by omega
    subst this
    exact hpn

/-- **Section 7 of `anevsanseparationv4.tex` (`sec:verification`), base cases.**  For
`k ∈ {3,6,9,12,15}` no colouring of the `3k+8` positions of `z_k` by `k+5` states is a
uniquely accepting walk.  This is the exhaustive machine search of Section 7 of the
source, which the task allows to be left unproved.

This is the only `sorry` of the development that is a **finite check**: for each of the
five values of `k` the statement concerns the finitely many colourings
`{0,…,3k+7} → Fin (k+5)`, and for each of them unique acceptance is decided by inspecting
the finitely many paths of length `n` in the resulting walk graph. -/
theorem base_search {k : ℕ} (hk : 3 ≤ k) (hk15 : k ≤ 15) (hk3 : k % 3 = 0)
    (c : ℕ → Fin (k + 5)) : ¬ IsUAWalk (zw k) (3 * k + 7) c := by
  sorry

/-- The lower bound for the base cases `k ∈ {3,6,9,12,15}`: every uniquely accepting walk
for `z_k` has at least `k+6` states. -/
theorem walk_card_lower_base {k : ℕ} (hk : 3 ≤ k) (hk15 : k ≤ 15) (hk3 : k % 3 = 0)
    {S : Type} [DecidableEq S] (c : ℕ → S) (hc : IsUAWalk (zw k) (3 * k + 7) c) :
    k + 6 ≤ (walkStates (3 * k + 7) c).card := by
  by_contra hcon
  obtain ⟨c', hc'⟩ := walk_relabel hc (by omega)
  exact base_search hk hk15 hk3 c' hc'

end AneVsAn
