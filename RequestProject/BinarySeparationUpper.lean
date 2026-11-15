import RequestProject.BinarySeparationDefs

/-!
# An exact acceptor with `L + 2` states

The chain states are `0, …, L - 1`, and the zero gadget states are `L, L + 1`.
An accepting run has a chain prefix and a final edge to `0`. Every intervening
return to the last chain state has length `L + z`, where `z = 0` or `z ≥ 2`.
At total length `3 * L + 1`, exactly one such return is possible and its zero
gadget has length `L + 1`.
-/

namespace AneVsAn.BinarySeparation

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Transition relation, with states represented by natural numbers. -/
def exactStep (L : ℕ) (u : ℕ → Bool) (i : ℕ) (a : Bool) (j : ℕ) : Prop :=
    (i + 1 < L ∧ a = (if i = 0 then false else u i) ∧ j = i + 1)
  ∨ (i = L - 1 ∧ a = false ∧ j = 0)
  ∨ (i = L - 1 ∧ a = true ∧ j = L)
  ∨ (i = L ∧ a = false ∧ j = L + 1)
  ∨ (i = L + 1 ∧ a = false ∧ (j = L ∨ j = L + 1))
  ∨ (i = L ∧ a = true ∧ j = 1)

private theorem step_chain {L i j : ℕ} {u : ℕ → Bool} {a : Bool}
    (hL : 2 ≤ L) (hi : i < L - 1) (h : exactStep L u i a j) :
    a = (if i = 0 then false else u i) ∧ j = i + 1 := by
  rcases h with ⟨_, ha, hj⟩ | ⟨hi', _, _⟩ | ⟨hi', _, _⟩ |
    ⟨hi', _, _⟩ | ⟨hi', _, _⟩ | ⟨hi', _, _⟩
  · exact ⟨ha, hj⟩
  all_goals omega

private theorem step_last {L j : ℕ} {u : ℕ → Bool} {a : Bool}
    (hL : 2 ≤ L) (h : exactStep L u (L - 1) a j) :
    (a = false ∧ j = 0) ∨ (a = true ∧ j = L) := by
  rcases h with ⟨hi, _, _⟩ | ⟨_, ha, hj⟩ | ⟨_, ha, hj⟩ |
    ⟨hi, _, _⟩ | ⟨hi, _, _⟩ | ⟨hi, _, _⟩
  · omega
  · exact Or.inl ⟨ha, hj⟩
  · exact Or.inr ⟨ha, hj⟩
  all_goals omega

private theorem step_gadget {L i j : ℕ} {u : ℕ → Bool} {a : Bool}
    (hL : 2 ≤ L) (hi : i = L ∨ i = L + 1) (h : exactStep L u i a j) :
    (a = false ∧ (j = L ∨ j = L + 1)) ∨ (i = L ∧ a = true ∧ j = 1) := by
  rcases h with ⟨hi', _, _⟩ | ⟨hi', _, _⟩ | ⟨hi', _, _⟩ |
    ⟨hi', ha, hj⟩ | ⟨hi', ha, hj⟩ | ⟨hi', ha, hj⟩
  · omega
  · omega
  · omega
  · exact Or.inl ⟨ha, Or.inr hj⟩
  · exact Or.inl ⟨ha, hj⟩
  · exact Or.inr ⟨hi', ha, hj⟩

section Analysis

variable {L N : ℕ} {u x : ℕ → Bool} {f : ℕ → ℕ}

private theorem before_end (hend : f N = 0) {v : ℕ} (hv : v ≤ N) (hf : f v ≠ 0) :
    v < N := by
  by_contra h
  have : v = N := by omega
  subst v
  exact hf hend

/-- Following the deterministic positive part of the chain. -/
private theorem chain_positive (hL : 2 ≤ L)
    (hrun : ∀ t, t < N → exactStep L u (f t) (x t) (f (t + 1)))
    (hend : f N = 0) {v i : ℕ} (hv : v ≤ N) (hfi : f v = i)
    (hi : 1 ≤ i) (hiL : i ≤ L - 1) :
    ∀ j, j ≤ L - 1 - i → v + j < N ∧ f (v + j) = i + j ∧
      (i + j < L - 1 → x (v + j) = u (i + j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    have hlt : v < N := before_end hend hv (by omega)
    refine ⟨by simpa using hlt, by simpa using hfi, ?_⟩
    intro h
    have hs := step_chain hL (by simpa using h) (hfi ▸ hrun v hlt)
    simpa [show i ≠ 0 by omega] using hs.1
  | succ j ih =>
    intro hj
    obtain ⟨hvn, hfj, _⟩ := ih (by omega)
    have hs := step_chain hL (by omega : i + j < L - 1) (hfj ▸ hrun (v + j) hvn)
    have hfnext : f (v + (j + 1)) = i + (j + 1) := by
      simpa [Nat.add_assoc] using hs.2
    have hvnext : v + (j + 1) < N := before_end hend (by omega) (by omega)
    refine ⟨hvnext, hfnext, ?_⟩
    intro h
    have hs' := step_chain hL h (hfnext ▸ hrun (v + (j + 1)) hvnext)
    simpa [show i + (j + 1) ≠ 0 by omega] using hs'.1

/-- Following a full chain prefix from state `0`. -/
private theorem chain_from_zero (hL : 2 ≤ L)
    (hrun : ∀ t, t < N → exactStep L u (f t) (x t) (f (t + 1)))
    (hend : f N = 0) {v : ℕ} (hv : v < N) (hfv : f v = 0) :
    v + (L - 1) < N ∧ f (v + (L - 1)) = L - 1 ∧ x v = false ∧
      (∀ k, 1 ≤ k → k ≤ L - 2 → x (v + k) = u k) := by
  have hs := step_chain hL (by omega : 0 < L - 1) (hfv ▸ hrun v hv)
  have hf1 : f (v + 1) = 1 := by simpa using hs.2
  have hc := chain_positive hL hrun hend (by omega) hf1 (by omega) (by omega)
  obtain ⟨hlt, hlast, _⟩ := hc (L - 2) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hlt using 1 <;> omega
  · simpa only [show v + 1 + (L - 2) = v + (L - 1) by omega,
      show 1 + (L - 2) = L - 1 by omega] using hlast
  · simpa using hs.1
  · intro k hk hkL
    obtain ⟨_, _, hlabel⟩ := hc (k - 1) (by omega)
    have heq := hlabel (by omega)
    convert heq using 2 <;> omega

/-- Every visit to the zero gadget is eventually followed by its unique exit. -/
private theorem gadget_exit (hL : 2 ≤ L)
    (hrun : ∀ t, t < N → exactStep L u (f t) (x t) (f (t + 1)))
    (hend : f N = 0) :
    ∀ d v, N - v ≤ d → v ≤ N → (f v = L ∨ f v = L + 1) →
      ∃ z, v + z < N ∧ (∀ i, i < z → x (v + i) = false) ∧
        f (v + z) = L ∧ x (v + z) = true ∧ f (v + z + 1) = 1 := by
  intro d
  induction d with
  | zero =>
    intro v hd hv hf
    have : v = N := by omega
    subst v
    omega
  | succ d ih =>
    intro v hd hv hf
    have hlt : v < N := before_end hend hv (by omega)
    rcases step_gadget hL hf (hrun v hlt) with ⟨ha, hnext⟩ | ⟨hfg, ha, hnext⟩
    · obtain ⟨z, hz, hzero, hfg, hexit, hnext'⟩ :=
        ih (v + 1) (by omega) (by omega) hnext
      refine ⟨z + 1, by omega, ?_, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hi0 : i = 0
        · subst i; simpa using ha
        · convert hzero (i - 1) (by omega) using 2 <;> omega
      · convert hfg using 2 <;> omega
      · convert hexit using 2 <;> omega
      · convert hnext' using 2 <;> omega
    · exact ⟨0, by simpa using hlt, by omega, by simpa using hfg,
        by simpa using ha, by simpa using hnext⟩

/-- A zero-gadget return from `L` to `L` cannot have length one. -/
private theorem gadget_length_ne_one (hL : 2 ≤ L)
    (hrun : ∀ t, t < N → exactStep L u (f t) (x t) (f (t + 1)))
    {v z : ℕ} (hv : v + z < N) (hf : f v = L)
    (hz : ∀ i, i < z → x (v + i) = false) (hend : f (v + z) = L) :
    z = 0 ∨ 2 ≤ z := by
  by_contra h
  have hz1 : z = 1 := by omega
  subst z
  have hzero : x v = false := by simpa using hz 0 (by omega)
  have hs := hrun v (by omega)
  rw [hf, hzero] at hs
  rcases hs with ⟨hi, _, _⟩ | ⟨hi, _, _⟩ | ⟨hi, _, _⟩ |
    ⟨_, _, hj⟩ | ⟨hi, _, _⟩ | ⟨_, ha, _⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · cases ha

/-- The next return to the last chain state, or the final accepting edge. -/
private theorem last_step (hL : 2 ≤ L)
    (hrun : ∀ t, t < N → exactStep L u (f t) (x t) (f (t + 1)))
    (hend : f N = 0) {v : ℕ} (hv : v ≤ N) (hfv : f v = L - 1) :
    (v + 1 = N ∧ x v = false) ∨
      ∃ z, (z = 0 ∨ 2 ≤ z) ∧ v + L + z < N ∧ f (v + L + z) = L - 1 ∧
        (0 < z → x v = true ∧
          (∀ i, i < z → x (v + 1 + i) = false) ∧ x (v + 1 + z) = true ∧
          (∀ k, 1 ≤ k → k ≤ L - 2 → x (v + 1 + z + k) = u k)) := by
  have hlt : v < N := before_end hend hv (by omega)
  rcases step_last hL (hfv ▸ hrun v hlt) with ⟨ha, hf0⟩ | ⟨ha, hfg⟩
  · by_cases hfinal : v + 1 = N
    · exact Or.inl ⟨hfinal, ha⟩
    · obtain ⟨hc, hlast, _, _⟩ := chain_from_zero hL hrun hend (by omega) hf0
      right
      refine ⟨0, Or.inl rfl, ?_, ?_, by omega⟩
      · convert hc using 1 <;> omega
      · convert hlast using 2 <;> omega
  · obtain ⟨z, hz, hzero, hlastg, hexit, hf1⟩ :=
      gadget_exit hL hrun hend (N - (v + 1)) (v + 1) (Nat.le_refl _) (by omega) (Or.inl hfg)
    have hzlen := gadget_length_ne_one hL hrun hz hfg hzero hlastg
    have hc := chain_positive hL hrun hend (by omega) hf1 (by omega) (by omega)
    obtain ⟨hcn, hclast, _⟩ := hc (L - 2) (by omega)
    right
    refine ⟨z, hzlen, ?_, ?_, ?_⟩
    · convert hcn using 1 <;> omega
    · simpa only [show v + 1 + z + 1 + (L - 2) = v + L + z by omega,
        show 1 + (L - 2) = L - 1 by omega] using hclast
    · intro _
      refine ⟨ha, hzero, hexit, ?_⟩
      intro k hk hkL
      obtain ⟨_, _, hlabel⟩ := hc (k - 1) (by omega)
      have heq := hlabel (by omega)
      convert heq using 2 <;> omega

/-- Every accepting run of the required length spells the binary family word. -/
theorem exact_run_word (hL : 2 ≤ L)
    (hrun : ∀ t, t < 3 * L + 1 → exactStep L u (f t) (x t) (f (t + 1)))
    (hstart : f 0 = 0) (hend : f (3 * L + 1) = 0) :
    ∀ t, t < 3 * L + 1 → x t = word L u t := by
  obtain ⟨hv, hlast, hx0, hleft⟩ := chain_from_zero hL hrun hend (by omega) hstart
  simp only [Nat.zero_add] at hv hlast hleft
  rcases last_step hL hrun hend (by omega) hlast with ⟨hfin, _⟩ | ⟨z, hz, hzn, hzf, hletters⟩
  · omega
  have hfinal : L - 1 + L + z + 1 = 3 * L + 1 := by
    rcases last_step hL hrun hend (by omega) hzf with ⟨hfin, _⟩ |
      ⟨z', hz', hz'n, hz'f, _⟩
    · exact hfin
    · have hz0 : z = 0 := by omega
      have hz'0 : z' = 0 := by omega
      rcases last_step hL hrun hend (by omega) hz'f with ⟨hfin, _⟩ |
        ⟨z'', _, hz''n, _, _⟩ <;> omega
  have hzval : z = L + 1 := by omega
  subst z
  obtain ⟨hxdel, hxzero, hxdel', hright⟩ := hletters (by omega)
  have hxlast : x (3 * L) = false := by
    have hs := hrun (3 * L) (by omega)
    have hflast : f (3 * L) = L - 1 := by convert hzf using 2 <;> omega
    rw [hflast] at hs
    rcases step_last hL hs with ⟨ha, _⟩ | ⟨_, hf⟩
    · exact ha
    · omega
  intro t ht
  by_cases ht0 : t = 0
  · subst t; simpa using hx0
  by_cases htleft : t < L - 1
  · rw [word_left (by omega) (by omega) hL]
    exact hleft t (by omega) (by omega)
  by_cases htdel : t = L - 1
  · subst t; rw [word_left_delimiter hL]; exact hxdel
  by_cases htrun : t ≤ 2 * L
  · rw [word_run hL (by omega) htrun]
    convert hxzero (t - L) (by omega) using 2 <;> omega
  by_cases htdel' : t = 2 * L + 1
  · subst t; rw [word_right_delimiter hL]
    convert hxdel' using 2 <;> omega
  by_cases htright : t < 3 * L
  · have hk : 1 ≤ t - (2 * L + 1) := by omega
    have hkL : t - (2 * L + 1) ≤ L - 2 := by omega
    have heq := word_right hk hkL hL (u := u)
    have heq' := hright (t - (2 * L + 1)) hk hkL
    convert heq'.trans heq.symm using 2 <;> omega
  · have htlast : t = 3 * L := by omega
    subst t; rw [word_last hL]; exact hxlast

end Analysis

/-- A particular accepting run, traversing the zero gadget once. -/
def exactWitness (L t : ℕ) : ℕ :=
  if t ≤ L then t
  else if t < 2 * L + 1 then L + 1
  else if t = 2 * L + 1 then L
  else if t < 3 * L + 1 then t - (2 * L + 1)
  else 0

private theorem exactWitness_lt {L t : ℕ} (hL : 2 ≤ L) : exactWitness L t < L + 2 := by
  unfold exactWitness
  split_ifs <;> omega

private theorem exactWitness_run {L : ℕ} {u : ℕ → Bool} (hL : 2 ≤ L) :
    ∀ t, t < 3 * L + 1 →
      exactStep L u (exactWitness L t) (word L u t) (exactWitness L (t + 1)) := by
  intro t ht
  by_cases hc : t < L - 1
  · left
    have htL : t ≤ L := by omega
    have htL' : t + 1 ≤ L := by omega
    simp only [exactWitness, if_pos htL, if_pos htL']
    refine ⟨by omega, ?_, by trivial⟩
    by_cases ht0 : t = 0
    · subst t; simp
    · simpa [ht0] using word_left (by omega) (by omega) hL (u := u)
  by_cases hdel : t = L - 1
  · subst t
    right; right; left
    simp [exactWitness, show L - 1 ≤ L by omega, show L - 1 + 1 = L by omega,
      word_left_delimiter hL]
  by_cases hg : t = L
  · subst t
    right; right; right; left
    simp [exactWitness, show ¬L + 1 ≤ L by omega, show L + 1 < 2 * L + 1 by omega,
      word_run (t := L) (u := u) hL (by omega) (by omega)]
  by_cases hh : t < 2 * L
  · have htv : exactWitness L t = L + 1 := by
      simp [exactWitness, show ¬t ≤ L by omega, show t < 2 * L + 1 by omega]
    have htv' : exactWitness L (t + 1) = L + 1 := by
      simp [exactWitness, show ¬t + 1 ≤ L by omega, show t + 1 < 2 * L + 1 by omega]
    rw [htv, htv', word_run hL (by omega) (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inr rfl⟩))))
  by_cases hhg : t = 2 * L
  · subst t
    have htv : exactWitness L (2 * L) = L + 1 := by
      simp [exactWitness, show ¬2 * L ≤ L by omega]
    have htv' : exactWitness L (2 * L + 1) = L := by
      simp [exactWitness, show ¬2 * L + 1 ≤ L by omega]
    rw [htv, htv', word_run hL (by omega) (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Or.inl rfl⟩))))
  by_cases hgd : t = 2 * L + 1
  · subst t
    have htv : exactWitness L (2 * L + 1) = L := by
      simp [exactWitness, show ¬2 * L + 1 ≤ L by omega]
    have htv' : exactWitness L (2 * L + 1 + 1) = 1 := by
      simp [exactWitness, show ¬2 * L + 1 + 1 ≤ L by omega,
        show ¬2 * L + 1 + 1 < 2 * L + 1 by omega,
        show 2 * L + 1 + 1 < 3 * L + 1 by omega]
    rw [htv, htv', word_right_delimiter hL]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
  by_cases hr : t < 3 * L
  · have htv : exactWitness L t = t - (2 * L + 1) := by
      simp [exactWitness, show ¬t ≤ L by omega, show ¬t < 2 * L + 1 by omega,
        hgd, show t < 3 * L + 1 by omega]
    have htv' : exactWitness L (t + 1) = t + 1 - (2 * L + 1) := by
      simp [exactWitness, show ¬t + 1 ≤ L by omega, show ¬t + 1 < 2 * L + 1 by omega,
        hhg, show t + 1 < 3 * L + 1 by omega]
    rw [htv, htv']
    left
    refine ⟨by omega, ?_, by omega⟩
    rw [if_neg (by omega : t - (2 * L + 1) ≠ 0)]
    have heq := word_right (L := L) (u := u) (t := t - (2 * L + 1))
      (by omega) (by omega) hL
    convert heq using 2 <;> omega
  · have htlast : t = 3 * L := by omega
    subst t
    right; left
    have htv : exactWitness L (3 * L) = L - 1 := by
      simp [exactWitness, show ¬3 * L ≤ L by omega, show ¬3 * L < 2 * L + 1 by omega,
        show 3 * L ≠ 2 * L + 1 by omega]
      omega
    have htv' : exactWitness L (3 * L + 1) = 0 := by
      simp [exactWitness, show ¬3 * L + 1 ≤ L by omega,
        show ¬3 * L + 1 < 2 * L + 1 by omega, show 3 * L ≠ 2 * L by omega]
    exact ⟨htv, word_last hL, htv'⟩

/-- The family is exactly accepted by an NFA with `L + 2` states. -/
theorem exact_size {L : ℕ} {u : ℕ → Bool} (hL : 2 ≤ L) :
    L + 2 ∈ ExactSizes (3 * L + 1) (word L u) := by
  let step : Fin (L + 2) → Bool → Fin (L + 2) → Prop :=
    fun i a j => exactStep L u i.val a j.val
  let start : Fin (L + 2) := ⟨0, by omega⟩
  let final : Fin (L + 2) → Prop := fun i => i.val = 0
  refine ⟨step, start, final, ?_, ?_⟩
  · let p : ℕ → Fin (L + 2) := fun t => ⟨exactWitness L t, exactWitness_lt hL⟩
    refine ⟨p, ?_, ?_, ?_⟩
    · apply Fin.ext; simp [p, start, exactWitness]
    · change exactWitness L (3 * L + 1) = 0
      simp [exactWitness, show ¬3 * L + 1 ≤ L by omega,
        show ¬3 * L + 1 < 2 * L + 1 by omega, show 3 * L ≠ 2 * L by omega]
    · exact exactWitness_run hL
  · intro x p hp
    apply exact_run_word hL (f := fun t => (p t).val)
    · exact hp.2.2
    · exact congrArg Fin.val hp.1
    · exact hp.2.1

/-- The exact-complexity upper bound used for binary infinitude. -/
theorem ANe_le {L : ℕ} {u : ℕ → Bool} (hL : 2 ≤ L) :
    AneVsAn.ANe (3 * L + 1) (word L u) ≤ L + 2 :=
  AneVsAn.ANe_le (exact_size hL)

/-- A chain automaton uniquely accepts every finite word. This supplies the
nonemptiness hypothesis of `le_AN` without needing the sharper unique upper bound. -/
theorem uniqueSizes_nonempty {Λ : Type} (n : ℕ) (w : ℕ → Λ) :
    (UniqueSizes n w).Nonempty := by
  let step : Fin (n + 1) → Λ → Fin (n + 1) → Prop :=
    fun i a j => j.val = i.val + 1 ∧ a = w i.val
  let start : Fin (n + 1) := ⟨0, by omega⟩
  let final : Fin (n + 1) → Prop := fun i => i.val = n
  have shape : ∀ x p, IsAcc step start final n x p →
      (∀ t, t ≤ n → (p t).val = t) ∧ (∀ t, t < n → x t = w t) := by
    intro x p hp
    have hstates : ∀ t, t ≤ n → (p t).val = t := by
      intro t
      induction t with
      | zero =>
        intro _
        exact congrArg Fin.val hp.1
      | succ t ih =>
        intro ht
        have hs := (hp.2.2 t (by omega)).1
        change (p (t + 1)).val = (p t).val + 1 at hs
        rw [ih (by omega)] at hs
        exact hs
    refine ⟨hstates, ?_⟩
    intro t ht
    have hs := (hp.2.2 t ht).2
    change x t = w (p t).val at hs
    simpa [hstates t (by omega)] using hs
  refine ⟨n + 1, step, start, final, ?_, ?_⟩
  · let p : ℕ → Fin (n + 1) := fun t => ⟨min t n, by omega⟩
    refine ⟨p, ?_, ?_, ?_⟩
    · apply Fin.ext; simp [p, start]
    · simp [p, final]
    · intro t ht
      change min (t + 1) n = min t n + 1 ∧ w t = w (min t n)
      simp [Nat.min_eq_left (by omega : t ≤ n), Nat.min_eq_left (by omega : t + 1 ≤ n)]
  · intro x p y q hp hq
    obtain ⟨hps, hpw⟩ := shape x p hp
    obtain ⟨hqs, hqw⟩ := shape y q hq
    refine ⟨?_, ?_⟩
    · intro t ht
      exact (hpw t ht).trans (hqw t ht).symm
    · intro t ht
      apply Fin.ext
      exact (hps t ht).trans (hqs t ht).symm

end AneVsAn.BinarySeparation
