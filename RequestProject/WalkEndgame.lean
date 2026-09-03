import RequestProject.WalkOffCycle
import RequestProject.WalkChordPair
import RequestProject.WalkEll2Bridge

/-!
# The endgame: from the cycle `γ` to the contradiction (Sections 5.2, 5.4–5.6 and 6 of
`anevsanseparationv4.tex`)

This file contains the part of the proof of the lower bound that turns the cycle `γ` into
a contradiction.  It consists of

* the structure `GammaData`, which packages the conclusions of Lemma 5.3 (`lem:gamma`)
  about the cycle `γ`, its stretch `S`, and the associated bookkeeping quantities
  `ℓ, α, ω, t, r_off, d₀, x₁, b₁, s₀`;
* the *assembly* results, which are fully proved here: the maximality half of Step 1 of
  Lemma 5.3 (`exists_maximal_Stretch`, together with the primitivity lemma
  `no_repeat_in_period`), the parity `b₁ ≡ s₀ (mod 2)` of `eq:count`, the arithmetic of
  Corollary 6.2 (`cor:shapes`), and the reduction of the case `k ≥ 18` of the lower bound
  to the four endgame propositions;
* the *leaf statements*, each corresponding to one clearly delimited piece of the source
  and each proved either here or in the file named in its docstring.

There is no `sorry` in this file; the only remaining `sorry` of the development is the
finite search `base_search` of `RequestProject/WalkBase.lean`.  The leaves are:

* `gamma_offCycle_count` — Steps 2, 4 and 5 of Lemma 5.3 (`lem:gamma`) ("no second
  cycle", the bound on `d₀` and `x_e = 0`), in the form of the two bookkeeping identities
  `eq:dzero`;
* `aligned_nonempty` — Lemma 5.11 (`lem:Inonempty`);
* `bridgeCount_eq_zero_of_ell_one` — the last sentence of Lemma 5.13 (`lem:bridgeparity`);
* `bridgeCount_le_one_of_ell_two` — Lemma 5.14(a) (`lem:twoodd`);
* `ell_one_impossible` — Proposition 6.3 (`prop:ell1`);
* `ell_four_impossible` — Proposition 6.5 (`prop:ell4`);
* `ell_two_clean_impossible` — Proposition 6.7 (`prop:ell2clean`);
* `ell_two_bridge_impossible` — Proposition 6.8 (`prop:ell2bridge`).
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

/-- The data produced by Lemma 5.3 (`lem:gamma`) of `anevsanseparationv4.tex`: the cycle
`γ` (recorded through its stretch `S = [p,q] = [k+α, 2k+5-ω]`, on which the walk is
`ℓ`-periodic), together with

* `hell4` : `ℓ ≤ |𝒜| ≤ 4` (Step 1);
* `htt3`  : `t ≥ 3` (Step 1);
* `hroff` : `0 ≤ r_off < ℓ` (definition of `r_off`);
* `hmax`  : every visit of a `γ`-state is a time of `S` (the maximality of `S`, Step 1(i));
* `hdist` : the `ℓ` states of one period of `γ` are distinct (the primitivity of `γ`,
  Step 1);
* `hd0`   : `d₀ = x₁ + b₁ + r_off` (the first identity of `eq:dzero`, i.e. Steps 2, 4
  and 5);
* `hbudget` : `ℓ + x₁ + (b₁+s₀)/2 ≤ 4` (the second identity of `eq:dzero`, the budget
  `eq:budget` combined with `|𝒜| = ℓ + x₁`). -/
structure GammaData (k : ℕ) (c : ℕ → S) where
  /-- the cycle `γ` and its stretch `S`, with the periodicity of Lemma 5.3(i) -/
  Str : Stretch k c
  /-- `ℓ ≤ 4` -/
  hell4 : Str.ell ≤ 4
  /-- the stretch contains at least three full turns of `γ` -/
  htt3 : 3 ≤ Str.tt
  /-- `r_off < ℓ` -/
  hroff : Str.roff < Str.ell
  /-- every visit of a `γ`-state is a time of the stretch (maximality of `S`) -/
  hmax : ∀ u, u ≤ 3 * k + 7 →
    (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) → Str.p ≤ u ∧ u ≤ Str.q
  /-- the cycle `γ` is simple: one period carries `ℓ` distinct states -/
  hdist : ∀ a b, Str.p ≤ a → a < b → b < Str.p + Str.ell → c a ≠ c b
  /-- `d₀ = x₁ + b₁ + r_off` -/
  hd0 : Str.d0 = offCycleCard Str + bridgeCount k c + Str.roff
  /-- `2ℓ + 2x₁ + b₁ + s₀ ≤ 8` -/
  hbudget : 2 * (Str.ell + offCycleCard Str) + bridgeCount k c + singleCount k c ≤ 8

/-!
### The leaves coming from Section 5.2 (`lem:gamma`)
-/

omit [DecidableEq S] in
/-- No state occurs twice on one period of the cycle `γ`: this is the primitivity
argument of Step 1 of Lemma 5.3 (`lem:gamma`).  If the walk is `ℓ`-periodic on `[ps,qs]`
with `ℓ` minimal on the subinterval `[p,q]`, then two times `a < b < a+ℓ` of `[ps,qs]`
carry distinct states. -/
theorem no_repeat_in_period (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {ell ps qs p q a b : ℕ} (hell : 1 ≤ ell) (hps : ps ≤ p) (hqq : q ≤ qs)
    (hpq : p + 4 * ell ≤ q) (hqn : qs ≤ 3 * k + 7)
    (hper : ∀ x, ps ≤ x → x + ell ≤ qs → c x = c (x + ell))
    (hmin : ∀ d, 1 ≤ d → d < ell → ¬ (∀ x, p ≤ x → x + d ≤ q → c x = c (x + d)))
    (ha : ps ≤ a) (hab : a < b) (hb : b < a + ell) (hbq : b ≤ qs) (hcab : c a = c b) :
    False := by
  have hmod : (a - ps) % ell < ell := Nat.mod_lt _ (by omega)
  have hdm : ell * ((a - ps) / ell) + (a - ps) % ell = a - ps := Nat.div_add_mod _ _
  have haa' : ps + (a - ps) % ell + (a - ps) / ell * ell = a := by
    rw [Nat.mul_comm]; omega
  have h1 : c (ps + (a - ps) % ell) = c a := by
    have h := period_iter hper ((a - ps) / ell) (ps + (a - ps) % ell) (by omega) (by omega)
    rwa [haa'] at h
  have h2 : c (ps + (a - ps) % ell + (b - a)) = c b := by
    have h := period_iter hper ((a - ps) / ell) (ps + (a - ps) % ell + (b - a))
      (by omega) (by omega)
    rwa [show ps + (a - ps) % ell + (b - a) + (a - ps) / ell * ell = b by omega] at h
  have hx₀ : c (ps + (a - ps) % ell) = c (ps + (a - ps) % ell + (b - a)) :=
    h1.trans (hcab.trans h2.symm)
  have hrefine := period_refine (k := k) (by omega) huaw (t₁ := ps) (tr := qs) (d := ell)
    (e := b - a) (x₀ := ps + (a - ps) % ell) (by omega) (by omega) (by omega) (by omega)
    hper (by omega) (by omega) hx₀
  exact hmin (b - a) (by omega) (by omega) fun x hx hxq => hrefine x (by omega) (by omega)

/-- **Step 1 of Lemma 5.3 (`lem:gamma`), maximality half.**  The stretch of
`exists_Stretch` may be chosen *maximal*: every visit of a state of `γ` is then a time of
the stretch.  (The existence of a stretch with `ℓ ≤ 4` and at least four full turns is
`exists_Stretch`; the maximality argument of the second paragraph of Step 1 is carried
out here, using the Two-visit Lemma 4.5, `lem:twovisit`, in the form `equal_gaps` and
`twovisit_run`, and the Rotation Lemma 4.2, `lem:rotation`.) -/
theorem exists_maximal_Stretch (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) :
    ∃ Str : Stretch k c, Str.ell ≤ 4 ∧ 3 ≤ Str.tt ∧ Str.roff < Str.ell ∧
      (∀ u, u ≤ 3 * k + 7 →
        (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) → Str.p ≤ u ∧ u ≤ Str.q) ∧
      ∀ a b, Str.p ≤ a → a < b → b < Str.p + Str.ell → c a ≠ c b := by
  classical
  obtain ⟨ell, p, q, hell, hkp, hq5, hpq, hper, hmin⟩ := exists_stretch_min hk huaw hcard
  have hell4 : ell ≤ 4 := ell_le_four hk huaw hcard hell hkp hq5 hpq hper hmin
  -- the maximal extension of the stretch to the left
  obtain ⟨ps, hkps, hpsp, hperps, hminps⟩ :
      ∃ ps, k ≤ ps ∧ ps ≤ p ∧ (∀ x, ps ≤ x → x + ell ≤ q → c x = c (x + ell)) ∧
        ∀ a, k ≤ a → a ≤ p → (∀ x, a ≤ x → x + ell ≤ q → c x = c (x + ell)) → ps ≤ a := by
    set L : Finset ℕ := (Finset.Icc k p).filter
      (fun a => ∀ x, a ≤ x → x + ell ≤ q → c x = c (x + ell)) with hLdef
    have hpL : p ∈ L := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hkp, le_rfl⟩, hper⟩
    have hmem := Finset.mem_filter.1 (L.min'_mem ⟨p, hpL⟩)
    obtain ⟨hIcc, hpe⟩ := hmem
    rw [Finset.mem_Icc] at hIcc
    exact ⟨L.min' ⟨p, hpL⟩, hIcc.1, hIcc.2, hpe, fun a h1 h2 h3 =>
      L.min'_le a (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h1, h2⟩, h3⟩)⟩
  -- the maximal extension of the stretch to the right
  obtain ⟨qs, hqqs, hqs5, hperqs, hmaxqs⟩ :
      ∃ qs, q ≤ qs ∧ qs ≤ 2 * k + 5 ∧ (∀ x, ps ≤ x → x + ell ≤ qs → c x = c (x + ell)) ∧
        ∀ b, q ≤ b → b ≤ 2 * k + 5 → (∀ x, ps ≤ x → x + ell ≤ b → c x = c (x + ell)) →
          b ≤ qs := by
    set R : Finset ℕ := (Finset.Icc q (2 * k + 5)).filter
      (fun b => ∀ x, ps ≤ x → x + ell ≤ b → c x = c (x + ell)) with hRdef
    have hqR : q ∈ R := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, hq5⟩, hperps⟩
    have hmem := Finset.mem_filter.1 (R.max'_mem ⟨q, hqR⟩)
    obtain ⟨hIcc, hqe⟩ := hmem
    rw [Finset.mem_Icc] at hIcc
    exact ⟨R.max' ⟨q, hqR⟩, hIcc.1, hIcc.2, hqe, fun b h1 h2 h3 =>
      R.le_max' b (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h1, h2⟩, h3⟩)⟩
  have hlen4 : ps + 4 * ell ≤ qs := by omega
  have hqsn : qs ≤ 3 * k + 7 := by omega
  have hdm : ps + (qs - ps) / ell * ell + (qs - ps) % ell = qs := by
    have h := Nat.div_add_mod (qs - ps) ell
    rw [Nat.mul_comm] at h
    omega
  have htt4 : 4 ≤ (qs - ps) / ell := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hroff : (qs - ps) % ell < ell := Nat.mod_lt _ (by omega)
  have htt3 : 3 ≤ (qs - ps) / ell := by omega
  -- maximality: every visit of a `γ`-state is a time of the stretch
  have key : ∀ u, u ≤ 3 * k + 7 → (∃ x, ps ≤ x ∧ x < ps + ell ∧ c x = c u) →
      ps ≤ u ∧ u ≤ qs := by
    rintro u hun ⟨x, hx1, hx2, hxu⟩
    constructor
    · -- a visit before the stretch would extend the periodicity to the left
      by_contra hcon
      push_neg at hcon
      -- the last visit `v` of `c x` before `x`
      set V : Finset ℕ := (Finset.range x).filter (fun w => c w = c x) with hVdef
      have huV : u ∈ V := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hxu.symm⟩
      obtain ⟨hvr, hvc⟩ := Finset.mem_filter.1 (V.max'_mem ⟨u, huV⟩)
      rw [Finset.mem_range] at hvr
      set v := V.max' ⟨u, huV⟩ with hvdef
      have hvlast : ∀ w, v < w → w < x → c w ≠ c x := by
        intro w h1 h2 hcw
        have : w ∈ V := Finset.mem_filter.2 ⟨Finset.mem_range.2 h2, hcw⟩
        exact absurd (V.le_max' w this) (by omega)
      have hnext : c x = c (x + ell) := hperqs x hx1 (by omega)
      have hnomid : ∀ w, x < w → w < x + ell → c w ≠ c x := by
        intro w h1 h2 hcw
        exact no_repeat_in_period hk huaw hell hpsp hqqs hpq hqsn hperqs hmin hx1 h1 h2
          (by omega) hcw.symm
      have hgap := equal_gaps (by omega : 3 ≤ k) huaw (show v < x by omega)
        (show x < x + ell by omega) (by omega) hvc hnext
        (fun w h1 h2 hcw => hvlast w h1 h2 (hcw.trans hvc))
        (fun w h1 h2 hcw => hnomid w h1 h2 hcw)
      have hvr2 := twovisit_run (by omega : 3 ≤ k) huaw (show v < x by omega)
        (show x < x + ell by omega) (by omega) hvc hnext
      -- the walk is `ℓ`-periodic already from `v` on, contradicting the minimality of `ps`
      have hvx : v + ell = x := by omega
      have h1 : c v = c (v + ell) := by rw [hvx]; exact hvc
      have h2 : c (qs - ell) = c (qs - ell + ell) :=
        hperqs (qs - ell) (by omega) (by omega)
      have hrot := (rotation (by omega : 3 ≤ k) huaw (show v < qs - ell by omega) hell
        (by omega) h1 h2).2
      have : ps ≤ v := hminps v (by omega) (by omega)
        (fun y hy hyq => hrot y (by omega) (by omega))
      omega
    · -- a visit after the stretch would extend the periodicity to the right
      by_contra hcon
      push_neg at hcon
      -- the last visit `m` of `c x` inside the stretch
      set M : Finset ℕ := (Finset.Icc ps qs).filter (fun w => c w = c x) with hMdef
      have hxM : x ∈ M := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hx1, by omega⟩, rfl⟩
      obtain ⟨hmr, hmc⟩ := Finset.mem_filter.1 (M.max'_mem ⟨x, hxM⟩)
      rw [Finset.mem_Icc] at hmr
      set m := M.max' ⟨x, hxM⟩ with hmdef
      have hxm : x ≤ m := M.le_max' x hxM
      have hmlast : qs < m + ell := by
        by_contra hc2
        have : c (m + ell) = c x := (hperqs m hmr.1 (by omega)).symm.trans hmc
        have hmem : m + ell ∈ M :=
          Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, this⟩
        exact absurd (M.le_max' _ hmem) (by omega)
      have hmprev : c (m - ell) = c m := by
        have := hperqs (m - ell) (by omega) (by omega)
        rwa [show m - ell + ell = m by omega] at this
      have hnomid1 : ∀ w, m - ell < w → w < m → c w ≠ c (m - ell) := by
        intro w h1 h2 hcw
        exact no_repeat_in_period hk huaw hell hpsp hqqs hpq hqsn hperqs hmin
          (show ps ≤ m - ell by omega) h1 (by omega) (by omega) hcw.symm
      -- the first visit `w` of `c x` after the stretch
      set W : Finset ℕ := (Finset.Icc (m + 1) (3 * k + 7)).filter (fun w => c w = c x) with hWdef
      have huW : u ∈ W := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, hun⟩, hxu.symm⟩
      obtain ⟨hwr, hwc⟩ := Finset.mem_filter.1 (W.min'_mem ⟨u, huW⟩)
      rw [Finset.mem_Icc] at hwr
      set w := W.min' ⟨u, huW⟩ with hwdef
      have hnomid2 : ∀ y, m < y → y < w → c y ≠ c m := by
        intro y h1 h2 hcy
        have : y ∈ W := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩,
          hcy.trans hmc⟩
        exact absurd (W.min'_le y this) (by omega)
      have hgap := equal_gaps (by omega : 3 ≤ k) huaw (show m - ell < m by omega)
        (show m < w by omega) hwr.2 hmprev (hmc.trans hwc.symm) hnomid1 hnomid2
      have hvr2 := twovisit_run (by omega : 3 ≤ k) huaw (show m - ell < m by omega)
        (show m < w by omega) hwr.2 hmprev (hmc.trans hwc.symm)
      have hwm : w = m + ell := by omega
      have h1 : c ps = c (ps + ell) := hperqs ps le_rfl (by omega)
      have h2 : c m = c (m + ell) := by rw [← hwm]; exact hmc.trans hwc.symm
      have hrot := (rotation (by omega : 3 ≤ k) huaw (show ps < m by omega) hell
        (by omega) h1 h2).2
      have : m + ell ≤ qs := hmaxqs (m + ell) (by omega) (by omega)
        (fun y hy hyq => hrot y (by omega) (by omega))
      omega
  have hdist : ∀ a b, ps ≤ a → a < b → b < ps + ell → c a ≠ c b := by
    intro a b ha hab hb hcab
    exact no_repeat_in_period hk huaw hell hpsp hqqs hpq hqsn hperqs hmin ha hab
      (by omega) (by omega) hcab
  exact ⟨⟨ell, ps, qs, (qs - ps) / ell, (qs - ps) % ell, hell, hkps, hqs5,
    by omega, hdm, hperqs⟩, hell4, htt3, hroff, key, hdist⟩

/-- **Steps 2, 4 and 5 of Lemma 5.3 (`lem:gamma`)**, in the bookkeeping form `eq:dzero`.
Step 2 ("no second cycle") shows that every cluster state off `γ` is visited once or
twice and that the run times outside the stretch are exactly the visits of those states
together with the run visits of the bridges, whence `α + ω = x₁ + 2x_e + b₁`; Step 5 shows
`x_e = 0`; and the `ℓ` states of `γ` are `ℓ` distinct cluster states, so
`|𝒜| = ℓ + x₁` and the budget `eq:budget` takes the stated form.

The proof is carried out in `RequestProject/WalkOffCycle.lean` (`gamma_count`). -/
theorem gamma_offCycle_count (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) (Str : Stretch k c)
    (hell4 : Str.ell ≤ 4) (htt3 : 3 ≤ Str.tt) (hroff : Str.roff < Str.ell)
    (hmax : ∀ u, u ≤ 3 * k + 7 →
      (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) → Str.p ≤ u ∧ u ≤ Str.q)
    (hdist : ∀ a b, Str.p ≤ a → a < b → b < Str.p + Str.ell → c a ≠ c b) :
    Str.d0 = offCycleCard Str + bridgeCount k c + Str.roff ∧
      2 * (Str.ell + offCycleCard Str) + bridgeCount k c + singleCount k c ≤ 8 :=
  gamma_count hk huaw hcard Str hell4 htt3 hroff hmax hdist

/-- **Lemma 5.3 (`lem:gamma`)**, assembled: a uniquely accepting walk for `z_k`
(`k ≥ 18`) with at most `k+5` states carries the data of the cycle `γ`. -/
theorem exists_GammaData (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) : Nonempty (GammaData k c) := by
  obtain ⟨Str, hell4, htt3, hroff, hmax, hdist⟩ := exists_maximal_Stretch hk huaw hcard
  obtain ⟨hd0, hbudget⟩ := gamma_offCycle_count hk huaw hcard Str hell4 htt3 hroff hmax hdist
  exact ⟨⟨Str, hell4, htt3, hroff, hmax, hdist, hd0, hbudget⟩⟩

/-!
### The leaves coming from Sections 5.4 and 5.5
-/

/-- **Lemma 5.11 (`lem:Inonempty`)**: the set `I = {i ≤ k-1 : g_i = h_i}` of aligned
indices is nonempty.  The proof of the source counts the doubles: with no aligned chord
there are at most `3ℓ` wide chords (Lemma 5.7, `lem:wide`) and at most `ℓ-1` narrow
chords (Lemma 5.6, `lem:narrow`), so `f ≤ 4ℓ-1` and `2k+2 = 2f+b₁+s₀ ≤ 6ℓ+6 ≤ 30`,
contradicting `k ≥ 18`.  The proof is carried out in `RequestProject/WalkAligned.lean`
(`exists_aligned_index`); here it is only fed with the bookkeeping bounds of
`eq:dzero`. -/
theorem aligned_nonempty (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (G : GammaData k c) :
    ∃ i, i < k ∧ c i = c (2 * k + 6 + i) := by
  have hroff := G.hroff
  have hd0 := G.hd0
  have hbud := G.hbudget
  have hell := G.Str.hell
  exact exists_aligned_index hk huaw G.Str G.hell4 (by omega) (by omega)

/-- **Lemma 5.13 (Bridge parity, `lem:bridgeparity`)**, last sentence: for `ℓ = 1` every
bridge chord has length divisible by `ℓ`, so there are no bridges at all.  The proof is
carried out in `RequestProject/WalkBridgeParity.lean` (`no_bridge_of_ell_one`); here it is
only fed with the bookkeeping bounds of `eq:dzero`. -/
theorem bridgeCount_eq_zero_of_ell_one (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (G : GammaData k c) (hell : G.Str.ell = 1) : bridgeCount k c = 0 := by
  have hroff := G.hroff
  have hd0 := G.hd0
  have hbud := G.hbudget
  exact no_bridge_of_ell_one hk huaw G.Str hell (by omega) (by omega) G.hmax

/-- **Lemma 5.14(a) (Two odd chords, `lem:twoodd`)**: for `ℓ = 2` there is at most one
bridge.  By Lemma 5.13 (`lem:bridgeparity`) all bridge chords have odd length, and two
chords of odd length are removed by one of the candidate paths `π_A,…,π_D` of the
source, after a spin adjustment.

The proof is carried out in `RequestProject/WalkChordPair.lean`
(`bridgeCount_le_one_of_two`); here it is only fed with the bookkeeping bounds of
`eq:dzero`. -/
theorem bridgeCount_le_one_of_ell_two (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (G : GammaData k c) (hell : G.Str.ell = 2) : bridgeCount k c ≤ 1 := by
  have hroff := G.hroff
  have hd0 := G.hd0
  have hbud := G.hbudget
  exact bridgeCount_le_one_of_two hk huaw G.Str hell (by omega) (by omega) G.hmax

/-!
### The surviving shapes (Corollary 6.2, `cor:shapes`)
-/

/-- `b₁ ≡ s₀ (mod 2)`, as noted after `eq:count` in Section 5.1 (`sec:budget`). -/
theorem bridge_single_parity (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) :
    (bridgeCount k c + singleCount k c) % 2 = 0 := by
  have h1 := count_nonrun hk huaw
  have h2 := card_onceSet hk huaw
  omega

/-- **Corollary 6.2 (Surviving shapes, `cor:shapes`)**: combining the budget `eq:dzero`,
the Double passage Lemma 6.1 (`lem:dichotomy`), the parity `b₁ ≡ s₀ (mod 2)`, the
congruence `m = k+5 ≡ 2 (mod 3)` and the two bridge bounds, only three shapes survive:

* (a) `ℓ = 1`, `b₁ = s₀ = 0`, `x₁ = 3`, `d₀ = 3`;
* (b) `ℓ = 2`, `d₀ = 3`, `r_off = 1`, and either `(x₁,b₁,s₀) = (2,0,0)` (clean shape) or
  `(x₁,b₁,s₀) = (1,1,1)` (bridge shape);
* (c) `ℓ = 4`, `d₀ ∈ {1,3}`, `x₁ = b₁ = s₀ = 0`.

In particular `ℓ = 3` is impossible; this is the only place where `k ≡ 0 (mod 3)` is
used. -/
theorem shapes (hk : 18 ≤ k) (hk3 : k % 3 = 0) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (G : GammaData k c)
    {i : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i)) :
    (G.Str.ell = 1 ∧ bridgeCount k c = 0 ∧ singleCount k c = 0 ∧
        offCycleCard G.Str = 3 ∧ G.Str.d0 = 3) ∨
    (G.Str.ell = 2 ∧ G.Str.d0 = 3 ∧ G.Str.roff = 1 ∧
        ((offCycleCard G.Str = 2 ∧ bridgeCount k c = 0 ∧ singleCount k c = 0) ∨
          (offCycleCard G.Str = 1 ∧ bridgeCount k c = 1 ∧ singleCount k c = 1))) ∨
    (G.Str.ell = 4 ∧ (G.Str.d0 = 1 ∨ G.Str.d0 = 3) ∧ offCycleCard G.Str = 0 ∧
        bridgeCount k c = 0 ∧ singleCount k c = 0) := by
  have hdadd := G.Str.d0_add
  have hd := G.hd0
  have hbud := G.hbudget
  have hroff := G.hroff
  have hpar := bridge_single_parity (by omega : 3 ≤ k) huaw
  have hell1 := G.Str.hell
  have hell4 := G.hell4
  -- Lemma 6.1 (`lem:dichotomy`): `d₀ ≤ 2` and `ℓ ∣ 4 - 2d₀` is impossible
  have hdich : ∀ (_ : G.Str.d0 ≤ 2), ¬ (G.Str.ell ∣ (4 - 2 * G.Str.d0)) :=
    fun h hdvd => double_passage (by omega) huaw G.Str hik halign h hdvd
  rcases (by omega : G.Str.ell = 1 ∨ G.Str.ell = 2 ∨ G.Str.ell = 3 ∨ G.Str.ell = 4)
    with he | he | he | he
  · -- `ℓ = 1`
    have hb0 : bridgeCount k c = 0 := bridgeCount_eq_zero_of_ell_one hk huaw G he
    have hd3 : 3 ≤ G.Str.d0 := by
      by_contra hcon
      exact hdich (by omega) (by rw [he]; exact one_dvd _)
    exact Or.inl ⟨he, hb0, by omega, by omega, by omega⟩
  · -- `ℓ = 2`
    have hb1 : bridgeCount k c ≤ 1 := bridgeCount_le_one_of_ell_two hk huaw G he
    have hd3 : 3 ≤ G.Str.d0 := by
      by_contra hcon
      exact hdich (by omega) ⟨2 - G.Str.d0, by rw [he]; omega⟩
    rcases (by omega : bridgeCount k c = 0 ∨ bridgeCount k c = 1) with hb | hb
    · exact Or.inr (Or.inl ⟨he, by omega, by omega, Or.inl ⟨by omega, hb, by omega⟩⟩)
    · exact Or.inr (Or.inl ⟨he, by omega, by omega, Or.inr ⟨by omega, hb, by omega⟩⟩)
  · -- `ℓ = 3`: impossible, since `d₀ ≡ m ≡ 2 (mod 3)` while the budget forces `d₀ ≤ 4`
    exfalso
    have hd2 : G.Str.d0 ≠ 2 := by
      intro h2
      exact hdich (by omega) (by rw [he, h2]; decide)
    rw [he] at hdadd
    omega
  · -- `ℓ = 4`
    have hd0' : G.Str.d0 ≠ 0 := by
      intro h0
      exact hdich (by omega) (by rw [he, h0])
    have hd2' : G.Str.d0 ≠ 2 := by
      intro h2
      exact hdich (by omega) (by rw [he, h2]; decide)
    exact Or.inr (Or.inr ⟨he, by omega, by omega, by omega, by omega⟩)

/-!
### The four endgame propositions (Section 6 of `anevsanseparationv4.tex`)
-/

/-- **Proposition 6.3 (`prop:ell1`)**: the shape `ℓ = 1` is impossible.  In that shape
every chord of a double is excluded — narrow chords by Lemma 5.6(a) (`lem:narrow`),
`γ`- and `δ`-chords by Corollary 5.8 (`cor:foldloop`), `PU`-chords by Lemma 5.9
(`lem:lasso`) — while `u_1 = c_{3k+6}` must be a double.

The proof is given here, directly from those surgeries. -/
theorem ell_one_impossible (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (G : GammaData k c) {i : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i))
    (hell : G.Str.ell = 1) (hb : bridgeCount k c = 0) (hs : singleCount k c = 0)
    (hd : G.Str.d0 = 3) : False := by
  classical
  have hk3 : (3 : ℕ) ≤ k := by omega
  have hadd := G.Str.d0_add
  have hdvd1 : ∀ m : ℕ, G.Str.ell ∣ m := by intro m; rw [hell]; exact one_dvd _
  -- `u₁ = c_{3k+6}` is a double: it has a non-run visit, and `b₁ = s₀ = 0`
  have hu1st : c (3 * k + 6) ∈ states k c :=
    mem_states (k := k) (c := c) (t := 3 * k + 6) (by simp only [times, Finset.mem_range]; omega)
  have hnv : 3 * k + 6 ∈ nvis k c (c (3 * k + 6)) :=
    mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, rfl⟩
  have hcard2 : (nvis k c (c (3 * k + 6))).card = 2 := by
    have hle := nvis_card_le_two hk3 huaw (c (3 * k + 6))
    have hpos : 0 < (nvis k c (c (3 * k + 6))).card := Finset.card_pos.2 ⟨_, hnv⟩
    rcases (by omega : (nvis k c (c (3 * k + 6))).card = 1 ∨
      (nvis k c (c (3 * k + 6))).card = 2) with h | h
    · exfalso
      have hmemo : c (3 * k + 6) ∈ onceSet k c := Finset.mem_filter.2 ⟨hu1st, h⟩
      have hco := card_onceSet hk3 huaw
      have := Finset.card_pos.2 ⟨_, hmemo⟩
      omega
    · exact h
  have htw : c (3 * k + 6) ∈ twiceSet k c := Finset.mem_filter.2 ⟨hu1st, hcard2⟩
  obtain ⟨hlt, hlo, hhi, hhin, hclo, hchi⟩ := dbl_chord htw
  have hne : (nvis k c (c (3 * k + 6))).Nonempty := ⟨_, hnv⟩
  have hset : nvis k c (c (3 * k + 6))
      = {dblLo k c (c (3 * k + 6)), dblHi k c (c (3 * k + 6))} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with h | h <;> subst h
      exacts [dblLo_mem hne, dblHi_mem hne]
    · rw [hcard2, Finset.card_pair (by omega)]
  have hmem36 : 3 * k + 6 = dblLo k c (c (3 * k + 6)) ∨
      3 * k + 6 = dblHi k c (c (3 * k + 6)) := by
    have h := hnv
    rw [hset] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  rcases hmem36 with h36 | h36
  · -- the partner is `u₂`: the narrow tail chord `(3k+6, n)` of length `1`
    have hhi7 : dblHi k c (c (3 * k + 6)) = 3 * k + 7 := by omega
    refine narrow_tail_skip hk3 huaw G.Str (i := 3 * k + 6) (j := 3 * k + 7)
      (by omega) (by omega) (by omega) ?_ (hdvd1 _)
    rw [← hhi7, hchi]
  · -- the partner is the earlier visit `dblLo`
    rcases hlo with hj | hj
    · -- a `PU`-chord `g_j = u₁`
      have hchord : c (dblLo k c (c (3 * k + 6))) = c (3 * k + 6) := hclo
      rcases Nat.lt_trichotomy (dblLo k c (c (3 * k + 6))) i with h | h | h
      · exact lasso_u1 hk3 huaw G.Str h hik halign hchord (hdvd1 _) (by omega)
      · -- `j = i` would give a third non-run visit
        refine no_three_nvis hk3 huaw (x := dblLo k c (c (3 * k + 6)))
          (y := 2 * k + 6 + i) (z := 3 * k + 6) (dblLo_mem hne) ?_ hnv
          (by omega) (by omega) (by omega)
        exact mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, by rw [← halign, ← h]; exact hchord⟩
      · exact positions_PU hk3 huaw halign h hj (Or.inl rfl) hchord
    · -- a narrow tail chord `(2k+6+j', 3k+6)`
      refine narrow_tail_skip hk3 huaw G.Str (i := dblLo k c (c (3 * k + 6)))
        (j := 3 * k + 6) hj (by omega) (by omega) hclo (hdvd1 _)

/-- **Proposition 6.5 (`prop:ell4`)**: the shape `ℓ = 4` is impossible.  Step 1 of the
source shows that there is at most one narrow chord and that its length is `7` or `9`
(Lemma 5.6(b),(c),(d), `lem:narrow`, and Lemma 5.12, `lem:counts`); Step 2 counts the
loose visits by kind (`PP`, `TT`, `TU`, `PU`, `γ`, `δ`) and reaches a contradiction.

The proof is `ell4` of `RequestProject/WalkEll4.lean`. -/
theorem ell_four_impossible (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (G : GammaData k c)
    {i : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i))
    (hell : G.Str.ell = 4) (hd : G.Str.d0 = 1 ∨ G.Str.d0 = 3)
    (hb : bridgeCount k c = 0) (hs : singleCount k c = 0) : False :=
  ell4 hk huaw G.Str hell hd hb hs hik halign

/-- **Proposition 6.7 (`prop:ell2clean`)**: the clean shape `ℓ = 2`, `(x₁,b₁,s₀)=(2,0,0)`
is impossible.  By Lemma 6.6 (`lem:parity2`) the partner of `u_1` is a tail state, this is
the unique narrow chord, and the count of the loose visits forces `J_L = {0}`,
`J_R = {k-1}` and a `TU`-chord of length `1`, excluded by Lemma 5.6(b) (`lem:narrow`).

The proof is `ell2_clean` of `RequestProject/WalkEll2.lean`. -/
theorem ell_two_clean_impossible (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (G : GammaData k c)
    {i : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i))
    (hell : G.Str.ell = 2) (hd : G.Str.d0 = 3) (hb : bridgeCount k c = 0)
    (hs : singleCount k c = 0) : False :=
  ell2_clean hk huaw G.Str hell hd hb hs hik halign

/-- **Proposition 6.8 (`prop:ell2bridge`)**: the bridge shape `ℓ = 2`,
`(x₁,b₁,s₀)=(1,1,1)` is impossible.  Step 1 of the source shows that the unique bridge is
a tail bridge and that `r ≤ 1`; Steps 2 and 3 dispose of `r = 1` (Crossing Lemma 4.7,
`lem:cross`, and Lemma 6.6(b), `lem:parity2`) and of `r = 0` (an explicit second
accepting path with one or three `c`-edges).

The proof is `ell2_bridge` of `RequestProject/WalkEll2Bridge.lean`. -/
theorem ell_two_bridge_impossible (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (G : GammaData k c)
    {i : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i))
    (hell : G.Str.ell = 2) (hd : G.Str.d0 = 3) (hroff : G.Str.roff = 1)
    (hb : bridgeCount k c = 1) (hs : singleCount k c = 1) : False :=
  ell2_bridge hk huaw G.Str hell hd hroff hb hs G.hmax hik halign

/-!
### Conclusion for `k ≥ 18`
-/

/-- **Sections 5 and 6 of `anevsanseparationv4.tex`, conclusion**: for `k ≥ 18` with
`k ≡ 0 (mod 3)` there is no uniquely accepting walk for `z_k` with at most `k+5` states.
This is the assembly of Lemma 5.3 (`lem:gamma`), Lemma 5.11 (`lem:Inonempty`),
Corollary 6.2 (`cor:shapes`) and Propositions 6.3, 6.5, 6.7, 6.8. -/
theorem no_small_walk_large (hk : 18 ≤ k) (hk3 : k % 3 = 0)
    (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) : False := by
  obtain ⟨G⟩ := exists_GammaData hk huaw hcard
  obtain ⟨i, hik, halign⟩ := aligned_nonempty hk huaw G
  rcases shapes hk hk3 huaw G hik halign with
    ⟨he, hb, hs, hx, hd⟩ | ⟨he, hd, hr, hcl | hbr⟩ | ⟨he, hd, hx, hb, hs⟩
  · exact ell_one_impossible hk huaw G hik halign he hb hs hd
  · exact ell_two_clean_impossible hk huaw G hik halign he hd hcl.2.1 hcl.2.2
  · exact ell_two_bridge_impossible hk huaw G hik halign he hd hr hbr.2.1 hbr.2.2
  · exact ell_four_impossible hk huaw G hik halign he hd hb hs

end

end AneVsAn
