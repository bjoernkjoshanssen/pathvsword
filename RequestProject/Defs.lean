import RequestProject.ProofImports

/-!
# Definitions: words, NFAs, exact and unique nondeterministic automatic complexity

This file formalizes the basic notions of the paper
*"Exact beats unique infinitely often: a separation of nondeterministic automatic
complexities"* (file `anevsanseparationv4.tex`).

It contains:

* the alphabet `Ltr` and the words `zw k` of Theorem 1.2 (`thm:main`);
* NFAs (single start state, no `ε`-transitions), runs, accepting runs;
* *exact acceptance* and *unique acceptance* (Definition 1.1, `def:complexities`);
* the complexities `ANe` and `AN` (Definition 1.1, `def:complexities`).
-/

namespace AneVsAn

set_option autoImplicit false

/-- The alphabet used in the paper: the letters `a 1, a 2, …`, together with `b`, `c`, `d`, `e`.
In the notation of `anevsanseparationv4.tex` these are the letters of
`Σ_k = {a_1,…,a_k, b, c, d, e}` (Theorem 1.2, `thm:main`). -/
inductive Ltr where
  | a : ℕ → Ltr
  | b : Ltr
  | c : Ltr
  | d : Ltr
  | e : Ltr
deriving DecidableEq, Repr

/-- The length `n = 3k+7` of the word `z_k` of Theorem 1.2 (`thm:main`). -/
def wlen (k : ℕ) : ℕ := 3 * k + 7

/-- The word
`z_k = a_1 a_2 ⋯ a_k b^{k+5} c a_1 a_2 ⋯ a_{k-1} d e`
of Theorem 1.2 (`thm:main`), presented as the function assigning to a position
`t < 3k+7` the letter of `z_k` at that position.  Positions `≥ 3k+7` are irrelevant. -/
def zw (k : ℕ) (t : ℕ) : Ltr :=
  if t < k then Ltr.a (t + 1)
  else if t < 2 * k + 5 then Ltr.b
  else if t = 2 * k + 5 then Ltr.c
  else if t < 3 * k + 5 then Ltr.a (t - (2 * k + 5))
  else if t = 3 * k + 5 then Ltr.d
  else Ltr.e

/-!
### Evaluation lemmas for `zw`

These record the letter of `z_k` at each position, as described in Section 2
(`sec:prelim`) of `anevsanseparationv4.tex`:
the prefix positions `[0,k-1]` carry `a_1,…,a_k`, the run window positions `[k,2k+4]`
carry `b`, position `2k+5` carries `c`, the tail positions `[2k+6,3k+4]` carry
`a_1,…,a_{k-1}`, position `3k+5` carries `d` and position `3k+6` carries `e`.
-/

theorem zw_a {k t : ℕ} (h : t < k) : zw k t = Ltr.a (t + 1) := by
  simp only [zw, if_pos h]

theorem zw_b {k t : ℕ} (h1 : k ≤ t) (h2 : t < 2 * k + 5) : zw k t = Ltr.b := by
  simp only [zw, if_neg (by omega : ¬ t < k), if_pos h2]

theorem zw_c {k t : ℕ} (h : t = 2 * k + 5) : zw k t = Ltr.c := by
  subst h
  simp only [zw, if_neg (by omega : ¬ (2 * k + 5 : ℕ) < k),
    if_neg (by omega : ¬ (2 * k + 5 : ℕ) < 2 * k + 5)]
  rfl

theorem zw_a' {k t : ℕ} (h1 : 2 * k + 6 ≤ t) (h2 : t < 3 * k + 5) :
    zw k t = Ltr.a (t - (2 * k + 5)) := by
  simp only [zw, if_neg (by omega : ¬ t < k), if_neg (by omega : ¬ t < 2 * k + 5),
    if_neg (by omega : ¬ t = 2 * k + 5), if_pos h2]

theorem zw_d {k t : ℕ} (hk : 1 ≤ k) (h : t = 3 * k + 5) : zw k t = Ltr.d := by
  subst h
  simp only [zw, if_neg (by omega : ¬ (3 * k + 5 : ℕ) < k),
    if_neg (by omega : ¬ (3 * k + 5 : ℕ) < 2 * k + 5),
    if_neg (by omega : ¬ (3 * k + 5 : ℕ) = 2 * k + 5),
    if_neg (by omega : ¬ (3 * k + 5 : ℕ) < 3 * k + 5)]
  rfl

theorem zw_e {k t : ℕ} (h : t = 3 * k + 6) : zw k t = Ltr.e := by
  subst h
  simp only [zw, if_neg (by omega : ¬ (3 * k + 6 : ℕ) < k),
    if_neg (by omega : ¬ (3 * k + 6 : ℕ) < 2 * k + 5),
    if_neg (by omega : ¬ (3 * k + 6 : ℕ) = 2 * k + 5),
    if_neg (by omega : ¬ (3 * k + 6 : ℕ) < 3 * k + 5),
    if_neg (by omega : ¬ (3 * k + 6 : ℕ) = 3 * k + 5)]

section NFA

-- The alphabet is an arbitrary type `Λ`; for Theorem 1.2 it is `Ltr`, and for the
-- binary examples it is `Bool`.
variable {Λ S : Type}

/-- `IsRun step n x p` says that `p 0, p 1, …, p n` is a path of length `n`
of the transition relation `step`, spelling the word `x 0 ⋯ x (n-1)`.
This is the notion of *path* of Section 2 (`sec:prelim`) of the source. -/
def IsRun (step : S → Λ → S → Prop) (n : ℕ) (x : ℕ → Λ) (p : ℕ → S) : Prop :=
  ∀ t, t < n → step (p t) (x t) (p (t + 1))

/-- `IsAcc step st acc n x p` says that `p` is an *accepting path* of length `n`
spelling `x`: it starts at the start state `st` and ends in an accepting state.
(Section 2, `sec:prelim`.) -/
def IsAcc (step : S → Λ → S → Prop) (st : S) (acc : S → Prop)
    (n : ℕ) (x : ℕ → Λ) (p : ℕ → S) : Prop :=
  p 0 = st ∧ acc (p n) ∧ IsRun step n x p

/-- *Exact acceptance* (Definition 1.1, `def:complexities`): the NFA accepts `w`
and `L(M) ∩ Σ^n = {w}`, i.e. every accepted word of length `n` equals `w`. -/
def ExactlyAccepts (step : S → Λ → S → Prop) (st : S) (acc : S → Prop)
    (n : ℕ) (w : ℕ → Λ) : Prop :=
  (∃ p, IsAcc step st acc n w p) ∧
    ∀ x p, IsAcc step st acc n x p → ∀ t, t < n → x t = w t

/-- *Unique acceptance* (Definition 1.1, `def:complexities`): the NFA accepts `w`,
and it has exactly one accepting computation path of length `n` (in particular it
exactly accepts `w`).  Two accepting paths are identified when they visit the same
states and read the same letters. -/
def UniquelyAccepts (step : S → Λ → S → Prop) (st : S) (acc : S → Prop)
    (n : ℕ) (w : ℕ → Λ) : Prop :=
  (∃ p, IsAcc step st acc n w p) ∧
    ∀ x p y q, IsAcc step st acc n x p → IsAcc step st acc n y q →
      (∀ t, t < n → x t = y t) ∧ (∀ t, t ≤ n → p t = q t)

/-- Unique acceptance implies exact acceptance; this is the remark
"`ANe(w) ≤ AN(w)` for every `w`" following Definition 1.1 (`def:complexities`). -/
theorem ExactlyAccepts.of_uniquelyAccepts {step : S → Λ → S → Prop} {st : S}
    {acc : S → Prop} {n : ℕ} {w : ℕ → Λ}
    (h : UniquelyAccepts step st acc n w) : ExactlyAccepts step st acc n w := by
  obtain ⟨⟨p0, hp0⟩, huniq⟩ := h
  refine ⟨⟨p0, hp0⟩, ?_⟩
  intro x p hp t ht
  exact (huniq x p w p0 hp hp0).1 t ht

end NFA

/-- The set of numbers of states of NFAs exactly accepting `w` (as a word of length `n`).
Without loss of generality the state set is `Fin q`. -/
def ExactSizes {Λ : Type} (n : ℕ) (w : ℕ → Λ) : Set ℕ :=
  {q | ∃ (step : Fin q → Λ → Fin q → Prop) (st : Fin q) (acc : Fin q → Prop),
    ExactlyAccepts step st acc n w}

/-- The set of numbers of states of NFAs uniquely accepting `w` (as a word of length `n`). -/
def UniqueSizes {Λ : Type} (n : ℕ) (w : ℕ → Λ) : Set ℕ :=
  {q | ∃ (step : Fin q → Λ → Fin q → Prop) (st : Fin q) (acc : Fin q → Prop),
    UniquelyAccepts step st acc n w}

/-- The *exact nondeterministic automatic complexity* `A_{Ne}(w)` of Definition 1.1
(`def:complexities`): the least number of states of an NFA exactly accepting `w`. -/
noncomputable def ANe {Λ : Type} (n : ℕ) (w : ℕ → Λ) : ℕ := sInf (ExactSizes n w)

/-- The *unique nondeterministic automatic complexity* `A_N(w)` of Definition 1.1
(`def:complexities`): the least number of states of an NFA uniquely accepting `w`. -/
noncomputable def AN {Λ : Type} (n : ℕ) (w : ℕ → Λ) : ℕ := sInf (UniqueSizes n w)

theorem ANe_le {Λ : Type} {n : ℕ} {w : ℕ → Λ} {q : ℕ} (h : q ∈ ExactSizes n w) : ANe n w ≤ q :=
  Nat.sInf_le h

theorem AN_le {Λ : Type} {n : ℕ} {w : ℕ → Λ} {q : ℕ} (h : q ∈ UniqueSizes n w) : AN n w ≤ q :=
  Nat.sInf_le h

/-- Lower bounds for `A_{Ne}` (Definition 1.1, `def:complexities`): if every NFA that
exactly accepts `w` has at least `N` states, and at least one such NFA exists, then
`N ≤ A_{Ne}(w)`. -/
theorem le_ANe {Λ : Type} {n : ℕ} {w : ℕ → Λ} {N : ℕ} (h : ∀ q ∈ ExactSizes n w, N ≤ q)
    (hne : (ExactSizes n w).Nonempty) : N ≤ ANe n w := by
  obtain ⟨q, hq⟩ := hne
  exact h _ (Nat.sInf_mem ⟨q, hq⟩)

theorem le_AN {Λ : Type} {n : ℕ} {w : ℕ → Λ} {N : ℕ} (h : ∀ q ∈ UniqueSizes n w, N ≤ q)
    (hne : (UniqueSizes n w).Nonempty) : N ≤ AN n w := by
  obtain ⟨q, hq⟩ := hne
  have : sInf (UniqueSizes n w) ∈ UniqueSizes n w := Nat.sInf_mem ⟨q, hq⟩
  exact h _ this

end AneVsAn
