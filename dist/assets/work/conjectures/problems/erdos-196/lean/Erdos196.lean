/-!
Single-file submission for Erdős problem 196, COUNTEREXAMPLE mode.

Task: fc-8432eac9-erdos196-erdos-196-b7454f0edd-counterexample-v1
Pinned Formal Conjectures commit: 8432eac998110a563e03df65a28c117e97c8c142

The validator supplies the following trusted wrapper around this entire file:
  import FormalConjectures.ErdosProblems.«196»
  import TaskSupport
  namespace Bounty
  ... this file ...
  end Bounty

Every proof declaration is contained below. No supplementary proof files are needed.
The target is negated because this is a disproof of the affirmative statement.
-/

namespace Construction196

def LowEq (k a b : ℕ) : Prop :=
  ∀ i < k, a.testBit i = b.testBit i

def low (a k : ℕ) : Fin k → Bool := fun i => a.testBit i

lemma low_eq_iff {k a b : ℕ} : low a k = low b k ↔ LowEq k a b := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i i.isLt

lemma LowEq.symm {k a b : ℕ} (h : LowEq k a b) : LowEq k b a :=
  fun i hi => (h i hi).symm

lemma LowEq.trans {k a b c : ℕ} (h : LowEq k a b) (h' : LowEq k b c) :
    LowEq k a c := fun i hi => (h i hi).trans (h' i hi)

lemma LowEq.mono {k l a b : ℕ} (h : LowEq k a b) (hl : l ≤ k) :
    LowEq l a b := fun i hi => h i (lt_of_lt_of_le hi hl)

lemma bit0_eq_iff (a b : ℕ) : a.testBit 0 = b.testBit 0 ↔ a % 2 = b % 2 := by
  simp only [Nat.testBit_eq_decide_div_mod_eq, pow_zero, Nat.div_one,
    decide_eq_decide]
  omega

lemma ap_bit0 {a b c : ℕ} (h : a + c = 2 * b) : a.testBit 0 = c.testBit 0 := by
  rw [bit0_eq_iff]
  omega

lemma ap_div_two {a b c : ℕ} (h : a + c = 2 * b)
    (hab : a.testBit 0 = b.testBit 0) : a / 2 + c / 2 = 2 * (b / 2) := by
  have hac := ap_bit0 h
  rw [bit0_eq_iff] at hab hac
  omega

lemma ap_low {a b c k : ℕ} (h : a + c = 2 * b) (hl : LowEq k a b) :
    LowEq (k + 1) a c := by
  induction k generalizing a b c with
  | zero =>
      intro i hi
      have : i = 0 := by omega
      subst i
      exact ap_bit0 h
  | succ k ih =>
      have hab : a.testBit 0 = b.testBit 0 := hl 0 (by omega)
      have hdiv := ap_div_two h hab
      have hl' : LowEq k (a / 2) (b / 2) := by
        intro i hi
        simpa only [Nat.testBit_div_two] using hl (i + 1) (by omega)
      have hd := ih hdiv hl'
      intro i hi
      cases i with
      | zero => exact ap_bit0 h
      | succ i =>
          simpa only [Nat.testBit_div_two, Nat.succ_eq_add_one] using hd i (by omega)

lemma first_difference {a b : ℕ} (hne : a ≠ b) :
    ∃ k, LowEq k a b ∧ a.testBit k ≠ b.testBit k := by
  classical
  have hex : ∃ k, a.testBit k ≠ b.testBit k := by
    by_contra h
    push Not at h
    exact hne (Nat.eq_of_testBit_eq h)
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  intro i hi
  exact not_not.mp (Nat.find_min hex hi)

abbrev Preference := (k : ℕ) → (Fin k → Bool) → Bool

def key (e : Preference) (a k : ℕ) : Bool :=
  if a.testBit k = e k (low a k) then false else true

def code (e : Preference) (a : ℕ) : Lex (ℕ → Bool) :=
  toLex (key e a)

lemma key_eq_of_low {e : Preference} {a b k : ℕ} (h : LowEq k a b) :
    ∀ i < k, key e a i = key e b i := by
  intro i hi
  have hw : low a i = low b i := low_eq_iff.mpr (h.mono (Nat.le_of_lt hi))
  simp only [key, h i hi, hw]

lemma code_lt_of_split {e : Preference} {a b k : ℕ}
    (hl : LowEq k a b) (hne : a.testBit k ≠ b.testBit k)
    (hp : a.testBit k = e k (low a k)) : code e a < code e b := by
  change ∃ i, (∀ j, j < i → key e a j = key e b j) ∧ key e a i < key e b i
  refine ⟨k, key_eq_of_low hl, ?_⟩
  have hb : b.testBit k ≠ e k (low b k) := by
    rw [← low_eq_iff.mpr hl, ← hp]
    exact hne.symm
  simp [key, hp, hb]

lemma code_lt_iff_split {e : Preference} {a b k : ℕ}
    (hl : LowEq k a b) (hne : a.testBit k ≠ b.testBit k) :
    code e a < code e b ↔ a.testBit k = e k (low a k) := by
  constructor
  · intro hab
    by_contra hp
    have hb : b.testBit k = e k (low b k) := by
      rw [← low_eq_iff.mpr hl]
      cases ha : a.testBit k <;> cases hb : b.testBit k <;>
        cases he : e k (low a k) <;> simp_all
    exact lt_asymm hab (code_lt_of_split hl.symm hne.symm hb)
  · exact code_lt_of_split hl hne

lemma code_injective (e : Preference) : Function.Injective (code e) := by
  intro a b heq
  by_contra hne
  obtain ⟨k, hl, hd⟩ := first_difference hne
  have hk : key e a k = key e b k := congrFun heq k
  have hw := low_eq_iff.mpr hl
  simp only [key, hw] at hk
  cases ha : a.testBit k <;> cases hb : b.testBit k <;>
    cases hp : e k (low b k) <;> simp_all

lemma binary_no_three {e : Preference} {a b c : ℕ}
    (hab : code e a < code e b) (hbc : code e b < code e c)
    (hap : a + c = 2 * b) : False := by
  have hne : a ≠ b := fun h => (ne_of_lt hab) (congrArg (code e) h)
  obtain ⟨k, hl, hd⟩ := first_difference hne
  have hac := ap_low hap hl
  have hbit : a.testBit k = c.testBit k := hac k (by omega)
  have hlow : LowEq k b c := hl.symm.trans (hac.mono (by omega))
  have hdiff : b.testBit k ≠ c.testBit k := by rw [← hbit]; exact hd.symm
  have ha := (code_lt_iff_split hl hd).mp hab
  have hb := (code_lt_iff_split hlow hdiff).mp hbc
  rw [← low_eq_iff.mpr hl] at hb
  exact hd (ha.trans hb.symm)

def shortCode (e : Preference) (K a : ℕ) : Lex (Fin K → Bool) :=
  toLex (fun i => key e a i)

noncomputable def rank (e : Preference) (K a : ℕ) : ℕ :=
  ((Fintype.orderIsoFinOfCardEq (Lex (Fin K → Bool)) rfl).symm (shortCode e K a)).val

lemma rank_lt_of_split {e : Preference} {K a b k : ℕ} (hk : k < K)
    (hl : LowEq k a b) (hne : a.testBit k ≠ b.testBit k)
    (hp : a.testBit k = e k (low a k)) : rank e K a < rank e K b := by
  have hshort : shortCode e K a < shortCode e K b := by
    change ∃ i : Fin K, (∀ j, j < i → key e a j = key e b j) ∧
      key e a i < key e b i
    refine ⟨⟨k, hk⟩, fun j hj => key_eq_of_low hl j hj, ?_⟩
    have hb : b.testBit k ≠ e k (low b k) := by
      rw [← low_eq_iff.mpr hl, ← hp]
      exact hne.symm
    simp [key, hp, hb]
  exact (Fintype.orderIsoFinOfCardEq (Lex (Fin K → Bool)) rfl).symm.strictMono hshort

/-- The sublevel set of `2^(ρ n) * n` supplies a finite saturation. -/
lemma finite_saturation (ρ : ℕ → ℕ) (F : Finset ℕ) :
    ∃ A : Finset ℕ, F ⊆ A ∧
      ∀ a b, ρ a < ρ b → a ≤ 2 * b → b ∈ A → a ∈ A := by
  classical
  let w : ℕ → ℕ := fun n => 2 ^ ρ n * n
  have hn (n : ℕ) : n ≤ w n := by
    have hp : 0 < 2 ^ ρ n := by positivity
    dsimp [w]
    nlinarith
  have hm {a b : ℕ} (hr : ρ a < ρ b) (hab : a ≤ 2 * b) : w a ≤ w b := by
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.succ_le_of_lt hr)
    rw [pow_succ] at hp
    have h₁ := Nat.mul_le_mul_left (2 ^ ρ a) hab
    have h₂ := Nat.mul_le_mul_right b hp
    dsimp [w]
    nlinarith
  let M := F.sup w
  let A := (Finset.range (M + 1)).filter (fun n => w n ≤ M)
  refine ⟨A, ?_, ?_⟩
  · intro n hF
    have hw : w n ≤ M := Finset.le_sup hF
    have hnv := hn n
    simp only [A, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hw⟩
  · intro a b hr hab hb
    have hwb : w b ≤ M := (Finset.mem_filter.mp hb).2
    have hwa : w a ≤ M := (hm hr hab).trans hwb
    have hav := hn a
    simp only [A, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hwa⟩

def Branch (P : List ℕ) (k : ℕ) (w : Fin k → Bool) : Prop :=
  ∃ a ∈ P, ∃ b ∈ P, low a k = w ∧ low b k = w ∧ a.testBit k ≠ b.testBit k

lemma branches_bounded (P : List ℕ) : ∃ K, ∀ k w, Branch P k w → k < K := by
  let K := P.toFinset.sup id + 1
  refine ⟨K, ?_⟩
  intro k w ⟨a, ha, b, hb, _, _, hd⟩
  by_contra hk
  have ha' : a < K := Nat.lt_succ_of_le (Finset.le_sup (f := id) (List.mem_toFinset.mpr ha))
  have hb' : b < K := Nat.lt_succ_of_le (Finset.le_sup (f := id) (List.mem_toFinset.mpr hb))
  have hpow : k < 2 ^ k := Nat.lt_two_pow_self
  have hba := Nat.testBit_eq_false_of_lt (show a < 2 ^ k by omega)
  have hbb := Nat.testBit_eq_false_of_lt (show b < 2 ^ k by omega)
  exact hd (hba.trans hbb.symm)

def Before (P : List ℕ) (a b : ℕ) : Prop :=
  a ∈ P ∧ b ∈ P ∧ P.idxOf a < P.idxOf b

lemma Before.ne {P : List ℕ} {a b : ℕ} (h : Before P a b) : a ≠ b := by
  intro he
  subst b
  exact (lt_irrefl _) h.2.2

lemma Before.asymm {P : List ℕ} {a b : ℕ} (h : Before P a b)
    (h' : Before P b a) : False := lt_asymm h.2.2 h'.2.2

lemma before_append_old {P B : List ℕ} {a b : ℕ} (h : Before P a b) :
    Before (P ++ B) a b := by
  refine ⟨List.mem_append_left _ h.1, List.mem_append_left _ h.2.1, ?_⟩
  simpa only [List.idxOf_append, if_pos h.1, if_pos h.2.1] using h.2.2

lemma before_append_old_iff {P B : List ℕ} {a b : ℕ} (ha : a ∈ P) (hb : b ∈ P) :
    Before (P ++ B) a b ↔ Before P a b := by
  constructor
  · intro h
    refine ⟨ha, hb, ?_⟩
    simpa only [List.idxOf_append, if_pos ha, if_pos hb] using h.2.2
  · exact before_append_old

lemma old_of_before_old {P B : List ℕ} {a b : ℕ}
    (h : Before (P ++ B) a b) (hb : b ∈ P) : a ∈ P := by
  by_contra ha
  have hi := h.2.2
  simp only [List.idxOf_append, if_neg ha, if_pos hb] at hi
  have hj := List.idxOf_lt_length_iff.mpr hb
  omega

lemma before_append_new_iff {P B : List ℕ} {a b : ℕ} (ha : a ∉ P) (hb : b ∉ P) :
    Before (P ++ B) a b ↔ Before B a b := by
  simp [Before, List.idxOf_append, ha, hb]

lemma before_old_new {P B : List ℕ} {a b : ℕ} (ha : a ∈ P)
    (hb : b ∈ B) (hb' : b ∉ P) : Before (P ++ B) a b := by
  refine ⟨List.mem_append_left _ ha, List.mem_append_right _ hb, ?_⟩
  rw [List.idxOf_append, List.idxOf_append, if_pos ha, if_neg hb']
  have hi := List.idxOf_lt_length_iff.mpr ha
  omega

def Closed (P : List ℕ) : Prop :=
  ∀ a b c d, Before P a b → Before P b c →
    a + c = 2 * b → b + d = 2 * c → Before P d c

def Compatible (P : List ℕ) (e : Preference) : Prop :=
  ∀ a b c d k, Before P a b → a + c = 2 * b → b + d = 2 * c →
    c ∉ P → d ∉ P → LowEq k a b → a.testBit k ≠ b.testBit k →
    e k (low a k) = b.testBit k

def Good (P : List ℕ) : Prop := P.Nodup ∧ Closed P ∧ ∃ e, Compatible P e

noncomputable def adapt (P : List ℕ) (e : Preference) : Preference := by
  classical
  exact fun k w => if Branch P k w then e k w else
    decide (∃ a ∈ P, low a k = w ∧ a.testBit k = true)

lemma adapt_branch {P : List ℕ} {e : Preference} {k : ℕ} {w : Fin k → Bool}
    (h : Branch P k w) : adapt P e k w = e k w := by
  classical
  simp [adapt, h]

lemma adapt_old {P : List ℕ} {e : Preference} {k a : ℕ} {w : Fin k → Bool}
    (hn : ¬ Branch P k w) (ha : a ∈ P) (hw : low a k = w) :
    adapt P e k w = a.testBit k := by
  classical
  cases hv : a.testBit k with
  | false =>
      have he : ¬ ∃ b ∈ P, low b k = w ∧ b.testBit k = true := by
        rintro ⟨b, hb, hbw, hbv⟩
        apply hn
        exact ⟨a, ha, b, hb, hw, hbw, by simp [hv, hbv]⟩
      simp [adapt, hn, he]
  | true =>
      have he : ∃ b ∈ P, low b k = w ∧ b.testBit k = true := ⟨a, ha, hw, hv⟩
      simp [adapt, hn, he]

lemma adapt_compatible {P : List ℕ} {e : Preference} (h : Compatible P e) :
    Compatible P (adapt P e) := by
  intro a b c d k hab h₁ h₂ hc hd hl hbit
  have hbr : Branch P k (low a k) :=
    ⟨a, hab.1, b, hab.2.1, rfl, (low_eq_iff.mpr hl).symm, hbit⟩
  rw [adapt_branch hbr]
  exact h a b c d k hab h₁ h₂ hc hd hl hbit

def Saturated (P : List ℕ) (e : Preference) (A : Finset ℕ) : Prop :=
  ∀ k w a b, Branch P k w → low a k = w → low b k = w →
    a.testBit k = e k w → b.testBit k ≠ e k w → a ≤ 2 * b → b ∈ A → a ∈ A

lemma saturated_exists (P : List ℕ) (e : Preference) (F : Finset ℕ) :
    ∃ A : Finset ℕ, F ⊆ A ∧ Saturated P e A := by
  obtain ⟨K, hK⟩ := branches_bounded P
  obtain ⟨A, hF, hA⟩ := finite_saturation (rank e K) F
  refine ⟨A, hF, ?_⟩
  intro k w a b hbr ha hb hpa hpb hab hmem
  apply hA a b _ hab hmem
  apply rank_lt_of_split (hK k w hbr) (low_eq_iff.mp (ha.trans hb.symm))
  · intro he
    exact hpb (he.symm.trans hpa)
  · simpa only [ha] using hpa

lemma sorted_block (e : Preference) (P : List ℕ) (A : Finset ℕ) :
    ∃ B : List ℕ, B.Nodup ∧ (∀ x, x ∈ B ↔ x ∈ A ∧ x ∉ P) ∧
      ∀ a b, Before B a b → code e a < code e b := by
  classical
  let r : ℕ → ℕ → Prop := fun a b => code e a ≤ code e b
  let : IsTrans ℕ r := ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩
  let : Std.Antisymm r := ⟨fun _ _ h₁ h₂ => code_injective e (le_antisymm h₁ h₂)⟩
  let : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  let B := (A \ P.toFinset).sort r
  refine ⟨B, Finset.sort_nodup _ _, ?_, ?_⟩
  · intro x
    simp [B]
  · intro a b hab
    have hi := List.idxOf_lt_length_iff.mpr hab.1
    have hj := List.idxOf_lt_length_iff.mpr hab.2.1
    have hp := List.pairwise_iff_getElem.mp (Finset.pairwise_sort (A \ P.toFinset) r)
      (B.idxOf a) (B.idxOf b) hi hj hab.2.2
    have ha := List.getElem_idxOf hi
    have hb := List.getElem_idxOf hj
    change code e (B[B.idxOf a]) ≤ code e (B[B.idxOf b]) at hp
    rw [ha, hb] at hp
    exact lt_of_le_of_ne hp (fun h => hab.ne (code_injective e h))

lemma before_of_code {e : Preference} {B : List ℕ} {a b : ℕ}
    (ho : ∀ x y, Before B x y → code e x < code e y)
    (ha : a ∈ B) (hb : b ∈ B) (h : code e a < code e b) : Before B a b := by
  refine ⟨ha, hb, ?_⟩
  rcases lt_trichotomy (B.idxOf a) (B.idxOf b) with hi | hi | hi
  · exact hi
  · have hva := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr ha)
    have hvb := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hb)
    have hab : a = b := by
      have hva' : B[B.idxOf b]'(List.idxOf_lt_length_iff.mpr hb) = a := by
        simpa only [hi] using hva
      exact hva'.symm.trans hvb
    exact False.elim ((ne_of_lt h) (congrArg (code e) hab))
  · exact False.elim (lt_asymm h (ho b a ⟨hb, ha, hi⟩))

lemma progression_bits {a b c d k : ℕ} (h₁ : a + c = 2 * b)
    (h₂ : b + d = 2 * c) (hl : LowEq k a b) :
    low b k = low a k ∧ low c k = low a k ∧ low d k = low a k ∧
      c.testBit k = a.testBit k ∧ d.testBit k = b.testBit k := by
  have hac := ap_low h₁ hl
  have hbc := hl.symm.trans (hac.mono (Nat.le_succ k))
  have hbd := ap_low h₂ hbc
  refine ⟨(low_eq_iff.mpr hl).symm,
    (low_eq_iff.mpr (hac.mono (Nat.le_succ k))).symm,
    (low_eq_iff.mpr (hbd.mono (Nat.le_succ k))).symm.trans (low_eq_iff.mpr hl).symm,
    (hac k (Nat.lt_succ_self k)).symm, (hbd k (Nat.lt_succ_self k)).symm⟩

lemma extend_closed {P B : List ℕ} {e : Preference} {A : Finset ℕ}
    (hP : Closed P) (he : Compatible P e)
    (hae : ∀ k w a, ¬ Branch P k w → a ∈ P → low a k = w → e k w = a.testBit k)
    (hs : Saturated P e A)
    (hB : ∀ x, x ∈ B ↔ x ∈ A ∧ x ∉ P)
    (ho : ∀ a b, Before B a b → code e a < code e b) : Closed (P ++ B) := by
  intro a b c d hab hbc h₁ h₂
  by_cases hc : c ∈ P
  · have hb := old_of_before_old hbc hc
    have ha := old_of_before_old hab hb
    exact before_append_old (hP a b c d
      ((before_append_old_iff ha hb).mp hab) ((before_append_old_iff hb hc).mp hbc) h₁ h₂)
  have hcm : c ∈ B := (List.mem_append.mp hbc.2.1).resolve_left hc
  have hcA : c ∈ A := ((hB c).mp hcm).1
  by_cases hd : d ∈ P
  · exact before_old_new hd hcm hc
  have finish (k : ℕ) (hl : LowEq k a b) (hbit : a.testBit k ≠ b.testBit k)
      (hbr : Branch P k (low a k)) (hp : b.testBit k = e k (low a k)) :
      Before (P ++ B) d c := by
    obtain ⟨hwb, hwc, hwd, hcb, hdb⟩ := progression_bits h₁ h₂ hl
    have hdA : d ∈ A := hs k (low a k) d c hbr hwd hwc
      (hdb.trans hp) (by rw [hcb, ← hp]; exact hbit) (by omega) hcA
    have hdm : d ∈ B := (hB d).mpr ⟨hdA, hd⟩
    have hdc : code e d < code e c := by
      apply code_lt_of_split (low_eq_iff.mp (hwd.trans hwc.symm))
      · rw [hdb, hcb]
        exact hbit.symm
      · simpa only [hwd] using hdb.trans hp
    exact (before_append_new_iff hd hc).mpr (before_of_code ho hdm hcm hdc)
  obtain ⟨k, hl, hbit⟩ := first_difference hab.ne
  by_cases hb : b ∈ P
  · have ha := old_of_before_old hab hb
    apply finish k hl hbit
    · exact ⟨a, ha, b, hb, rfl, (low_eq_iff.mpr hl).symm, hbit⟩
    · exact (he a b c d k ((before_append_old_iff ha hb).mp hab) h₁ h₂ hc hd hl hbit).symm
  have hbcT := ho b c ((before_append_new_iff hb hc).mp hbc)
  by_cases ha : a ∈ P
  · obtain ⟨hwb, hwc, _, hcb, _⟩ := progression_bits h₁ h₂ hl
    have hlbc : LowEq k b c := low_eq_iff.mp (hwb.trans hwc.symm)
    have hbitbc : b.testBit k ≠ c.testBit k := by rw [hcb]; exact hbit.symm
    have hp : b.testBit k = e k (low a k) := by
      simpa only [hwb] using (code_lt_iff_split hlbc hbitbc).mp hbcT
    apply finish k hl hbit _ hp
    by_contra hbr
    have hpa := hae k (low a k) a hbr ha rfl
    exact hbit (hpa.symm.trans hp.symm)
  · exact False.elim (binary_no_three
      (ho a b ((before_append_new_iff ha hb).mp hab)) hbcT h₁)

lemma bool_other {x y z : Bool} (hxy : x ≠ y) (hyz : y ≠ z) : x = z := by
  cases x <;> cases y <;> cases z <;> simp_all

lemma bool_not_other {x y : Bool} (h : x ≠ y) : (!x) = y := by
  cases x <;> cases y <;> simp_all

noncomputable def nextPreference (P : List ℕ) (e : Preference) : Preference := by
  classical
  exact fun k w => if Branch P k w then e k w else !(e k w)

lemma extend_compatible {P B : List ℕ} {e : Preference} {A : Finset ℕ}
    (he : Compatible P e)
    (hae : ∀ k w a, ¬ Branch P k w → a ∈ P → low a k = w → e k w = a.testBit k)
    (hs : Saturated P e A)
    (hcover : ∀ x, x ∈ P ++ B ↔ x ∈ A)
    (ho : ∀ a b, Before B a b → code e a < code e b) :
    Compatible (P ++ B) (nextPreference P e) := by
  classical
  intro a b c d k hab h₁ h₂ hc hd hl hbit
  have hcP : c ∉ P := fun h => hc (List.mem_append_left _ h)
  have hdP : d ∉ P := fun h => hd (List.mem_append_left _ h)
  by_cases hbr : Branch P k (low a k)
  · simp only [nextPreference, if_pos hbr]
    by_cases hb : b ∈ P
    · have ha := old_of_before_old hab hb
      exact he a b c d k ((before_append_old_iff ha hb).mp hab) h₁ h₂ hcP hdP hl hbit
    · by_contra hp
      have hpa : a.testBit k = e k (low a k) := bool_other hbit (Ne.symm hp)
      obtain ⟨hwb, hwc, _, hcb, _⟩ := progression_bits h₁ h₂ hl
      have hbA : b ∈ A := (hcover b).mp hab.2.1
      have hcA : c ∈ A := hs k (low a k) c b hbr hwc hwb
        (hcb.trans hpa) (Ne.symm hp) (by omega) hbA
      exact hc ((hcover c).mpr hcA)
  · simp only [nextPreference, if_neg hbr]
    have hb : b ∉ P := by
      intro hb
      have ha := old_of_before_old hab hb
      exact hbr ⟨a, ha, b, hb, rfl, (low_eq_iff.mpr hl).symm, hbit⟩
    by_cases ha : a ∈ P
    · have hp := hae k (low a k) a hbr ha rfl
      exact bool_not_other (by rw [hp]; exact hbit)
    · have hT := ho a b ((before_append_new_iff ha hb).mp hab)
      have hp := (code_lt_iff_split hl hbit).mp hT
      exact bool_not_other (by rw [← hp]; exact hbit)

/-- Every admissible prefix extends to include an arbitrary finite set. -/
lemma finite_extension (P : List ℕ) (hP : Good P) (F : Finset ℕ) :
    ∃ Q : List ℕ, Good Q ∧ P <+: Q ∧ ∀ x ∈ F, x ∈ Q := by
  classical
  obtain ⟨hPN, hPC, e₀, he₀⟩ := hP
  let e := adapt P e₀
  have he : Compatible P e := adapt_compatible he₀
  have hae : ∀ k w a, ¬ Branch P k w → a ∈ P → low a k = w → e k w = a.testBit k :=
    fun _ _ _ hn ha hw => adapt_old hn ha hw
  obtain ⟨A, hseed, hs⟩ := saturated_exists P e (P.toFinset ∪ F)
  obtain ⟨B, hBN, hB, ho⟩ := sorted_block e P A
  have hPA : ∀ x ∈ P, x ∈ A := fun _ hx =>
    hseed (Finset.mem_union_left _ (List.mem_toFinset.mpr hx))
  have hcover : ∀ x, x ∈ P ++ B ↔ x ∈ A := by
    intro x
    rw [List.mem_append, hB x]
    constructor
    · rintro (hp | ⟨ha, _⟩)
      · exact hPA x hp
      · exact ha
    · intro ha
      by_cases hp : x ∈ P
      · exact Or.inl hp
      · exact Or.inr ⟨ha, hp⟩
  have hsep : ∀ a ∈ P, ∀ b ∈ B, a ≠ b := by
    intro a ha b hb hab
    subst b
    exact ((hB a).mp hb).2 ha
  refine ⟨P ++ B, ⟨List.nodup_append.mpr ⟨hPN, hBN, hsep⟩,
    extend_closed hPC he hae hs hB ho,
    ⟨nextPreference P e, extend_compatible he hae hs hcover ho⟩⟩,
    List.prefix_append P B, ?_⟩
  intro x hx
  exact (hcover x).mpr (hseed (Finset.mem_union_right _ hx))

lemma good_nil : Good [] := by
  refine ⟨by simp, ?_, ⟨fun _ _ => false, ?_⟩⟩
  · simp [Closed, Before]
  · simp [Compatible, Before]

noncomputable def nextStage (P : {Q : List ℕ // Good Q}) (n : ℕ) :
    {Q : List ℕ // Good Q} :=
  ⟨Classical.choose (finite_extension P.val P.property {n}),
    (Classical.choose_spec (finite_extension P.val P.property {n})).1⟩

lemma nextStage_prefix (P : {Q : List ℕ // Good Q}) (n : ℕ) :
    P.val <+: (nextStage P n).val :=
  (Classical.choose_spec (finite_extension P.val P.property {n})).2.1

lemma nextStage_mem (P : {Q : List ℕ // Good Q}) (n : ℕ) :
    n ∈ (nextStage P n).val :=
  (Classical.choose_spec (finite_extension P.val P.property {n})).2.2 n (by simp)

/-- Stage `n + 1` includes the value `n` and preserves every earlier position. -/
noncomputable def stage : ℕ → {Q : List ℕ // Good Q}
  | 0 => ⟨[], good_nil⟩
  | n + 1 => nextStage (stage n) n

lemma stage_prefix_succ (n : ℕ) : (stage n).val <+: (stage (n + 1)).val :=
  nextStage_prefix (stage n) n

lemma stage_mem_succ (n : ℕ) : n ∈ (stage (n + 1)).val := nextStage_mem (stage n) n

lemma stage_prefix {m n : ℕ} (h : m ≤ n) : (stage m).val <+: (stage n).val := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact List.prefix_refl _
  | succ n ih =>
      by_cases hm : m ≤ n
      · exact (ih hm).trans (stage_prefix_succ n)
      · have hm' : m = n + 1 := by omega
        subst m
        exact List.prefix_refl _

lemma stage_contains {a n : ℕ} (h : a < n) : a ∈ (stage n).val :=
  (stage_prefix (Nat.succ_le_of_lt h)).subset (stage_mem_succ a)

lemma stage_length (n : ℕ) : n ≤ (stage n).val.length := by
  have hs : Finset.range n ⊆ (stage n).val.toFinset := by
    intro a ha
    exact List.mem_toFinset.mpr (stage_contains (Finset.mem_range.mp ha))
  calc
    n = (Finset.range n).card := (Finset.card_range n).symm
    _ ≤ (stage n).val.toFinset.card := Finset.card_le_card hs
    _ ≤ (stage n).val.length := List.toFinset_card_le _

lemma stage_index_bound (n : ℕ) : n < (stage (n + 1)).val.length :=
  lt_of_lt_of_le (Nat.lt_succ_self n) (stage_length (n + 1))

noncomputable def permFun (n : ℕ) : ℕ := (stage (n + 1)).val[n]'(stage_index_bound n)

lemma permFun_agrees (t i : ℕ) (hi : i < (stage t).val.length) :
    permFun i = (stage t).val[i] := by
  by_cases ht : i + 1 ≤ t
  · exact (stage_prefix ht).getElem (stage_index_bound i)
  · have ht' : t ≤ i + 1 := by omega
    exact ((stage_prefix ht').getElem hi).symm

lemma permFun_injective : Function.Injective permFun := by
  intro i j h
  let t := i + j + 1
  have hlen := stage_length t
  have hi : i < (stage t).val.length :=
    lt_of_lt_of_le (show i < t by dsimp [t]; omega) hlen
  have hj : j < (stage t).val.length :=
    lt_of_lt_of_le (show j < t by dsimp [t]; omega) hlen
  have hv : (stage t).val[i] = (stage t).val[j] :=
    (permFun_agrees t i hi).symm.trans (h.trans (permFun_agrees t j hj))
  have hidx := congrArg (fun x => (stage t).val.idxOf x) hv
  simpa only [(stage t).property.1.idxOf_getElem] using hidx

lemma permFun_surjective : Function.Surjective permFun := by
  intro x
  obtain ⟨i, hi, hv⟩ := List.mem_iff_getElem.mp (stage_mem_succ x)
  exact ⟨i, (permFun_agrees (x + 1) i hi).trans hv⟩

lemma before_get {P : List ℕ} (hP : P.Nodup) {i j : ℕ}
    (hi : i < P.length) (hj : j < P.length) (hij : i < j) : Before P P[i] P[j] := by
  refine ⟨List.getElem_mem hi, List.getElem_mem hj, ?_⟩
  simpa only [hP.idxOf_getElem] using hij

lemma permFun_no_four (i j k l : ℕ) (hij : i < j) (hjk : j < k) (hkl : k < l)
    (h₁ : permFun i + permFun k = 2 * permFun j)
    (h₂ : permFun j + permFun l = 2 * permFun k) : False := by
  let t := l + 1
  have hlen := stage_length t
  have hi : i < (stage t).val.length :=
    lt_of_lt_of_le (show i < t by dsimp [t]; omega) hlen
  have hj : j < (stage t).val.length :=
    lt_of_lt_of_le (show j < t by dsimp [t]; omega) hlen
  have hk : k < (stage t).val.length :=
    lt_of_lt_of_le (show k < t by dsimp [t]; omega) hlen
  have hl : l < (stage t).val.length :=
    lt_of_lt_of_le (show l < t by dsimp [t]; omega) hlen
  have hP := (stage t).property
  have hab : Before (stage t).val (permFun i) (permFun j) := by
    rw [permFun_agrees t i hi, permFun_agrees t j hj]
    exact before_get hP.1 hi hj hij
  have hbc : Before (stage t).val (permFun j) (permFun k) := by
    rw [permFun_agrees t j hj, permFun_agrees t k hk]
    exact before_get hP.1 hj hk hjk
  have hcd : Before (stage t).val (permFun k) (permFun l) := by
    rw [permFun_agrees t k hk, permFun_agrees t l hl]
    exact before_get hP.1 hk hl hkl
  exact hcd.asymm (hP.2.1 _ _ _ _ hab hbc h₁ h₂)

lemma permFun_no_monotoneAP : ¬ HasMonotoneAP permFun 4 := by
  rintro ⟨indices, hap, hinc⟩
  have hlen : indices.length = 4 := by simpa using hap.length
  obtain ⟨i, j, k, l, rfl⟩ := List.length_eq_four.mp hlen
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, or_false] at hinc
  have hij : i < j := by tauto
  have hjk : j < k := by tauto
  have hkl : k < l := by tauto
  rcases hap with ⟨a, d, heq | heq⟩ <;>
    norm_num [List.range_succ] at heq <;>
    apply permFun_no_four i j k l hij hjk hkl <;> omega

/-- A permutation of all natural numbers avoiding both directions of four-term APs. -/
theorem counterexample : ∃ f : ℕ ≃ ℕ, ¬ HasMonotoneAP f 4 :=
  ⟨Equiv.ofBijective permFun ⟨permFun_injective, permFun_surjective⟩,
    permFun_no_monotoneAP⟩

end Construction196

/-- The exact counterexample-mode target from the pinned submission bundle. -/
theorem target : ¬ (fcTypeOfName% "Erdos196.erdos_196") := by
  intro h
  obtain ⟨f, hf⟩ := Construction196.counterexample
  exact hf (h.mp True.intro f)
