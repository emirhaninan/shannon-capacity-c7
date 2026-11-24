/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
import ShannonBounds.CosetC23PortData
import ShannonBounds.CosetC23

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

/-!
# A rich port system on the 16501-word `C23` coset code

With auxiliary translate `Xaux` and the certified pairs in `CosetC23PortData`, the profile is

  `(N, d, L, eta) = (16501, 50, 16501, 16279)`,

with seven-letter weights `(B,N,A,D,O,H,V) = (16451, 16279, 76, 146, 50, 50, 50)`.
-/

namespace ShannonBounds
namespace CosetC23Port

open SimpleGraph BaseC23 CosetC23

/-! ### The translate `Xaux` as a `Finset` -/

theorem XauxboundCheck : Xaux.all (fun u => u < 279841) = true := by native_decide
theorem XauxsortCheck : ssorted Xaux = true := by native_decide
theorem XauxlenCheck : Xaux.length = 16501 := by native_decide

lemma Xauxbound : ∀ u ∈ Xaux, u < 279841 := by
  intro u hu; simpa using List.all_eq_true.mp XauxboundCheck u hu

def Xauxlist : List Code := Xaux.map toCode

def Xauxset : Finset Code :=
  ⟨(Xauxlist : Multiset Code), nodup_map_toCode Xauxbound (ssorted_nodup XauxsortCheck)⟩

lemma mem_Xauxset (x : Code) : x ∈ Xauxset ↔ x.val ∈ Xaux := by
  rw [Xauxset, Finset.mem_mk, Multiset.mem_coe]
  exact mem_map_toCode Xauxbound x

theorem XauxsubCheck : Xaux.all (fun u => membWXaux u) = true := by native_decide

theorem XauxnbrCheck :
    Xaux.all (fun u => (nb u).all (fun w => (w == u) || !(membWXaux w))) = true := by
  native_decide

lemma Xauxsub : ∀ u ∈ Xaux, membWXaux u = true := by
  intro u hu; exact List.all_eq_true.mp XauxsubCheck u hu

lemma Xauxnbr : ∀ u ∈ Xaux, ∀ w ∈ nb u, w = u ∨ membWXaux w = false := by
  intro u hu w hw
  have h := List.all_eq_true.mp (List.all_eq_true.mp XauxnbrCheck u hu) w hw
  rcases Bool.or_eq_true_iff.mp h with h1 | h1
  · exact Or.inl (by simpa using h1)
  · exact Or.inr (by simpa using h1)

theorem isIndepSet_Xaux : G4.IsIndepSet (Xauxset : Set Code) :=
  CosetC23.indep_of_pred Xauxbound Xauxsub Xauxnbr _

/-! ### Ports -/

def portsList : List Code := portsAux.map toCode

lemma portsBoundCheck : portsAux.all (fun u => u < 279841) = true := by native_decide

lemma portsBound : ∀ u ∈ portsAux, u < 279841 := by
  intro u hu; simpa using List.all_eq_true.mp portsBoundCheck u hu

theorem portsNodupCheck : portsAux.Nodup := by native_decide

def portsSet : Finset Code :=
  ⟨(portsList : Multiset Code), nodup_map_toCode portsBound portsNodupCheck⟩

lemma mem_portsSet (r : Code) : r ∈ portsSet ↔ r.val ∈ portsAux := by
  rw [portsSet, Finset.mem_mk, Multiset.mem_coe]
  exact mem_map_toCode portsBound r

def bsideN (r : Nat) : Bool :=
  match pairsAux.find? (fun p => p.1 == r) with
  | some p => p.2.2
  | none => false

def bepN (c : Bool) (r : Nat) : Nat :=
  match pairsAux.find? (fun p => p.1 == r) with
  | some p => if c == p.2.2 then r else p.2.1
  | none => r

def bside (r : Code) : Bool := bsideN r.val
def bep (c : Bool) (r : Code) : Code := toCode (bepN c r.val)

theorem bepBoundCheck :
    portsAux.all (fun r => (bepN false r < 279841) && (bepN true r < 279841)) = true := by
  native_decide

lemma bep_val {c : Bool} {r : Code} (hr : r ∈ portsSet) : (bep c r).val = bepN c r.val := by
  have h := List.all_eq_true.mp bepBoundCheck r.val ((mem_portsSet r).mp hr)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  cases c
  · exact toCode_val h.1
  · exact toCode_val h.2

/-! ### Raw certificates for the structure fields -/

theorem portsCheck : portsAux.all (fun r => Jraw.contains r) = true := by native_decide

theorem h_ports : portsSet ⊆ Jset := by
  intro r hr
  rw [CosetC23.mem_Jset]
  exact List.contains_iff_mem.mp (List.all_eq_true.mp portsCheck r.val ((mem_portsSet r).mp hr))

theorem epParentCheck : portsAux.all (fun r => bepN (bsideN r) r == r) = true := by
  native_decide

theorem h_ep_parent : ∀ r ∈ portsSet, bep (bside r) r = r := by
  intro r hr
  apply Fin.val_injective
  rw [bep_val hr]
  have h := List.all_eq_true.mp epParentCheck r.val ((mem_portsSet r).mp hr)
  show bepN (bsideN r.val) r.val = r.val
  simpa using h

theorem altNotCheck : portsAux.all (fun r => !(Jraw.contains (bepN (!bsideN r) r))) = true := by
  native_decide

theorem h_alt_not : ∀ r ∈ portsSet, bep (!bside r) r ∉ Jset := by
  intro r hr
  rw [CosetC23.mem_Jset, bep_val hr, ← List.contains_iff_mem]
  have h := List.all_eq_true.mp altNotCheck r.val ((mem_portsSet r).mp hr)
  show ¬ (Jraw.contains (bepN (!bsideN r.val) r.val) = true)
  simpa using h

theorem altInjCheck :
    portsAux.all (fun r => portsAux.all (fun s =>
      !(bepN (!bsideN r) r == bepN (!bsideN s) s) || (r == s))) = true := by
  native_decide

theorem h_alt_inj : ∀ r ∈ portsSet, ∀ s ∈ portsSet,
    bep (!bside r) r = bep (!bside s) s → r = s := by
  intro r hr s hs hrs
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp altInjCheck r.val ((mem_portsSet r).mp hr))
    s.val ((mem_portsSet s).mp hs)
  have hv : bepN (!bsideN r.val) r.val = bepN (!bsideN s.val) s.val := by
    have h2 := congrArg Fin.val hrs
    rwa [bep_val hr, bep_val hs] at h2
  apply Fin.val_injective
  simpa [hv] using h

theorem pFalseCheck :
    portsAux.all (fun r => portsAux.all (fun s =>
      (r == s) || !(wconfN (bepN false r) (bepN false s)))) = true := by native_decide

theorem pTrueCheck :
    portsAux.all (fun r => portsAux.all (fun s =>
      (r == s) || !(wconfN (bepN true r) (bepN true s)))) = true := by native_decide

theorem h_P_indep : ∀ c : Bool, ∀ r ∈ portsSet, ∀ s ∈ portsSet, r ≠ s →
    ¬ conflict G4 (bep c r) (bep c s) := by
  intro c r hr s hs hrs hc
  have hw : wconfN (bepN c r.val) (bepN c s.val) = true := by
    have h2 : wconfN (bep c r).val (bep c s).val = true := (conflict_G4 _ _).mp hc
    rwa [bep_val hr, bep_val hs] at h2
  have hne : (r.val == s.val) = false := by
    simpa using fun h => hrs (Fin.ext h)
  cases c with
  | false =>
      have h := List.all_eq_true.mp
        (List.all_eq_true.mp pFalseCheck r.val ((mem_portsSet r).mp hr))
        s.val ((mem_portsSet s).mp hs)
      rw [hw, hne] at h
      simp at h
  | true =>
      have h := List.all_eq_true.mp
        (List.all_eq_true.mp pTrueCheck r.val ((mem_portsSet r).mp hr))
        s.val ((mem_portsSet s).mp hs)
      rw [hw, hne] at h
      simp at h

/-- **Privacy, in the neighbour direction.**  For each port the alternative has 81
neighbours; the only one the mask accepts is the parent itself.  `50 * 81` lookups. -/
theorem privCheck :
    portsAux.all (fun r => (nb (bepN (!bsideN r) r)).all
      (fun w => !(membW w) || (w == r))) = true := by native_decide

theorem h_private : ∀ r ∈ portsSet, ∀ w ∈ Jset,
    conflict G4 (bep (!bside r) r) w → w = r := by
  intro r hr w hw hc
  have hwr : w.val ∈ Jraw := (CosetC23.mem_Jset w).mp hw
  have hconf : wconfN (bepN (!bsideN r.val) r.val) w.val = true := by
    have h2 : wconfN (bep (!bside r) r).val w.val = true := (conflict_G4 _ _).mp hc
    rwa [bep_val hr] at h2
  have hmem : w.val ∈ nb (bepN (!bsideN r.val) r.val) := mem_nb _ _ w.isLt hconf
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp privCheck r.val ((mem_portsSet r).mp hr)) w.val hmem
  rw [CosetC23.Jsub w.val hwr] at h
  apply Fin.val_injective
  simpa using h

/-- **The pairs are edges**: each parent conflicts with its own alternative.  This is
the port-indexed form of the data-layer `pairConflict` (`portsAux` is exactly the list of
first components of `pairsAux`).  With `h_private` it makes `N[alt r] ∩ I = {r}` an
equality rather than just an inclusion. -/
theorem epConflictCheck :
    portsAux.all (fun r => wconfN r (bepN (!bsideN r) r)) = true := by native_decide

theorem h_ep_conflict : ∀ r ∈ portsSet, conflict G4 r (bep (!bside r) r) := by
  intro r hr
  have h : wconfN r.val (bepN (!bsideN r.val) r.val) = true :=
    List.all_eq_true.mp epConflictCheck r.val ((mem_portsSet r).mp hr)
  rw [conflict_G4]
  show wconfN r.val (bep (!bside r) r).val = true
  rw [bep_val hr]
  exact h

/-! ### Footprints and separation -/

def fpBN (c : Bool) (x : Nat) : Bool := portsAux.any fun r => wconfN x (bepN c r)

def fpB (c : Bool) (x : Code) : Bool := fpBN c x.val

lemma fpB_iff (c : Bool) (x : Code) :
    (∃ r ∈ portsSet, conflict G4 x (bep c r)) ↔ fpB c x = true := by
  rw [fpB, fpBN, List.any_eq_true]
  constructor
  · rintro ⟨r, hr, hc⟩
    refine ⟨r.val, (mem_portsSet r).mp hr, ?_⟩
    have h2 : wconfN x.val (bep c r).val = true := (conflict_G4 _ _).mp hc
    rwa [bep_val hr] at h2
  · rintro ⟨rv, hrv, hc⟩
    have hb := portsBound rv hrv
    have hmem : (toCode rv) ∈ portsSet := (mem_portsSet _).mpr (by rwa [toCode_val hb])
    refine ⟨toCode rv, hmem, ?_⟩
    rw [conflict_G4]
    show wconfN x.val (bep c (toCode rv)).val = true
    rw [bep_val hmem, toCode_val hb]
    exact hc

theorem sepCheck :
    (Xaux.filter (fpBN false)).all (fun x => !(fpBN true x)) = true := by native_decide

theorem h_sep : ∀ x ∈ Xauxset, ¬ ((∃ r ∈ portsSet, conflict G4 x (bep false r)) ∧
    (∃ r ∈ portsSet, conflict G4 x (bep true r))) := by
  intro x hx hcon
  obtain ⟨h0, h1⟩ := hcon
  rw [fpB_iff] at h0 h1
  have h0' : fpBN false x.val = true := h0
  have h1' : fpBN true x.val = true := h1
  have hmem : x.val ∈ Xaux.filter (fpBN false) :=
    List.mem_filter.mpr ⟨(mem_Xauxset x).mp hx, h0'⟩
  have h := List.all_eq_true.mp sepCheck x.val hmem
  rw [h1'] at h
  simp at h

/-! ### The assembled system -/

/-- **The base system on `C23^(box 4)`.** -/
def base : RichPortSystem G4 where
  I := Jset
  hI := isIndepSet_J
  ports := portsSet
  hports := h_ports
  ep := bep
  side := bside
  hep_parent := h_ep_parent
  halt_not := h_alt_not
  hprivate := h_private
  hep_conflict := h_ep_conflict
  halt_inj := h_alt_inj
  hP_indep := h_P_indep
  X := Xauxset
  hX := isIndepSet_Xaux
  hsep := h_sep

/-! ### The four parameters -/

theorem portsLenCheck : portsAux.length = 50 := by native_decide

theorem base_N : base.N = 16501 := by
  change Jset.card = 16501
  change (Jraw.map toCode).length = 16501
  rw [List.length_map]
  exact CosetC23.JlenCheck

theorem base_d : base.d = 50 := by
  change portsSet.card = 50
  change (portsAux.map toCode).length = 50
  rw [List.length_map]
  exact portsLenCheck

theorem base_L : base.L = 16501 := by
  change Xauxset.card = 16501
  change (Xaux.map toCode).length = 16501
  rw [List.length_map]
  exact XauxlenCheck

lemma Xlist_nodup : Xauxlist.Nodup := nodup_map_toCode Xauxbound (ssorted_nodup XauxsortCheck)

def Xc (c : Bool) : Finset Code :=
  ⟨((Xaux.filter (fpBN c)).map toCode : Multiset Code),
    nodup_map_toCode (fun u hu => Xauxbound u (List.mem_of_mem_filter hu))
      (List.Nodup.filter _ (ssorted_nodup XauxsortCheck))⟩

lemma mem_Xc {c : Bool} {x : Code} :
    x ∈ Xc c ↔ x.val ∈ Xaux ∧ fpBN c x.val = true := by
  rw [Xc, Finset.mem_mk, Multiset.mem_coe,
    mem_map_toCode (fun u hu => Xauxbound u (List.mem_of_mem_filter hu)) x, List.mem_filter]

lemma Xc_eq (c : Bool) : base.Xc c = Xc c := by
  ext x
  rw [RichPortSystem.mem_Xc, mem_Xc]
  change (x ∈ Xauxset ∧ ∃ r ∈ portsSet, conflict G4 x (bep c r)) ↔ _
  rw [mem_Xauxset, fpB_iff]
  exact Iff.rfl

theorem XcFalseLenCheck : (Xaux.filter (fpBN false)).length = 76 := by native_decide
theorem XcTrueLenCheck : (Xaux.filter (fpBN true)).length = 146 := by native_decide

theorem base_Xc_false : (base.Xc false).card = 76 := by
  rw [Xc_eq]
  change ((Xaux.filter (fpBN false)).map toCode).length = 76
  rw [List.length_map]
  exact XcFalseLenCheck

theorem base_Xc_true : (base.Xc true).card = 146 := by
  rw [Xc_eq]
  change ((Xaux.filter (fpBN true)).map toCode).length = 146
  rw [List.length_map]
  exact XcTrueLenCheck

theorem base_eta : base.eta = 16279 := by
  change (Xauxset \ (base.Xc false ∪ base.Xc true)).card = 16279
  have hsub : base.Xc false ∪ base.Xc true ⊆ Xauxset := by
    change base.Xc false ∪ base.Xc true ⊆ base.X
    exact Finset.union_subset (base.Xc_subset_X false) (base.Xc_subset_X true)
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_union_of_disjoint base.Xc_disjoint,
    base_Xc_false, base_Xc_true]
  have hXcard : Xauxset.card = 16501 := by
    change (Xaux.map toCode).length = 16501
    rw [List.length_map]; exact XauxlenCheck
  rw [hXcard]

end CosetC23Port
end ShannonBounds
