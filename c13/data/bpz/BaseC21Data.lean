/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# Base data for `C21^(box 4)`

Words of `C21^4` are encoded as their base-21 code in `Fin 194481`; coordinate `k` is
`(n / 21^k) % 21`.  Conflict in `C21` is `sconf` and conflict in the strong 4th power
is `wconf` (conflict in *every* coordinate), so `G4` is `C21^(box 4)` by definition;
`CycleC21.lean` proves this for an explicitly constructed 21-cycle.

## What this file provides

This is the graph-encoding layer only; it carries no code of its own.

* `Code`, `sconf`, `wconf`, `G4`, `decG4`, `conflict_G4` -- the graph;
* `nb` and `mem_nb` -- the 81 closed cyclic neighbours, and the fact that a conflicting
  word is always one of them;
* `ssorted` and `ssorted_nodup` -- strict sortedness gives `Nodup` in linear time;
* `toCode`, `mem_map_toCode` and `nodup_map_toCode` -- raw `Nat` data lifted to `Code`.

The code used for the `C21` bound is the union of cosets in `BaseC21CosetData.lean`;
`CosetC21.lean` proves it independent: a list of words is independent as soon as every
word is in the membership set and no closed cyclic neighbour of a word other than
itself is.
-/
import ShannonBounds.Lift

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace ShannonBounds
namespace BaseC21

/-- Words of `C21^4`, encoded in base 21. -/
abbrev Code := Fin 194481

/-! ### The coordinate conflict test -/

/-- **Reference spec** for conflict in `C21`: `(a - b) mod 21` is `0`, `1` or `20`. -/
def sconfSpec (a b : Nat) : Bool :=
  ((a + 21 - b) % 21 == 0) || ((a + 21 - b) % 21 == 1) || ((a + 21 - b) % 21 == 20)

/-- Equivalently: `{0,1,20}` shifted up by one mod 21 is `{x | x <= 2}`. -/
def sconf (a b : Nat) : Bool := (a + 22 - b) % 21 <= 2

theorem sconf_eq_spec : ∀ a < 21, ∀ b < 21, sconf a b = sconfSpec a b := by native_decide
theorem sconf_symm : ∀ a < 21, ∀ b < 21, sconf a b = sconf b a := by native_decide
theorem sconf_refl : ∀ a < 21, sconf a a = true := by native_decide

/-- The three admissible cyclic offsets, as residues mod 21. -/
def ds : List Nat := [20, 0, 1]

/-- `sconf` really does mean "differs by one of the three offsets". -/
theorem sconf_cases : ∀ a < 21, ∀ b < 21,
    sconf a b = true → ds.any (fun i => b == (a + i) % 21) = true := by native_decide

/-! ### Conflict in `C21^(box 4)` -/

/-- Conflict on raw codes: conflict in every one of the four coordinates. -/
def wconfN (u v : Nat) : Bool :=
  sconf (u / 1 % 21) (v / 1 % 21) && sconf (u / 21 % 21) (v / 21 % 21) &&
    sconf (u / 441 % 21) (v / 441 % 21) && sconf (u / 9261 % 21) (v / 9261 % 21)

/-- Coordinate `k` of a code, as a `Nat`, for `m = 21^k`. -/
def dgt (m : Nat) (u : Code) : Nat := u.val / m % 21

lemma dgt_lt (m : Nat) (u : Code) : dgt m u < 21 := Nat.mod_lt _ (by decide)

def wconf (u v : Code) : Bool := wconfN u.val v.val

lemma wconf_eq (u v : Code) :
    wconf u v = (sconf (dgt 1 u) (dgt 1 v) && sconf (dgt 21 u) (dgt 21 v) &&
      sconf (dgt 441 u) (dgt 441 v) && sconf (dgt 9261 u) (dgt 9261 v)) := rfl

lemma wconf_symm (u v : Code) : wconf u v = wconf v u := by
  rw [wconf_eq, wconf_eq,
    sconf_symm (dgt 1 u) (dgt_lt 1 u) (dgt 1 v) (dgt_lt 1 v),
    sconf_symm (dgt 21 u) (dgt_lt 21 u) (dgt 21 v) (dgt_lt 21 v),
    sconf_symm (dgt 441 u) (dgt_lt 441 u) (dgt 441 v) (dgt_lt 441 v),
    sconf_symm (dgt 9261 u) (dgt_lt 9261 u) (dgt 9261 v) (dgt_lt 9261 v)]

lemma wconf_refl (u : Code) : wconf u u = true := by
  rw [wconf_eq, sconf_refl (dgt 1 u) (dgt_lt 1 u), sconf_refl (dgt 21 u) (dgt_lt 21 u),
    sconf_refl (dgt 441 u) (dgt_lt 441 u), sconf_refl (dgt 9261 u) (dgt_lt 9261 u)]
  rfl

/-- `C21^(box 4)`. -/
def G4 : SimpleGraph Code where
  Adj u v := u ≠ v ∧ wconf u v = true
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by rw [wconf_symm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance decG4 : DecidableRel G4.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ wconf u v = true))

lemma conflict_G4 (u v : Code) : conflict G4 u v ↔ wconf u v = true := by
  constructor
  · rintro (rfl | ⟨-, h⟩)
    · exact wconf_refl u
    · exact h
  · intro h
    by_cases huv : u = v
    · exact Or.inl huv
    · exact Or.inr ⟨huv, h⟩

/-! ### Digit reconstruction and the 81 neighbours -/

/-- A code below `194481` is recovered from its four base-21 digits. -/
theorem recon (v : Nat) (h : v < 194481) :
    ((v / 9261 % 21 * 21 + v / 441 % 21) * 21 + v / 21 % 21) * 21 + v / 1 % 21 = v := by
  omega

/-- The 81 closed cyclic neighbours of `u` in `Z_21^4`. -/
def nb (u : Nat) : List Nat :=
  ds.flatMap fun i => ds.flatMap fun j => ds.flatMap fun k => ds.map fun m =>
    ((((u / 9261 % 21 + i) % 21) * 21 + (u / 441 % 21 + j) % 21) * 21
      + (u / 21 % 21 + k) % 21) * 21 + (u / 1 % 21 + m) % 21

private lemma pick {a b : Nat} (ha : a < 21) (hb : b < 21) (h : sconf a b = true) :
    ∃ i ∈ ds, b = (a + i) % 21 := by
  obtain ⟨i, hi, he⟩ := List.any_eq_true.mp (sconf_cases a ha b hb h)
  exact ⟨i, hi, by simpa using he⟩

/-- **Conflict implies neighbour.**  This is the bridge that makes the 81-neighbour
certificate a proof of independence. -/
theorem mem_nb (u v : Nat) (hv : v < 194481) (h : wconfN u v = true) : v ∈ nb u := by
  simp only [wconfN, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  obtain ⟨i0, hi0, e0⟩ := pick (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) h0
  obtain ⟨i1, hi1, e1⟩ := pick (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) h1
  obtain ⟨i2, hi2, e2⟩ := pick (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) h2
  obtain ⟨i3, hi3, e3⟩ := pick (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) h3
  refine List.mem_flatMap.mpr ⟨i3, hi3, ?_⟩
  refine List.mem_flatMap.mpr ⟨i2, hi2, ?_⟩
  refine List.mem_flatMap.mpr ⟨i1, hi1, ?_⟩
  refine List.mem_map.mpr ⟨i0, hi0, ?_⟩
  rw [← e3, ← e2, ← e1, ← e0]
  exact recon v hv

/-! ### Strict sortedness gives `Nodup` in linear time -/

def ssorted : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => (a < b) && ssorted (b :: t)

theorem ssorted_pairwise : ∀ {l : List Nat}, ssorted l = true → l.Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons a t ih =>
      cases t with
      | nil => intro _; simp
      | cons b t' =>
          intro h
          simp only [ssorted, Bool.and_eq_true, decide_eq_true_eq] at h
          have hp := ih h.2
          refine List.Pairwise.cons ?_ hp
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc'
          · exact h.1
          · exact lt_trans h.1 (List.rel_of_pairwise_cons hp hc')

theorem ssorted_nodup {l : List Nat} (h : ssorted l = true) : l.Nodup :=
  (ssorted_pairwise h).imp Nat.ne_of_lt

/-! ### Raw `Nat` data lifted to `Code` -/

def toCode (u : Nat) : Code := ⟨u % 194481, Nat.mod_lt _ (by decide)⟩

theorem toCode_val {u : Nat} (h : u < 194481) : (toCode u).val = u := Nat.mod_eq_of_lt h

theorem mem_map_toCode {raw : List Nat} (hb : ∀ u ∈ raw, u < 194481) (x : Code) :
    x ∈ raw.map toCode ↔ x.val ∈ raw := by
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    rwa [toCode_val (hb u hu)]
  · intro hx
    exact List.mem_map.mpr ⟨x.val, hx, by apply Fin.ext; exact toCode_val x.isLt⟩

theorem nodup_map_toCode {raw : List Nat} (hb : ∀ u ∈ raw, u < 194481)
    (hn : raw.Nodup) : (raw.map toCode).Nodup := by
  refine List.Nodup.map_on ?_ hn
  intro a ha b hb' hab
  have := congrArg Fin.val hab
  rwa [toCode_val (hb a ha), toCode_val (hb b hb')] at this

end BaseC21
end ShannonBounds
