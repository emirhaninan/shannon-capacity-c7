/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
import ShannonBounds.BaseC23CosetData
import ShannonBounds.BaseC23Data

/-!
# The 16501-word coset code in `C23^(box 4)`

`Jraw` is the 16501-word code of `BaseC23CosetData`, obtained from the 11466-word
union-of-cosets code in `C21^(box 4)` by a coordinatewise interval expansion.  This file
proves it independent in `C23^(box 4)`; `CosetC23Port.lean` builds the rich port system
on it, and `CapCertC23.lean` derives the capacity bound.

The expansion is the *expansion process* of Baumert, McEliece, Rodemich, Rumsey, Stanley and
Taylor (1971), Theorem 1: a preselected cell of the `p^n`-torus is allowed to expand into a
`3^n`-cube, giving a packing of the `(p+2)^n`-torus.  Applying that expansion to the stated
source code and cell gives the listed 16501-word code.
-/

namespace ShannonBounds
namespace CosetC23

open SimpleGraph BaseC23

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

/-! ### The list as `Code` data -/

theorem JboundCheck : Jraw.all (fun u => u < 279841) = true := by native_decide
theorem JsortCheck : ssorted Jraw = true := by native_decide
theorem JlenCheck : Jraw.length = 16501 := by native_decide

lemma Jbound : ∀ u ∈ Jraw, u < 279841 := by
  intro u hu; simpa using List.all_eq_true.mp JboundCheck u hu

def Jlist : List Code := Jraw.map toCode

def Jset : Finset Code :=
  ⟨(Jlist : Multiset Code), nodup_map_toCode Jbound (ssorted_nodup JsortCheck)⟩

lemma mem_Jset (x : Code) : x ∈ Jset ↔ x.val ∈ Jraw := by
  rw [Jset, Finset.mem_mk, Multiset.mem_coe]
  exact mem_map_toCode Jbound x

/-! ### Independence -/

theorem JsubCheck : Jraw.all (fun u => membW u) = true := by native_decide

theorem JnbrCheck :
    Jraw.all (fun u => (nb u).all (fun w => (w == u) || !(membW w))) = true := by
  native_decide

lemma Jsub : ∀ u ∈ Jraw, membW u = true := by
  intro u hu; exact List.all_eq_true.mp JsubCheck u hu

lemma Jnbr : ∀ u ∈ Jraw, ∀ w ∈ nb u, w = u ∨ membW w = false := by
  intro u hu w hw
  have h := List.all_eq_true.mp (List.all_eq_true.mp JnbrCheck u hu) w hw
  rcases Bool.or_eq_true_iff.mp h with h1 | h1
  · exact Or.inl (by simpa using h1)
  · exact Or.inr (by simpa using h1)

/-- **Independence from a membership certificate.**  A list of words is independent in
`G4` once every word satisfies the membership predicate `p` and no closed cyclic
neighbour of a word other than itself does. -/
theorem indep_of_pred {raw : List Nat} {p : Nat → Bool}
    (hb : ∀ u ∈ raw, u < 279841)
    (hsub : ∀ u ∈ raw, p u = true)
    (hnbr : ∀ u ∈ raw, ∀ w ∈ nb u, w = u ∨ p w = false)
    (nd : ((raw.map toCode : List Code) : Multiset Code).Nodup) :
    G4.IsIndepSet ((⟨((raw.map toCode : List Code) : Multiset Code), nd⟩ : Finset Code) :
      Set Code) := by
  intro x hx y hy hne hadj
  rw [Finset.mem_coe, Finset.mem_mk, Multiset.mem_coe, mem_map_toCode hb] at hx hy
  have hw : wconfN x.val y.val = true := hadj.2
  have hmem : y.val ∈ nb x.val := mem_nb x.val y.val y.isLt hw
  rcases hnbr x.val hx y.val hmem with heq | hfalse
  · exact hne (Fin.val_injective heq).symm
  · rw [hsub y.val hy] at hfalse
    exact Bool.noConfusion hfalse

/-- The expanded code is independent in `C23^(box 4)`. -/
theorem isIndepSet_J : G4.IsIndepSet (Jset : Set Code) :=
  indep_of_pred Jbound Jsub Jnbr _

theorem card_J : Jset.card = 16501 := by
  change Jlist.length = 16501
  rw [Jlist, List.length_map]
  exact JlenCheck

end CosetC23
end ShannonBounds
