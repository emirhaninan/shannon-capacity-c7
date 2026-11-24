/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
import ShannonBounds.BaseC21CosetData
import ShannonBounds.BaseC21Data
import ShannonBounds.CapC21
import ShannonBounds.Decimal

/-!
# `Theta (C21) >= 10.347918137743866`, from a union of cosets

`Jraw` is the union of the 26 cosets of the rank-two subgroup `<(1,0,0,2),(0,1,2,0)>` of
`(ZZ/21)^4` listed in `BaseC21CosetData`.  It is independent in `C21^(box 4)` and has
`11466 = 26 * 21^2` elements, so

  `Theta (C21) >= 11466^(1/4) = 10.347918137743866...`.

Baumert, McEliece, Rodemich, Rumsey, Stanley and Taylor (1971), Corollary 4, give
`alpha(C21^(box 4)) <= 11576`.
-/

namespace ShannonBounds
namespace CosetC21

open SimpleGraph BaseC21

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

/-! ### The list as `Code` data -/

theorem JboundCheck : Jraw.all (fun u => u < 194481) = true := by native_decide
theorem JsortCheck : ssorted Jraw = true := by native_decide
theorem JlenCheck : Jraw.length = 11466 := by native_decide

lemma Jbound : ∀ u ∈ Jraw, u < 194481 := by
  intro u hu; simpa using List.all_eq_true.mp JboundCheck u hu

def Jlist : List Code := Jraw.map toCode

def Jset : Finset Code :=
  ⟨(Jlist : Multiset Code), nodup_map_toCode Jbound (ssorted_nodup JsortCheck)⟩

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
    (hb : ∀ u ∈ raw, u < 194481)
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

/-- The union of cosets is independent in `C21^(box 4)`. -/
theorem isIndepSet_J : G4.IsIndepSet (Jset : Set Code) :=
  indep_of_pred Jbound Jsub Jnbr _

theorem card_J : Jset.card = 11466 := by
  change Jlist.length = 11466
  rw [Jlist, List.length_map]
  exact JlenCheck

/-! ### The capacity bound -/

theorem alpha_G4_ge : 11466 ≤ G4.indepNum := by
  rw [← card_J]
  exact isIndepSet_J.card_le_indepNum

theorem alpha_strongPower_ge : 11466 ≤ (strongPower Cyc21 4).indepNum := by
  rw [← independenceNumber_iso CapC21.G4_iso]
  exact alpha_G4_ge

theorem shannonCapacity_Cyc_ge :
    ((11466 : ℕ) : ℝ) ^ ((1 : ℝ) / (4 : ℕ)) ≤ shannonCapacity Cyc21 := by
  calc ((11466 : ℕ) : ℝ) ^ ((1 : ℝ) / (4 : ℕ))
      ≤ (((strongPower Cyc21 4).indepNum : ℕ) : ℝ) ^ ((1 : ℝ) / (4 : ℕ)) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        exact_mod_cast alpha_strongPower_ge
    _ ≤ shannonCapacity Cyc21 := shannonCapacity_ge_root Cyc21 4 (by norm_num)

theorem shannonCapacity_cycleGraph_ge :
    ((11466 : ℕ) : ℝ) ^ ((1 : ℝ) / (4 : ℕ)) ≤ shannonCapacity (SimpleGraph.cycleGraph 21) := by
  rw [← CapC21.Cyc_eq_cycleGraph]
  exact shannonCapacity_Cyc_ge

/-- **`Theta (cycleGraph 21) >= 10.347918137743866`**, from the coset construction. -/
theorem shannonCapacity_cycleGraph_21_ge_coset :
    (10.347918137743866 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 21) := by
  have h := shannonCapacity_cycleGraph_ge
  refine le_trans ?_ h
  rw [show ((10.347918137743866 : ℝ))
      = ((10347918137743866 : ℕ) : ℝ) / ((1000000000000000 : ℕ) : ℝ) by norm_num]
  exact Decimal.decimal_le (by norm_num) (by norm_num) (by native_decide) le_rfl

/-- The truncation is tight. -/
theorem tight :
    10347918137743866 ^ 4 ≤ 11466 * (10 ^ 15) ^ 4 ∧
      11466 * (10 ^ 15) ^ 4 < 10347918137743867 ^ 4 := by
  constructor <;> native_decide

end CosetC21
end ShannonBounds
