/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
/-
# The base `RichPortSystem` data on `C11^(box 3)`

Words of `C11^3` are encoded as their base-11 code in `Fin 1331`; coordinate `k` is
`(n / 11^k) % 11`.  Conflict in `C11` is `sconf` and conflict in the strong cube is
`wconf` (conflict in *every* coordinate), so `G3` is `C11^(box 3)` by definition.
`CycleC11.lean` proves this for an explicitly constructed 11-cycle.

The independent set of size 148 in `C11^(box 3)` is due to Baumert, McEliece,
Rodemich, Rumsey, Stanley and Taylor.  See the paper.

## The data

* `Ilist` -- an independent set of size 148 in `C11^(box 3)`.
* `pairs` -- the three private pairs, parents `P_0 = {(0,0,5),(0,5,9),(6,1,10)}` and
  alternatives `P_1 = {(10,0,5),(0,5,10),(6,0,10)}`; every side is `false`, i.e. the
  parent transversal is `P_0` and the alternative transversal is `P_1`.
* `Xlist` -- the auxiliary set `X`, obtained from a second independent set of size 148
  by the translation `+(0,0,8)` and then the signed coordinate permutation
  `perm (0, 2, 1)`, `signs (-1, 1, 1)`.

The resulting parameters are `(N, d, L, eta) = (148, 3, 148, 142)`; the footprint
sizes are `|X_0| = 3`, `|X_1| = 3`, so `c = 6` and `eta = 148 - 6 = 142`.

## The checks

Every check here is `native_decide`.  The coordinate conflict test is
`sconf a b := (a + 12 - b) % 11 <= 2`, tied by `sconf_eq_spec` to the literal definition
`(a - b) % 11 in {0,1,10}`, and `pairwiseOK` runs it over the unordered pairs of `Ilist`.
Because `wconf u u = true` (`sconf_refl`), `pairwiseOK Ilist = true` together with `Nodup`
certifies an independent *set* of size 148.
-/
import ShannonBounds.Lift

namespace ShannonBounds
namespace BaseC11

/-- Words of `C11^3`, encoded in base 11. -/
abbrev Code := Fin 1331

/-- **Reference spec** for conflict in `C11`: `(a - b) mod 11` is `0`, `1` or `10`.
(`a + 11 - b` keeps truncated `Nat` subtraction harmless for `a, b < 11`.) -/
def sconfSpec (a b : Nat) : Bool :=
  ((a + 11 - b) % 11 == 0) || ((a + 11 - b) % 11 == 1) || ((a + 11 - b) % 11 == 10)

/-- Equivalently: `{0,1,10}` shifted up by one mod 11 is `{x | x <= 2}`. -/
def sconf (a b : Nat) : Bool := (a + 12 - b) % 11 <= 2

theorem sconf_eq_spec : ∀ a < 11, ∀ b < 11, sconf a b = sconfSpec a b := by native_decide
theorem sconf_symm : ∀ a < 11, ∀ b < 11, sconf a b = sconf b a := by native_decide
theorem sconf_refl : ∀ a < 11, sconf a a = true := by native_decide

/-- Coordinate `k` of a code, as a `Nat`, for `m = 11^k`. -/
def dgt (m : Nat) (u : Code) : Nat := u.val / m % 11

lemma dgt_lt (m : Nat) (u : Code) : dgt m u < 11 := Nat.mod_lt _ (by decide)

/-- Conflict in `C11^(box 3)`: conflict in every one of the three coordinates. -/
def wconf (u v : Code) : Bool :=
  sconf (dgt 1 u) (dgt 1 v) && sconf (dgt 11 u) (dgt 11 v) && sconf (dgt 121 u) (dgt 121 v)

lemma wconf_symm (u v : Code) : wconf u v = wconf v u := by
  unfold wconf
  rw [sconf_symm (dgt 1 u) (dgt_lt 1 u) (dgt 1 v) (dgt_lt 1 v),
    sconf_symm (dgt 11 u) (dgt_lt 11 u) (dgt 11 v) (dgt_lt 11 v),
    sconf_symm (dgt 121 u) (dgt_lt 121 u) (dgt 121 v) (dgt_lt 121 v)]

lemma wconf_refl (u : Code) : wconf u u = true := by
  unfold wconf
  rw [sconf_refl (dgt 1 u) (dgt_lt 1 u), sconf_refl (dgt 11 u) (dgt_lt 11 u),
    sconf_refl (dgt 121 u) (dgt_lt 121 u)]
  rfl

/-- `C11^(box 3)`. -/
def G3 : SimpleGraph Code where
  Adj u v := u ≠ v ∧ wconf u v = true
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by rw [wconf_symm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance decG3 : DecidableRel G3.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ wconf u v = true))

lemma conflict_G3 (u v : Code) : conflict G3 u v ↔ wconf u v = true := by
  constructor
  · rintro (rfl | ⟨-, h⟩)
    · exact wconf_refl u
    · exact h
  · intro h
    by_cases huv : u = v
    · exact Or.inl huv
    · exact Or.inr ⟨huv, h⟩

/-! ### Independence as a one-directional `Bool` check -/

def pairwiseOK : List Code → Bool
  | [] => true
  | u :: us => us.all (fun v => !(wconf u v)) && pairwiseOK us

lemma pairwiseOK_forall {l : List Code} (h : pairwiseOK l = true) :
    ∀ x ∈ l, ∀ y ∈ l, x ≠ y → wconf x y = false := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons u rest ih =>
      simp only [pairwiseOK, Bool.and_eq_true] at h
      intro x hx y hy hne
      rcases List.mem_cons.mp hx with rfl | hx'
      · rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd rfl hne
        · simpa using List.all_eq_true.mp h.1 y hy'
      · rcases List.mem_cons.mp hy with rfl | hy'
        · rw [wconf_symm]
          simpa using List.all_eq_true.mp h.1 x hx'
        · exact ih h.2 x hx' y hy' hne

lemma isIndepSet_of_pairwiseOK {l : List Code} {nd : (l : Multiset Code).Nodup}
    (h : pairwiseOK l = true) :
    G3.IsIndepSet ((⟨(l : Multiset Code), nd⟩ : Finset Code) : Set Code) := by
  intro x hx y hy hne
  rw [Finset.mem_coe, Finset.mem_mk, Multiset.mem_coe] at hx hy
  intro hadj
  have h2 : wconf x y = true := hadj.2
  rw [pairwiseOK_forall h x hx y hy hne] at h2
  exact Bool.false_ne_true h2

/-! ### The data -/

/-- An independent set of size 148 in `C11^(box 3)`. -/
def Ilist : List Code :=
  [
    5, 7, 11, 26, 28, 43, 47, 49, 64, 69, 86, 90, 107, 111,
    130, 134, 151, 155, 172, 177, 192, 194, 198, 213, 215, 230, 234, 242,
    257, 259, 274, 278, 280, 295, 300, 317, 321, 338, 342, 357, 359, 365,
    382, 386, 403, 407, 423, 425, 429, 444, 446, 461, 465, 482, 488, 490,
    505, 509, 511, 526, 530, 548, 552, 569, 573, 588, 590, 594, 613, 617,
    634, 638, 653, 655, 660, 675, 677, 692, 696, 713, 717, 732, 740, 747,
    753, 761, 768, 783, 789, 804, 811, 819, 825, 832, 840, 855, 859, 876,
    880, 895, 897, 912, 917, 919, 934, 938, 955, 959, 978, 982, 984, 999,
    1003, 1020, 1024, 1042, 1046, 1061, 1063, 1067, 1082, 1084, 1090, 1107, 1111, 1126,
    1128, 1143, 1147, 1149, 1165, 1169, 1186, 1190, 1207, 1213, 1230, 1234, 1251, 1255,
    1272, 1277, 1292, 1294, 1298, 1313, 1315, 1330
  ]

/-- The auxiliary set `X`, with `|X| = 148`. -/
def Xlist : List Code :=
  [
    10, 19, 28, 37, 46, 55, 63, 72, 81, 90, 99, 108, 117, 122,
    126, 135, 144, 162, 164, 171, 180, 189, 198, 207, 216, 225, 234, 261,
    263, 270, 279, 288, 297, 306, 315, 324, 333, 342, 360, 362, 365, 369,
    378, 387, 396, 405, 414, 423, 432, 441, 459, 461, 468, 477, 495, 504,
    513, 522, 531, 540, 558, 560, 567, 576, 585, 594, 603, 608, 612, 621,
    630, 639, 657, 659, 666, 675, 684, 693, 702, 711, 720, 738, 756, 758,
    765, 774, 783, 792, 801, 810, 819, 828, 837, 846, 851, 855, 864, 873,
    882, 891, 900, 909, 918, 927, 936, 945, 954, 963, 968, 981, 990, 999,
    1008, 1017, 1026, 1035, 1044, 1053, 1062, 1071, 1080, 1094, 1098, 1107, 1116, 1125,
    1134, 1143, 1152, 1161, 1170, 1179, 1188, 1197, 1206, 1211, 1224, 1233, 1242, 1251,
    1260, 1269, 1278, 1287, 1296, 1305, 1314, 1323
  ]

/-- The three private pairs `(parent, alternative, side)`.  Every side is `false`, so
the parent transversal is `P c = false` and the alternative transversal is `c = true`. -/
def pairs : List (Code × Code × Bool) :=
  [(5, 1215, false), (64, 65, false), (747, 736, false)]

/-- The parents `P_0 = {(0,0,5),(0,5,9),(6,1,10)}`, as base-11 codes. -/
def portsList : List Code := [5, 64, 747]

/-- The alternatives `P_1 = {(10,0,5),(0,5,10),(6,0,10)}`, as base-11 codes. -/
def Iset : Finset Code := ⟨(Ilist : Multiset Code), by native_decide⟩
def Xset : Finset Code := ⟨(Xlist : Multiset Code), by native_decide⟩
def portsSet : Finset Code := ⟨(portsList : Multiset Code), by native_decide⟩

def bside (r : Code) : Bool :=
  match pairs.find? (fun t => t.1.val == r.val) with
  | some t => t.2.2
  | none => false

def bep (c : Bool) (r : Code) : Code :=
  match pairs.find? (fun t => t.1.val == r.val) with
  | some t => if c == t.2.2 then r else t.2.1
  | none => r

/-! ### Independence of `I` and of `X` -/

theorem pairwiseOK_I : pairwiseOK Ilist = true := by native_decide
theorem pairwiseOK_X : pairwiseOK Xlist = true := by native_decide

/-! ### The private pairs are edges, and both transversals are independent -/

/-- Each parent genuinely conflicts with its own alternative: the pairs are edges. -/
theorem pairConflict : portsList.all (fun r => wconf (bep false r) (bep true r)) = true := by
  native_decide

/-- Both transversals separately *are* independent (this is what `hP_indep` needs). -/
theorem transversal_false_indep : pairwiseOK (portsList.map (bep false)) = true := by
  native_decide

theorem transversal_true_indep : pairwiseOK (portsList.map (bep true)) = true := by
  native_decide

end BaseC11
end ShannonBounds
