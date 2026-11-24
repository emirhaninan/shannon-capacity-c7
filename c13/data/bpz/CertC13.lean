/-
Copyright (c) 2026 Pjotr Buys, Sven Polak, Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys, Sven Polak, Jeroen Zuiddam
-/
import ShannonBounds.PortRealisation
import ShannonBounds.Layered
import ShannonBounds.Substitutions
import ShannonBounds.TerminalCodes

set_option maxRecDepth 4000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 4000
set_option exponentiation.threshold 20000

/-!
# A weighted layered bound for `C13`

A heterogeneous DAG over the seven-letter separation system, using an arity-`3`
substitution together with an arity-`2` substitution.  Writing `w` for the
base realisation (exponent `1`),

```
a3  = Tt (w, w, w)            a(j+1) = Ss (a j, w)   for j = 3 .. 8
b2  = Ss (w, w)               b(j+1) = Ss (b j, w)   for j = 2 .. 16
c12 = Tt (a3, a7, b2)
x34 = Tt (a9, b13, c12)       x36    = Tt (a7, b17, c12)
```

and the subscript of each node is its strong-power exponent.  The terminal code
`K` is applied to `(x34, x36, b17)`, giving exponent `34 + 36 + 17 = 87`.

`bound` is what this proves: a port system whose seven families have the sizes recorded in
`w0` gives an independent set of size `M` in `G^(box 87)`.  The base system of `C13` lives
in `C13^(box 6)`, so `M` is an independent set in `C13^(box 522)`.
-/

namespace ShannonBounds
namespace CertC13

open SimpleGraph

/-- The arity-`3` substitution. -/
abbrev Tt : Subst Letter Letter.sep 3 := Substitutions.S3c

/-- The arity-`2` substitution. -/
abbrev Ss : Subst Letter Letter.sep 2 := Substitutions.S2b

/-- The terminal code, of `19` words of length `3`. -/
abbrev K : Code Letter Letter.sep 3 := TerminalCodes.K3a

/-- The size of each of the seven families of the base port system. -/
def w0 : Letter → Nat
  | .B => 61516
  | .N => 60502
  | .A => 1014
  | .D => 1014
  | .O => 1014
  | .H => 1014
  | .V => 1014

/-- The size of the independent set the construction produces. -/
def M : Nat :=
  2296460381476588218557784714607916555821735215842235657422063709967472046388590671039445990314835453532287927129054300935809605566313640680416850619170792677088359272060919872915091855126481463077864366034595511602265113812807433166736895166001025727331303746555909789115142163380824770899805627970640032438106635377536797524856543870646748758850611538293943083007991697753785956882728113597379667638999165717627011072

variable {α : Type*} [Fintype α] [DecidableEq α]
  {G : SimpleGraph α} [DecidableRel G.Adj]

/-- The base realisation, seen in the first strong power. -/
def R1 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 1) :=
  R.mapIso (strongPower_one_iso G).symm

lemma w_R1 (R : Realisation Letter Letter.sep G) (a : Letter) :
    (R1 R).w a = R.w a := by simp [R1]

/-! ### Node `a3`, exponent `3` -/

/-- The child exponents of node `a3`. -/
def ea3 : Fin 3 → Nat := Fin.cases 1 (Fin.cases 1 (fun _ => 1))

/-- The children of node `a3`. -/
def cha3 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (ea3 i)) :=
  Fin.cases (R1 R) (Fin.cases (R1 R) (fun _ => (R1 R)))

/-- Node `a3`. -/
def Ra3 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 3) :=
  Realisation.multiSubst ea3 (cha3 R) Tt

/-- The seven sizes at node `a3`. -/
def wa3 : Letter → Nat
  | .B => 233172601039144
  | .N => 221663094285880
  | .A => 11696130496440
  | .D => 11135216676168
  | .O => 0
  | .H => 11321840419344
  | .V => 11508464162520

/-- Node `a3` has the sizes `wa3`. -/
lemma stepa3 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Ra3 R).w a = wa3 a := by
  intro a
  change (Realisation.multiSubst ea3 (cha3 R) Tt).w a = wa3 a
  rw [w_multiSubst]
  have h0 : ∀ b, (cha3 R 0).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  have h1 : ∀ b, (cha3 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  have h2 : ∀ b, (cha3 R 2).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### Node `a4`, exponent `4` -/

/-- The child exponents of node `a4`. -/
def ea4 : Fin 2 → Nat := Fin.cases 3 (fun _ => 1)

/-- The children of node `a4`. -/
def cha4 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (ea4 i)) :=
  Fin.cases (Ra3 R) (fun _ => (R1 R))

/-- Node `a4`. -/
def Ra4 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 4) :=
  Realisation.multiSubst ea4 (cha4 R) Ss

/-- The seven sizes at node `a4`. -/
def wa4 : Letter → Nat
  | .B => 14366996711557006816
  | .N => 13422920406807701920
  | .A => 967036997119734528
  | .D => 898469256947398656
  | .O => 0
  | .H => 921240712842247824
  | .V => 944201405212677456

/-- Node `a4` has the sizes `wa4`. -/
lemma stepa4 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Ra4 R).w a = wa4 a := by
  intro a
  change (Realisation.multiSubst ea4 (cha4 R) Ss).w a = wa4 a
  rw [w_multiSubst]
  have h0 : ∀ b, (cha4 R 0).w b = wa3 b := fun b => stepa3 R h b
  have h1 : ∀ b, (cha4 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `a5`, exponent `5` -/

/-- The child exponents of node `a5`. -/
def ea5 : Fin 2 → Nat := Fin.cases 4 (fun _ => 1)

/-- The children of node `a5`. -/
def cha5 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (ea5 i)) :=
  Fin.cases (Ra4 R) (fun _ => (R1 R))

/-- Node `a5`. -/
def Ra5 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 5) :=
  Realisation.multiSubst ea5 (cha5 R) Ss

/-- The seven sizes at node `a5`. -/
def wa5 : Letter → Nat
  | .B => 885691793049764904341632
  | .N => 813094105967758992375232
  | .A => 74944275116687300502048
  | .D => 67970028276334523232192
  | .O => 0
  | .H => 70281884983706726888064
  | .V => 72628473018388115423712

/-- Node `a5` has the sizes `wa5`. -/
lemma stepa5 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Ra5 R).w a = wa5 a := by
  intro a
  change (Realisation.multiSubst ea5 (cha5 R) Ss).w a = wa5 a
  rw [w_multiSubst]
  have h0 : ∀ b, (cha5 R 0).w b = wa4 b := fun b => stepa4 R h b
  have h1 : ∀ b, (cha5 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `a6`, exponent `6` -/

/-- The child exponents of node `a6`. -/
def ea6 : Fin 2 → Nat := Fin.cases 5 (fun _ => 1)

/-- The children of node `a6`. -/
def cha6 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (ea6 i)) :=
  Fin.cases (Ra5 R) (fun _ => (R1 R))

/-- Node `a6`. -/
def Ra6 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 6) :=
  Realisation.multiSubst ea6 (cha6 R) Ss

/-- The seven sizes at node `a6`. -/
def wa6 : Letter → Nat
  | .B => 54629131444889861984746353472
  | .N => 49269813094229675479395363136
  | .A => 5574936891575125423574409600
  | .D => 4936800074226098942862565632
  | .O => 0
  | .H => 5147937860109010629514630272
  | .V => 5363556401023949547738049536

/-- Node `a6` has the sizes `wa6`. -/
lemma stepa6 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Ra6 R).w a = wa6 a := by
  intro a
  change (Realisation.multiSubst ea6 (cha6 R) Ss).w a = wa6 a
  rw [w_multiSubst]
  have h0 : ∀ b, (cha6 R 0).w b = wa5 b := fun b => stepa5 R h b
  have h1 : ∀ b, (cha6 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `a7`, exponent `7` -/

/-- The child exponents of node `a7`. -/
def ea7 : Fin 2 → Nat := Fin.cases 6 (fun _ => 1)

/-- The children of node `a7`. -/
def cha7 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (ea7 i)) :=
  Fin.cases (Ra6 R) (fun _ => (R1 R))

/-- Node `a7`. -/
def Ra7 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 7) :=
  Realisation.multiSubst ea7 (cha7 R) Ss

/-- The seven sizes at node `a7`. -/
def wa7 : Letter → Nat
  | .B => 3371224551247167191361223773068800
  | .N => 2986575217835141003033882711788672
  | .A => 403133332565100107599100755820160
  | .D => 348645868568376329177177844087168
  | .O => 0
  | .H => 366640135880014788821328894032256
  | .V => 385124135033088708093088588572288

/-- Node `a7` has the sizes `wa7`. -/
lemma stepa7 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Ra7 R).w a = wa7 a := by
  intro a
  change (Realisation.multiSubst ea7 (cha7 R) Ss).w a = wa7 a
  rw [w_multiSubst]
  have h0 : ∀ b, (cha7 R 0).w b = wa6 b := fun b => stepa6 R h b
  have h1 : ∀ b, (cha7 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `a8`, exponent `8` -/

/-- The child exponents of node `a8`. -/
def ea8 : Fin 2 → Nat := Fin.cases 7 (fun _ => 1)

/-- The children of node `a8`. -/
def cha8 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (ea8 i)) :=
  Fin.cases (Ra7 R) (fun _ => (R1 R))

/-- Node `a8`. -/
def Ra8 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 8) :=
  Realisation.multiSubst ea8 (cha8 R) Ss

/-- The seven sizes at node `a8`. -/
def wa8 : Letter → Nat
  | .B => 208146553604470082050668188124406331392
  | .N => 181102551028682712474661459995039875584
  | .A => 28552837365470199789793124997239771904
  | .D => 24122159611008737644953970992715551744
  | .O => 0
  | .H => 25582621869679822726209225315041973504
  | .V => 27091456659362652939995622182915289600

/-- Node `a8` has the sizes `wa8`. -/
lemma stepa8 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Ra8 R).w a = wa8 a := by
  intro a
  change (Realisation.multiSubst ea8 (cha8 R) Ss).w a = wa8 a
  rw [w_multiSubst]
  have h0 : ∀ b, (cha8 R 0).w b = wa7 b := fun b => stepa7 R h b
  have h1 : ∀ b, (cha8 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `a9`, exponent `9` -/

/-- The child exponents of node `a9`. -/
def ea9 : Fin 2 → Nat := Fin.cases 8 (fun _ => 1)

/-- The children of node `a9`. -/
def cha9 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (ea9 i)) :=
  Fin.cases (Ra8 R) (fun _ => (R1 R))

/-- Node `a9`. -/
def Ra9 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 9) :=
  Realisation.multiSubst ea9 (cha9 R) Ss

/-- The seven sizes at node `a9`. -/
def wa9 : Letter → Nat
  | .B => 12857755838466731209987737815994794580089344
  | .N => 10986019119425948252728817881367103681293824
  | .A => 1990494978538767280934580078821238372890112
  | .D => 1643076887528334915444311873436246745457664
  | .O => 0
  | .H => 1757378553678308245274793424915092475914240
  | .V => 1876136813176292568950453569108639950008832

/-- Node `a9` has the sizes `wa9`. -/
lemma stepa9 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Ra9 R).w a = wa9 a := by
  intro a
  change (Realisation.multiSubst ea9 (cha9 R) Ss).w a = wa9 a
  rw [w_multiSubst]
  have h0 : ∀ b, (cha9 R 0).w b = wa8 b := fun b => stepa8 R h b
  have h1 : ∀ b, (cha9 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b2`, exponent `2` -/

/-- The child exponents of node `b2`. -/
def eb2 : Fin 2 → Nat := Fin.cases 1 (fun _ => 1)

/-- The children of node `b2`. -/
def chb2 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb2 i)) :=
  Fin.cases (R1 R) (fun _ => (R1 R))

/-- Node `b2`. -/
def Rb2 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 2) :=
  Realisation.multiSubst eb2 (chb2 R) Ss

/-- The seven sizes at node `b2`. -/
def wb2 : Letter → Nat
  | .B => 3786274648
  | .N => 3661520200
  | .A => 125782644
  | .D => 122698056
  | .O => 0
  | .H => 123726252
  | .V => 124754448

/-- Node `b2` has the sizes `wb2`. -/
lemma stepb2 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb2 R).w a = wb2 a := by
  intro a
  change (Realisation.multiSubst eb2 (chb2 R) Ss).w a = wb2 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb2 R 0).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  have h1 : ∀ b, (chb2 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b3`, exponent `3` -/

/-- The child exponents of node `b3`. -/
def eb3 : Fin 2 → Nat := Fin.cases 2 (fun _ => 1)

/-- The children of node `b3`. -/
def chb3 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb3 i)) :=
  Fin.cases (Rb2 R) (fun _ => (R1 R))

/-- Node `b3`. -/
def Rb3 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 3) :=
  Realisation.multiSubst eb3 (chb3 R) Ss

/-- The seven sizes at node `b3`. -/
def wb3 : Letter → Nat
  | .B => 233168430676168
  | .N => 221656838741416
  | .A => 11700300859416
  | .D => 11136259266912
  | .O => 0
  | .H => 11323925600832
  | .V => 11512634525496

/-- Node `b3` has the sizes `wb3`. -/
lemma stepb3 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb3 R).w a = wb3 a := by
  intro a
  change (Realisation.multiSubst eb3 (chb3 R) Ss).w a = wb3 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb3 R 0).w b = wb2 b := fun b => stepb2 R h b
  have h1 : ∀ b, (chb3 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b4`, exponent `4` -/

/-- The child exponents of node `b4`. -/
def eb4 : Fin 2 → Nat := Fin.cases 3 (fun _ => 1)

/-- The children of node `b4`. -/
def chb4 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb4 i)) :=
  Fin.cases (Rb3 R) (fun _ => (R1 R))

/-- Node `b4`. -/
def Rb4 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 4) :=
  Realisation.multiSubst eb4 (chb4 R) Ss

/-- The seven sizes at node `b4`. -/
def wb4 : Letter → Nat
  | .B => 14366745453443247280
  | .N => 13422546162604598656
  | .A => 967290369607522896
  | .D => 898525992650505648
  | .O => 0
  | .H => 921362641744577136
  | .V => 944453720513451408

/-- Node `b4` has the sizes `wb4`. -/
lemma stepb4 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb4 R).w a = wb4 a := by
  intro a
  change (Realisation.multiSubst eb4 (chb4 R) Ss).w a = wb4 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb4 R 0).w b = wb3 b := fun b => stepb3 R h b
  have h1 : ∀ b, (chb4 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b5`, exponent `5` -/

/-- The child exponents of node `b5`. -/
def eb5 : Fin 2 → Nat := Fin.cases 4 (fun _ => 1)

/-- The children of node `b5`. -/
def chb5 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb5 i)) :=
  Fin.cases (Rb4 R) (fun _ => (R1 R))

/-- Node `b5`. -/
def Rb5 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 5) :=
  Realisation.multiSubst eb5 (chb5 R) Ss

/-- The seven sizes at node `b5`. -/
def wb5 : Letter → Nat
  | .B => 885676651105344440620096
  | .N => 813071720364685456101856
  | .A => 74959663260934055450496
  | .D => 67973081416221955752480
  | .O => 0
  | .H => 70289006078440470135360
  | .V => 72643738598715541067616

/-- Node `b5` has the sizes `wb5`. -/
lemma stepb5 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb5 R).w a = wb5 a := by
  intro a
  change (Realisation.multiSubst eb5 (chb5 R) Ss).w a = wb5 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb5 R 0).w b = wb4 b := fun b => stepb4 R h b
  have h1 : ∀ b, (chb5 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b6`, exponent `6` -/

/-- The child exponents of node `b6`. -/
def eb6 : Fin 2 → Nat := Fin.cases 5 (fun _ => 1)

/-- The children of node `b6`. -/
def chb6 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb6 i)) :=
  Fin.cases (Rb5 R) (fun _ => (R1 R))

/-- Node `b6`. -/
def Rb6 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 6) :=
  Realisation.multiSubst eb6 (chb6 R) Ss

/-- The seven sizes at node `b6`. -/
def wb6 : Letter → Nat
  | .B => 54628218672499004804545643200
  | .N => 49268474324050786597301294656
  | .A => 5575871126328998107430263680
  | .D => 4936962096294051819423826944
  | .O => 0
  | .H => 5148353222371135013334087744
  | .V => 5364480000251914913520002880

/-- Node `b6` has the sizes `wb6`. -/
lemma stepb6 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb6 R).w a = wb6 a := by
  intro a
  change (Realisation.multiSubst eb6 (chb6 R) Ss).w a = wb6 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb6 R 0).w b = wb5 b := fun b => stepb5 R h b
  have h1 : ∀ b, (chb6 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b7`, exponent `7` -/

/-- The child exponents of node `b7`. -/
def eb7 : Fin 2 → Nat := Fin.cases 6 (fun _ => 1)

/-- The children of node `b7`. -/
def chb7 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb7 i)) :=
  Fin.cases (Rb6 R) (fun _ => (R1 R))

/-- Node `b7`. -/
def Rb7 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 7) :=
  Realisation.multiSubst eb7 (chb7 R) Ss

/-- The seven sizes at node `b7`. -/
def wb7 : Letter → Nat
  | .B => 3371169512745188552182259834983936
  | .N => 2986495166875818294790857216648832
  | .A => 403190030904968644634760138813696
  | .D => 348654313714570220788443890547072
  | .O => 0
  | .H => 366664329791970239089923254441088
  | .V => 385180014827568626333280774919680

/-- Node `b7` has the sizes `wb7`. -/
lemma stepb7 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb7 R).w a = wb7 a := by
  intro a
  change (Realisation.multiSubst eb7 (chb7 R) Ss).w a = wb7 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb7 R 0).w b = wb6 b := fun b => stepb6 R h b
  have h1 : ∀ b, (chb7 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b8`, exponent `8` -/

/-- The child exponents of node `b8`. -/
def eb8 : Fin 2 → Nat := Fin.cases 7 (fun _ => 1)

/-- The children of node `b8`. -/
def chb8 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb8 i)) :=
  Fin.cases (Rb7 R) (fun _ => (R1 R))

/-- Node `b8`. -/
def Rb8 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 8) :=
  Realisation.multiSubst eb8 (chb8 R) Ss

/-- The seven sizes at node `b8`. -/
def wb8 : Letter → Nat
  | .B => 208143233911477231385583024894643625728
  | .N => 181097765277658396677096090102444721408
  | .A => 28556277144877762920586498201963233024
  | .D => 24122589387571007249060361483560865792
  | .O => 0
  | .H => 25584029010694920978773648137879885056
  | .V => 27094837521753849190873211547644213760

/-- Node `b8` has the sizes `wb8`. -/
lemma stepb8 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb8 R).w a = wb8 a := by
  intro a
  change (Realisation.multiSubst eb8 (chb8 R) Ss).w a = wb8 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb8 R 0).w b = wb7 b := fun b => stepb7 R h b
  have h1 : ∀ b, (chb8 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b9`, exponent `9` -/

/-- The child exponents of node `b9`. -/
def eb9 : Fin 2 → Nat := Fin.cases 8 (fun _ => 1)

/-- The children of node `b9`. -/
def chb9 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb9 i)) :=
  Fin.cases (Rb8 R) (fun _ => (R1 R))

/-- Node `b9`. -/
def Rb9 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 9) :=
  Realisation.multiSubst eb9 (chb9 R) Ss

/-- The seven sizes at node `b9`. -/
def wb9 : Letter → Nat
  | .B => 12857555547962336418867547275140018716483072
  | .N => 10985733059853794367359142352554901252913152
  | .A => 1990703589891687729276398144511990111571968
  | .D => 1643098037118366694813225425842278449655296
  | .O => 0
  | .H => 1757460262613454373160815174213697956612608
  | .V => 1876341364396600050928808396140570604614656

/-- Node `b9` has the sizes `wb9`. -/
lemma stepb9 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb9 R).w a = wb9 a := by
  intro a
  change (Realisation.multiSubst eb9 (chb9 R) Ss).w a = wb9 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb9 R 0).w b = wb8 b := fun b => stepb8 R h b
  have h1 : ∀ b, (chb9 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b10`, exponent `10` -/

/-- The child exponents of node `b10`. -/
def eb10 : Fin 2 → Nat := Fin.cases 9 (fun _ => 1)

/-- The children of node `b10`. -/
def chb10 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb10 i)) :=
  Fin.cases (Rb9 R) (fun _ => (R1 R))

/-- Node `b10`. -/
def Rb10 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 10) :=
  Realisation.multiSubst eb10 (chb10 R) Ss

/-- The seven sizes at node `b10`. -/
def wb10 : Letter → Nat
  | .B => 794630061938239282329082916477852619684257102848
  | .N => 666677395027424438171449098332811793576885497856
  | .A => 137047821474396876405594755771747013649870774272
  | .D => 110550250764427169258091935059800200631498654720
  | .O => 0
  | .H => 119251458837621006707862876602420513369435129856
  | .V => 128346613401203038955823814229126700911934299136

/-- Node `b10` has the sizes `wb10`. -/
lemma stepb10 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb10 R).w a = wb10 a := by
  intro a
  change (Realisation.multiSubst eb10 (chb10 R) Ss).w a = wb10 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb10 R 0).w b = wb9 b := fun b => stepb9 R h b
  have h1 : ∀ b, (chb10 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b11`, exponent `11` -/

/-- The child exponents of node `b11`. -/
def eb11 : Fin 2 → Nat := Fin.cases 10 (fun _ => 1)

/-- The children of node `b11`. -/
def chb11 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb11 i)) :=
  Fin.cases (Rb10 R) (fun _ => (R1 R))

/-- Node `b11`. -/
def Rb11 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 11) :=
  Realisation.multiSubst eb11 (chb11 R) Ss

/-- The seven sizes at node `b11`. -/
def wb11 : Letter → Nat
  | .B => 49133527335442895274058842994554770627778068539795456
  | .N => 40474282244924271790924286429684330606829695356395520
  | .A => 9339663597913283479701894560789752254369359302502400
  | .D => 7364522150307180974758927640697502897293893502695424
  | .O => 0
  | .H => 8011883620412902228946742102783971459121133343047680
  | .V => 8692302127807562225514080098703283692542119462150144

/-- Node `b11` has the sizes `wb11`. -/
lemma stepb11 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb11 R).w a = wb11 a := by
  intro a
  change (Realisation.multiSubst eb11 (chb11 R) Ss).w a = wb11 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb11 R 0).w b = wb10 b := fun b => stepb10 R h b
  have h1 : ∀ b, (chb11 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b12`, exponent `12` -/

/-- The child exponents of node `b12`. -/
def eb12 : Fin 2 → Nat := Fin.cases 11 (fun _ => 1)

/-- The children of node `b12`. -/
def chb12 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb12 i)) :=
  Fin.cases (Rb11 R) (fun _ => (R1 R))

/-- Node `b12`. -/
def Rb12 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 12) :=
  Realisation.multiSubst eb12 (chb12 R) Ss

/-- The seven sizes at node `b12`. -/
def wb12 : Letter → Nat
  | .B => 3039436111915800696635827059365339346662182202638527864832
  | .N => 2458245443270692361342918898653402179160340758785379184640
  | .A => 631171343537096922501896521361132525912515655165706203136
  | .D => 486609241334238274930861866557180231527400455791463600128
  | .O => 0
  | .H => 533899954989673305111885013634558699514620949822306140160
  | .V => 583880629881661892320873374283754057925295161134863663104

/-- Node `b12` has the sizes `wb12`. -/
lemma stepb12 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb12 R).w a = wb12 a := by
  intro a
  change (Realisation.multiSubst eb12 (chb12 R) Ss).w a = wb12 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb12 R 0).w b = wb11 b := fun b => stepb11 R h b
  have h1 : ∀ b, (chb12 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b13`, exponent `13` -/

/-- The child exponents of node `b13`. -/
def eb13 : Fin 2 → Nat := Fin.cases 12 (fun _ => 1)

/-- The children of node `b13`. -/
def chb13 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb13 i)) :=
  Fin.cases (Rb12 R) (fun _ => (R1 R))

/-- Node `b13`. -/
def Rb13 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 13) :=
  Realisation.multiSubst eb13 (chb13 R) Ss

/-- The seven sizes at node `b13`. -/
def wb13 : Letter → Nat
  | .B => 188107381373671929544446354389267384385314875314022250313515008
  | .N => 149368773551110045525386202278988327024834227462371037519069184
  | .A => 42354593573576982681191731507800401549779508277874319801991168
  | .D => 31933493198680566164268724413677068177539367905703505228169216
  | .O => 0
  | .H => 35336050510621225091664438261978062769010007878677359011307520
  | .V => 38952036261636323753796017659499406958308868304900466018852864

/-- Node `b13` has the sizes `wb13`. -/
lemma stepb13 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb13 R).w a = wb13 a := by
  intro a
  change (Realisation.multiSubst eb13 (chb13 R) Ss).w a = wb13 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb13 R 0).w b = wb12 b := fun b => stepb12 R h b
  have h1 : ∀ b, (chb13 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b14`, exponent `14` -/

/-- The child exponents of node `b14`. -/
def eb14 : Fin 2 → Nat := Fin.cases 13 (fun _ => 1)

/-- The children of node `b14`. -/
def chb14 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb14 i)) :=
  Fin.cases (Rb13 R) (fun _ => (R1 R))

/-- Node `b14`. -/
def Rb14 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 14) :=
  Realisation.multiSubst eb14 (chb14 R) Ss

/-- The seven sizes at node `b14`. -/
def wb14 : Letter → Nat
  | .B => 11646941792569871572385458838914550572150531210267540664866771861504
  | .N => 9080057095272867034815644426032261368827996851322137072257942814720
  | .A => 2825156431974219269112448391497857968119219204913923085322454253568
  | .D => 2083500141887397200233327973587184142480668743677717705359030059008
  | .O => 0
  | .H => 2325192419592200868901571193234736672901601551311560648983929552896
  | .V => 2583464154269415600444205171850305437698286397280080141697554759680

/-- Node `b14` has the sizes `wb14`. -/
lemma stepb14 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb14 R).w a = wb14 a := by
  intro a
  change (Realisation.multiSubst eb14 (chb14 R) Ss).w a = wb14 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb14 R 0).w b = wb13 b := fun b => stepb13 R h b
  have h1 : ∀ b, (chb14 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b15`, exponent `15` -/

/-- The child exponents of node `b15`. -/
def eb15 : Fin 2 → Nat := Fin.cases 14 (fun _ => 1)

/-- The children of node `b15`. -/
def chb15 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb15 i)) :=
  Fin.cases (Rb14 R) (fun _ => (R1 R))

/-- Node `b15`. -/
def Rb15 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 15) :=
  Realisation.multiSubst eb15 (chb15 R) Ss

/-- The seven sizes at node `b15`. -/
def wb15 : Letter → Nat
  | .B => 721450649077623898746780503168863725696560364310689955301695362925232128
  | .N => 552226323000220859679296141732782705316504353772474655154267024789307392
  | .A => 187469915221273072174127226454536371501611099495844667759269410923085824
  | .D => 135263103479077992581819872505968528016357009137229923600901590644228096
  | .O => 0
  | .H => 152243714778240515824652116971024774198206509837722611874164964390076416
  | .V => 170489303922110548931294981989480125319761598795351979486006037177237504

/-- Node `b15` has the sizes `wb15`. -/
lemma stepb15 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb15 R).w a = wb15 a := by
  intro a
  change (Realisation.multiSubst eb15 (chb15 R) Ss).w a = wb15 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb15 R 0).w b = wb14 b := fun b => stepb14 R h b
  have h1 : ∀ b, (chb15 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b16`, exponent `16` -/

/-- The child exponents of node `b16`. -/
def eb16 : Fin 2 → Nat := Fin.cases 15 (fun _ => 1)

/-- The children of node `b16`. -/
def chb16 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb16 i)) :=
  Fin.cases (Rb15 R) (fun _ => (R1 R))

/-- Node `b16`. -/
def Rb16 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 16) :=
  Realisation.multiSubst eb16 (chb16 R) Ss

/-- The seven sizes at node `b16`. -/
def wb16 : Letter → Nat
  | .B => 44708009409621267734969479791281772918060827033090340925978305341297835900928
  | .N => 33600891488193733347501340174741719117761780066831048079251362716478684856320
  | .A => 12383888709986979227102579347623972300929611219552271753177361332285690019840
  | .D => 8743645778213400658900072214073149545236567181545974138028174800293445959680
  | .O => 0
  | .H => 9925381849820467523184105915306601672767807073902633492377558712556298502144
  | .V => 11202152638379912362818545646390520173398371327195612398827977420022837477376

/-- Node `b16` has the sizes `wb16`. -/
lemma stepb16 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb16 R).w a = wb16 a := by
  intro a
  change (Realisation.multiSubst eb16 (chb16 R) Ss).w a = wb16 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb16 R 0).w b = wb15 b := fun b => stepb15 R h b
  have h1 : ∀ b, (chb16 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `b17`, exponent `17` -/

/-- The child exponents of node `b17`. -/
def eb17 : Fin 2 → Nat := Fin.cases 16 (fun _ => 1)

/-- The children of node `b17`. -/
def chb17 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eb17 i)) :=
  Fin.cases (Rb16 R) (fun _ => (R1 R))

/-- Node `b17`. -/
def Rb17 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 17) :=
  Realisation.multiSubst eb17 (chb17 R) Ss

/-- The seven sizes at node `b17`. -/
def wb17 : Letter → Nat
  | .B => 2771681226813297091188789207524050424379442340666299033736163845013712917164720128
  | .N => 2045478399970624051926808098710714197975965843380038074448587791463331080857190400
  | .A => 814808995867413802085441986708815450984452844264769120058050855293425534589075456
  | .D => 563079360842495612279138528033041796971313232605661210051341513561863453896867840
  | .O => 0
  | .H => 644641093842584325770559818423189011687394864945961084669458783556122645102198784
  | .V => 733247262867325088594020696318668236268371211924469245439933585299166343383744512

/-- Node `b17` has the sizes `wb17`. -/
lemma stepb17 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb17 R).w a = wb17 a := by
  intro a
  change (Realisation.multiSubst eb17 (chb17 R) Ss).w a = wb17 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb17 R 0).w b = wb16 b := fun b => stepb16 R h b
  have h1 : ∀ b, (chb17 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `c12`, exponent `12` -/

/-- The child exponents of node `c12`. -/
def ec12 : Fin 3 → Nat := Fin.cases 3 (Fin.cases 7 (fun _ => 2))

/-- The children of node `c12`. -/
def chc12 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (ec12 i)) :=
  Fin.cases (Ra3 R) (Fin.cases (Ra7 R) (fun _ => (Rb2 R)))

/-- Node `c12`. -/
def Rc12 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 12) :=
  Realisation.multiSubst ec12 (chc12 R) Tt

/-- The seven sizes at node `c12`. -/
def wc12 : Letter → Nat
  | .B => 3041774400948574155336992179526152939487172960570499612672
  | .N => 2459339490249900110501664800293430748398477419605826269184
  | .A => 630488280422751595925613148531552705706427448188534571008
  | .D => 485965198192849270805239999346398737783879027871598223360
  | .O => 0
  | .H => 533509922158576031959347583157731685625080771743272689664
  | .V => 581624379142145203857128576299983308113536923683127365632

/-- Node `c12` has the sizes `wc12`. -/
lemma stepc12 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rc12 R).w a = wc12 a := by
  intro a
  change (Realisation.multiSubst ec12 (chc12 R) Tt).w a = wc12 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chc12 R 0).w b = wa3 b := fun b => stepa3 R h b
  have h1 : ∀ b, (chc12 R 1).w b = wa7 b := fun b => stepa7 R h b
  have h2 : ∀ b, (chc12 R 2).w b = wb2 b := fun b => stepb2 R h b
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### Node `x34`, exponent `34` -/

/-- The child exponents of node `x34`. -/
def ex34 : Fin 3 → Nat := Fin.cases 9 (Fin.cases 13 (fun _ => 12))

/-- The children of node `x34`. -/
def chx34 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (ex34 i)) :=
  Fin.cases (Ra9 R) (Fin.cases (Rb13 R) (fun _ => (Rc12 R)))

/-- Node `x34`. -/
def Rx34 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 34) :=
  Realisation.multiSubst ex34 (chx34 R) Tt

/-- The seven sizes at node `x34`. -/
def wx34 : Letter → Nat
  | .B => 8808234753249397458022307578279690912769031442508421686438630273902512996091228482851184593247492087947474056233148089511668148809581084611742937029056297386901504
  | .N => 4871852899930810053856308172449342930383217453161070248770418099127610019143680659086179581204212089140193618058859318808027151892596662715585147108010832028499968
  | .A => 4684797182432994593403009648789960197426475205186934420000002640172944630210413316257125761634426416380259339239300191649431663415929328554140045148234911745835008
  | .D => 2263825623098385970654547240747551040031366289735639428725219180524058105598136076237279258683834986133857630170284333403947016790732166009253745434406516110131200
  | .O => 0
  | .H => 3018365714061420695201709805142942939617387670479136461046038445041544296346455257622244792366557047612168227524692452261611489218254770517520622048256361158934528
  | .V => 3783493762306585330135721273285075509165437454415644357601015720542696024621513738715411886268874214161295690040941925200766992181841601542813486871912748475744256

/-- Node `x34` has the sizes `wx34`. -/
lemma stepx34 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rx34 R).w a = wx34 a := by
  intro a
  change (Realisation.multiSubst ex34 (chx34 R) Tt).w a = wx34 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chx34 R 0).w b = wa9 b := fun b => stepa9 R h b
  have h1 : ∀ b, (chx34 R 1).w b = wb13 b := fun b => stepb13 R h b
  have h2 : ∀ b, (chx34 R 2).w b = wc12 b := fun b => stepc12 R h b
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### Node `x36`, exponent `36` -/

/-- The child exponents of node `x36`. -/
def ex36 : Fin 3 → Nat := Fin.cases 7 (Fin.cases 17 (fun _ => 12))

/-- The children of node `x36`. -/
def chx36 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (ex36 i)) :=
  Fin.cases (Ra7 R) (Fin.cases (Rb17 R) (fun _ => (Rc12 R)))

/-- Node `x36`. -/
def Rx36 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 36) :=
  Realisation.multiSubst ex36 (chx36 R) Tt

/-- The seven sizes at node `x36`. -/
def wx36 : Letter → Nat
  | .B => 34248447864851208350238481586344477455294845581758901594105545377641383621001900043008897154462772064411475085367395604485246337312959858009696420567940163402844888805408768
  | .N => 18368548233213285829942574952230185161251297679464115691345055317144707986000658842169902773303013041284103171292272143385525807233500177239943449173399113160515214351794176
  | .A => 19056933069861606176580453836929090558043802789016493477243181560386123414020536903986537766747338366378077819754977819470022429855391190623833504476282516966911740978659328
  | .D => 8858440575093596449236047511725612336482264870189121403145819574268276520584481699321830976059794482752955492361496120609375011192953514113171677905619649767687784098693120
  | .O => 0
  | .H => 12042209225927775309314559293888847658120752153371358820501315085972895326857927868428319230015368014222431724376195267951307025242522641212305858328264735072661357906100224
  | .V => 15287979260347001182515157581626181702691918640298935990281523484931728760827818545252426129550087727496436630663671716357772533077546840882225476899405113195770278284623872

/-- Node `x36` has the sizes `wx36`. -/
lemma stepx36 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rx36 R).w a = wx36 a := by
  intro a
  change (Realisation.multiSubst ex36 (chx36 R) Tt).w a = wx36 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chx36 R 0).w b = wa7 b := fun b => stepa7 R h b
  have h1 : ∀ b, (chx36 R 1).w b = wb17 b := fun b => stepb17 R h b
  have h2 : ∀ b, (chx36 R 2).w b = wc12 b := fun b => stepc12 R h b
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### The bound -/

/-- The exponents of the three terminal children. -/
def eT : Fin 3 → Nat := Fin.cases 34 (Fin.cases 36 (fun _ => 17))

/-- The three terminal children. -/
def terminalChildren (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eT i)) :=
  Fin.cases (Rx34 R) (Fin.cases (Rx36 R) (fun _ => Rb17 R))

/-- **The weighted layered bound for `C13`.**  A port system whose seven families have the
sizes of `w0` gives an independent set of size `M` in `G^(box 87)`. -/
theorem bound (S : RichPortSystem G) (hw : ∀ a, (S.fam a).card = w0 a) :
    M ≤ (SimpleGraph.strongPower G 87).indepNum := by
  have base_w : ∀ a, S.toRealisation.w a = w0 a := hw
  refine le_trans (le_of_eq ?_) (le_indepNum_multiCode eT (terminalChildren S.toRealisation) K)
  have h1 : ∀ a, (terminalChildren S.toRealisation 0).w a = wx34 a := by
    intro a; change (Rx34 S.toRealisation).w a = wx34 a; exact stepx34 S.toRealisation base_w a
  have h2 : ∀ a, (terminalChildren S.toRealisation 1).w a = wx36 a := by
    intro a; change (Rx36 S.toRealisation).w a = wx36 a; exact stepx36 S.toRealisation base_w a
  have h3 : ∀ a, (terminalChildren S.toRealisation 2).w a = wb17 a := by
    intro a; change (Rb17 S.toRealisation).w a = wb17 a; exact stepb17 S.toRealisation base_w a
  simp only [Fin.prod_univ_three, h1, h2, h3]
  native_decide

end CertC13
end ShannonBounds
