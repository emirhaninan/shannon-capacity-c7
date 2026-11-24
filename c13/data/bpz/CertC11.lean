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
# `Theta (C11) >= 5.295492315784620`, a weighted schedule

Writing `v` for the base realisation (exponent `1`),

```
g3  = Gg (v, v, v)              h4 = Hh (g3, v),  h(j+1) = Hh (h j, v)  for j = 4 .. 8
b2  = Hh (v, v)                 b(j+1) = Hh (b j, v)                    for j = 2 .. 12
p11 = Gg (g3, h6, b2)
x27 = Gg (h7, p11, h9)          x29 = Gg (h6, b12, p11)
```

with the subscript of each node its exponent, and the `19`-word terminal code
`K` applied to `(x27, x29, b13)`, giving `E = 27 + 29 + 13 = 69`.  The base
lives in `C11^(box 3)`, hence `C11^(box 207)`.
-/
namespace ShannonBounds
namespace CertC11

open SimpleGraph

/-- The arity-`3` substitution. -/
abbrev Gg : Subst Letter Letter.sep 3 := Substitutions.S3c

/-- The arity-`2` substitution. -/
abbrev Hh : Subst Letter Letter.sep 2 := Substitutions.S2b

/-- The `19`-word terminal code. -/
abbrev K : Code Letter Letter.sep 3 := TerminalCodes.K3a

/-- The size of each of the seven families of the base port system. -/
def w0 : Letter → Nat
  | .B => 145
  | .N => 142
  | .A => 3
  | .D => 3
  | .O => 3
  | .H => 3
  | .V => 3

/-- The size of the independent set the construction produces. -/
def M : Nat :=
  705688158939417766083006128695703821080101605304173623991920300506716846627203440324635068341693109509608786929844839653207121849017872676157797788816

variable {α : Type*} [Fintype α] [DecidableEq α]
  {G : SimpleGraph α} [DecidableRel G.Adj]

/-- The base realisation, seen in the first strong power. -/
def R1 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 1) :=
  R.mapIso (strongPower_one_iso G).symm

lemma w_R1 (R : Realisation Letter Letter.sep G) (a : Letter) :
    (R1 R).w a = R.w a := by simp [R1]

/-! ### Node `g3`, exponent `3` -/

/-- The child exponents of node `g3`. -/
def eg3 : Fin 3 → Nat := Fin.cases 1 (Fin.cases 1 (fun _ => 1))

/-- The children of node `g3`. -/
def chg3 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eg3 i)) :=
  Fin.cases (R1 R) (Fin.cases (R1 R) (fun _ => (R1 R)))

/-- Node `g3`. -/
def Rg3 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 3) :=
  Realisation.multiSubst eg3 (chg3 R) Gg

/-- The seven sizes at node `g3`. -/
def wg3 : Letter → Nat
  | .B => 3056536
  | .N => 2867365
  | .A => 193005
  | .D => 181476
  | .O => 0
  | .H => 185310
  | .V => 189144

/-- Node `g3` has the sizes `wg3`. -/
lemma stepg3 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rg3 R).w a = wg3 a := by
  intro a
  change (Realisation.multiSubst eg3 (chg3 R) Gg).w a = wg3 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chg3 R 0).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  have h1 : ∀ b, (chg3 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  have h2 : ∀ b, (chg3 R 2).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### Node `h4`, exponent `4` -/

/-- The child exponents of node `h4`. -/
def eh4 : Fin 2 → Nat := Fin.cases 3 (fun _ => 1)

/-- The children of node `h4`. -/
def chh4 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eh4 i)) :=
  Fin.cases (Rg3 R) (fun _ => (R1 R))

/-- Node `h4`. -/
def Rh4 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 4) :=
  Realisation.multiSubst eh4 (chh4 R) Hh

/-- The seven sizes at node `h4`. -/
def wh4 : Letter → Nat
  | .B => 444321163
  | .N => 407744845
  | .A => 37688178
  | .D => 34371687
  | .O => 0
  | .H => 35472045
  | .V => 36583905

/-- Node `h4` has the sizes `wh4`. -/
lemma steph4 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rh4 R).w a = wh4 a := by
  intro a
  change (Realisation.multiSubst eh4 (chh4 R) Hh).w a = wh4 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chh4 R 0).w b = wg3 b := fun b => stepg3 R h b
  have h1 : ∀ b, (chh4 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `h5`, exponent `5` -/

/-- The child exponents of node `h5`. -/
def eh5 : Fin 2 → Nat := Fin.cases 4 (fun _ => 1)

/-- The children of node `h5`. -/
def chh5 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eh5 i)) :=
  Fin.cases (Rh4 R) (fun _ => (R1 R))

/-- Node `h5`. -/
def Rh5 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 5) :=
  Realisation.multiSubst eh5 (chh5 R) Hh

/-- The seven sizes at node `h5`. -/
def wh5 : Letter → Nat
  | .B => 64642748230
  | .N => 58012832524
  | .A => 6897551541
  | .D => 6104014089
  | .O => 0
  | .H => 6366681060
  | .V => 6634316895

/-- Node `h5` has the sizes `wh5`. -/
lemma steph5 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rh5 R).w a = wh5 a := by
  intro a
  change (Realisation.multiSubst eh5 (chh5 R) Hh).w a = wh5 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chh5 R 0).w b = wh4 b := fun b => steph4 R h b
  have h1 : ∀ b, (chh5 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `h6`, exponent `6` -/

/-- The child exponents of node `h6`. -/
def eh6 : Fin 2 → Nat := Fin.cases 5 (fun _ => 1)

/-- The children of node `h6`. -/
def chh6 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eh6 i)) :=
  Fin.cases (Rh5 R) (fun _ => (R1 R))

/-- Node `h6`. -/
def Rh6 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 6) :=
  Realisation.multiSubst eh6 (chh6 R) Hh

/-- The seven sizes at node `h6`. -/
def wh6 : Letter → Nat
  | .B => 9412203190240
  | .N => 8258514873031
  | .A => 1211595556464
  | .D => 1040808498210
  | .O => 0
  | .H => 1097207251272
  | .V => 1155114490527

/-- Node `h6` has the sizes `wh6`. -/
lemma steph6 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rh6 R).w a = wh6 a := by
  intro a
  change (Realisation.multiSubst eh6 (chh6 R) Hh).w a = wh6 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chh6 R 0).w b = wh5 b := fun b => steph5 R h b
  have h1 : ∀ b, (chh6 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `h7`, exponent `7` -/

/-- The child exponents of node `h7`. -/
def eh7 : Fin 2 → Nat := Fin.cases 6 (fun _ => 1)

/-- The children of node `h7`. -/
def chh7 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eh7 i)) :=
  Fin.cases (Rh6 R) (fun _ => (R1 R))

/-- Node `h7`. -/
def Rh7 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 7) :=
  Realisation.multiSubst eh7 (chh7 R) Hh

/-- The seven sizes at node `h7`. -/
def wh7 : Letter → Nat
  | .B => 1371526674748822
  | .N => 1176343898639794
  | .A => 206870947554819
  | .D => 172570351364913
  | .O => 0
  | .H => 183870596053533
  | .V => 195558767499324

/-- Node `h7` has the sizes `wh7`. -/
lemma steph7 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rh7 R).w a = wh7 a := by
  intro a
  change (Realisation.multiSubst eh7 (chh7 R) Hh).w a = wh7 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chh7 R 0).w b = wh6 b := fun b => steph6 R h b
  have h1 : ∀ b, (chh7 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `h8`, exponent `8` -/

/-- The child exponents of node `h8`. -/
def eh8 : Fin 2 → Nat := Fin.cases 7 (fun _ => 1)

/-- The children of node `h8`. -/
def chh8 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eh8 i)) :=
  Fin.cases (Rh7 R) (fun _ => (R1 R))

/-- Node `h8`. -/
def Rh8 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 8) :=
  Realisation.multiSubst eh8 (chh8 R) Hh

/-- The seven sizes at node `h8`. -/
def wh8 : Letter → Nat
  | .B => 200009691735338386
  | .N => 167661446449515205
  | .A => 34594641933623475
  | .D => 28034021589737028
  | .O => 0
  | .H => 30190268123681667
  | .V => 32436664771481961

/-- Node `h8` has the sizes `wh8`. -/
lemma steph8 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rh8 R).w a = wh8 a := by
  intro a
  change (Realisation.multiSubst eh8 (chh8 R) Hh).w a = wh8 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chh8 R 0).w b = wh7 b := fun b => steph7 R h b
  have h1 : ∀ b, (chh8 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `h9`, exponent `9` -/

/-- The child exponents of node `h9`. -/
def eh9 : Fin 2 → Nat := Fin.cases 8 (fun _ => 1)

/-- The children of node `h9`. -/
def chh9 (R : Realisation Letter Letter.sep G) :
    (i : Fin 2) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eh9 i)) :=
  Fin.cases (Rh8 R) (fun _ => (R1 R))

/-- Node `h9`. -/
def Rh9 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 9) :=
  Realisation.multiSubst eh9 (chh9 R) Hh

/-- The seven sizes at node `h9`. -/
def wh9 : Letter → Nat
  | .B => 29189291292194147479
  | .N => 23911709321632029535
  | .A => 5693880288864205575
  | .D => 4483815405091203591
  | .O => 0
  | .H => 4880573217282387330
  | .V => 5296871535584474961

/-- Node `h9` has the sizes `wh9`. -/
lemma steph9 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rh9 R).w a = wh9 a := by
  intro a
  change (Realisation.multiSubst eh9 (chh9 R) Hh).w a = wh9 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chh9 R 0).w b = wh8 b := fun b => steph8 R h b
  have h1 : ∀ b, (chh9 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
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
  Realisation.multiSubst eb2 (chb2 R) Hh

/-- The seven sizes at node `b2`. -/
def wb2 : Letter → Nat
  | .B => 21043
  | .N => 20173
  | .A => 879
  | .D => 852
  | .O => 0
  | .H => 861
  | .V => 870

/-- Node `b2` has the sizes `wb2`. -/
lemma stepb2 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb2 R).w a = wb2 a := by
  intro a
  change (Realisation.multiSubst eb2 (chb2 R) Hh).w a = wb2 a
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
  Realisation.multiSubst eb3 (chb3 R) Hh

/-- The seven sizes at node `b3`. -/
def wb3 : Letter → Nat
  | .B => 3056428
  | .N => 2867203
  | .A => 193113
  | .D => 181503
  | .O => 0
  | .H => 185364
  | .V => 189252

/-- Node `b3` has the sizes `wb3`. -/
lemma stepb3 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb3 R).w a = wb3 a := by
  intro a
  change (Realisation.multiSubst eb3 (chb3 R) Hh).w a = wb3 a
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
  Realisation.multiSubst eb4 (chb4 R) Hh

/-- The seven sizes at node `b4`. -/
def wb4 : Letter → Nat
  | .B => 444305908
  | .N => 407722165
  | .A => 37703595
  | .D => 34375035
  | .O => 0
  | .H => 35479389
  | .V => 36599241

/-- Node `b4` has the sizes `wb4`. -/
lemma stepb4 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb4 R).w a = wb4 a := by
  intro a
  change (Realisation.multiSubst eb4 (chb4 R) Hh).w a = wb4 a
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
  Realisation.multiSubst eb5 (chb5 R) Hh

/-- The seven sizes at node `b5`. -/
def wb5 : Letter → Nat
  | .B => 64640592550
  | .N => 58009658215
  | .A => 6899751042
  | .D => 6104421465
  | .O => 0
  | .H => 6367677900
  | .V => 6636494607

/-- Node `b5` has the sizes `wb5`. -/
lemma stepb5 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb5 R).w a = wb5 a := by
  intro a
  change (Realisation.multiSubst eb5 (chb5 R) Hh).w a = wb5 a
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
  Realisation.multiSubst eb6 (chb6 R) Hh

/-- The seven sizes at node `b6`. -/
def wb6 : Letter → Nat
  | .B => 9411898437271
  | .N => 8258070719656
  | .A => 1211909173830
  | .D => 1040856822675
  | .O => 0
  | .H => 1097342270145
  | .V => 1155423726360

/-- Node `b6` has the sizes `wb6`. -/
lemma stepb6 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb6 R).w a = wb6 a := by
  intro a
  change (Realisation.multiSubst eb6 (chb6 R) Hh).w a = wb6 a
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
  Realisation.multiSubst eb7 (chb7 R) Hh

/-- The seven sizes at node `b7`. -/
def wb7 : Letter → Nat
  | .B => 1371483571393810
  | .N => 1176281769712642
  | .A => 206915639642778
  | .D => 172575880978818
  | .O => 0
  | .H => 183888841329993
  | .V => 195602679291603

/-- Node `b7` has the sizes `wb7`. -/
lemma stepb7 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb7 R).w a = wb7 a := by
  intro a
  change (Realisation.multiSubst eb7 (chb7 R) Hh).w a = wb7 a
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
  Realisation.multiSubst eb8 (chb8 R) Hh

/-- The seven sizes at node `b8`. -/
def wb8 : Letter → Nat
  | .B => 200003592413967238
  | .N => 167652758218123498
  | .A => 34601007224267169
  | .D => 28034620408130082
  | .O => 0
  | .H => 30192727301986911
  | .V => 32442900330410340

/-- Node `b8` has the sizes `wb8`. -/
lemma stepb8 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb8 R).w a = wb8 a := by
  intro a
  change (Realisation.multiSubst eb8 (chb8 R) Hh).w a = wb8 a
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
  Realisation.multiSubst eb9 (chb9 R) Hh

/-- The seven sizes at node `b9`. -/
def wb9 : Letter → Nat
  | .B => 29188427782922441263
  | .N => 23910494688646338223
  | .A => 5694786365303460978
  | .D => 4483874372608842138
  | .O => 0
  | .H => 4880903733442472589
  | .V => 5297757004469830527

/-- Node `b9` has the sizes `wb9`. -/
lemma stepb9 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb9 R).w a = wb9 a := by
  intro a
  change (Realisation.multiSubst eb9 (chb9 R) Hh).w a = wb9 a
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
  Realisation.multiSubst eb10 (chb10 R) Hh

/-- The seven sizes at node `b10`. -/
def wb10 : Letter → Nat
  | .B => 4262858010737490892483
  | .N => 3412374604883690410600
  | .A => 925569841353094800660
  | .D => 708441644976394598265
  | .O => 0
  | .H => 779462525415097540074
  | .V => 854548960914391858851

/-- Node `b10` has the sizes `wb10`. -/
lemma stepb10 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb10 R).w a = wb10 a := by
  intro a
  change (Realisation.multiSubst eb10 (chb10 R) Hh).w a = wb10 a
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
  Realisation.multiSubst eb11 (chb11 R) Hh

/-- The seven sizes at node `b11`. -/
def wb11 : Letter → Nat
  | .B => 623016446015924647606810
  | .N => 487333903417543322707180
  | .A => 148908463322024293742517
  | .D => 110835837401299104185430
  | .O => 0
  | .H => 123259189999840214542530
  | .V => 136485110723483183385417

/-- Node `b11` has the sizes `wb11`. -/
lemma stepb11 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb11 R).w a = wb11 a := by
  intro a
  change (Realisation.multiSubst eb11 (chb11 R) Hh).w a = wb11 a
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
  Realisation.multiSubst eb12 (chb12 R) Hh

/-- The seven sizes at node `b12`. -/
def wb12 : Letter → Nat
  | .B => 91116617574479044096771291
  | .N => 69648139675257224705647111
  | .A => 23756013974149570516970385
  | .D => 17200690621237102762452600
  | .O => 0
  | .H => 19334584260229461076788390
  | .V => 21622120335157212202634595

/-- Node `b12` has the sizes `wb12`. -/
lemma stepb12 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb12 R).w a = wb12 a := by
  intro a
  change (Realisation.multiSubst eb12 (chb12 R) Hh).w a = wb12 a
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
  Realisation.multiSubst eb13 (chb13 R) Hh

/-- The seven sizes at node `b13`. -/
def wb13 : Letter → Nat
  | .B => 13334779662085621413870106150
  | .N => 9961303875808974619752800917
  | .A => 3763172269921859090595370128
  | .D => 2651442487241440266385210533
  | .O => 0
  | .H => 3012459136759043530251257883
  | .V => 3402155620404255826729322778

/-- Node `b13` has the sizes `wb13`. -/
lemma stepb13 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rb13 R).w a = wb13 a := by
  intro a
  change (Realisation.multiSubst eb13 (chb13 R) Hh).w a = wb13 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chb13 R 0).w b = wb12 b := fun b => stepb12 R h b
  have h1 : ∀ b, (chb13 R 1).w b = w0 b := fun b => (w_R1 R b).trans (h b)
  simp only [Fin.prod_univ_two, h0, h1]
  cases a <;> native_decide

/-! ### Node `p11`, exponent `11` -/

/-- The child exponents of node `p11`. -/
def ep11 : Fin 3 → Nat := Fin.cases 3 (Fin.cases 6 (fun _ => 2))

/-- The children of node `p11`. -/
def chp11 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (ep11 i)) :=
  Fin.cases (Rg3 R) (Fin.cases (Rh6 R) (fun _ => (Rb2 R)))

/-- Node `p11`. -/
def Rp11 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 11) :=
  Realisation.multiSubst ep11 (chp11 R) Gg

/-- The seven sizes at node `p11`. -/
def wp11 : Letter → Nat
  | .B => 623825371512402661496710
  | .N => 487764785816855225733415
  | .A => 148649851569514001973198
  | .D => 110613088786522158144618
  | .O => 0
  | .H => 123094010236441396497846
  | .V => 135706536167990920025226

/-- Node `p11` has the sizes `wp11`. -/
lemma stepp11 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rp11 R).w a = wp11 a := by
  intro a
  change (Realisation.multiSubst ep11 (chp11 R) Gg).w a = wp11 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chp11 R 0).w b = wg3 b := fun b => stepg3 R h b
  have h1 : ∀ b, (chp11 R 1).w b = wh6 b := fun b => steph6 R h b
  have h2 : ∀ b, (chp11 R 2).w b = wb2 b := fun b => stepb2 R h b
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### Node `x27`, exponent `27` -/

/-- The child exponents of node `x27`. -/
def ex27 : Fin 3 → Nat := Fin.cases 7 (Fin.cases 11 (fun _ => 9))

/-- The children of node `x27`. -/
def chx27 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (ex27 i)) :=
  Fin.cases (Rh7 R) (Fin.cases (Rp11 R) (fun _ => (Rh9 R)))

/-- Node `x27`. -/
def Rx27 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 27) :=
  Realisation.multiSubst ex27 (chx27 R) Gg

/-- The seven sizes at node `x27`. -/
def wx27 : Letter → Nat
  | .B => 29838441714094862993252839013822328163235607901233033567784
  | .N => 16541141141077802618954438265898987987722164239163397895330
  | .A => 15804443370734233724287801036342961110072632999394850461965
  | .D => 7696826188722826294170981742359508014219650447768917984455
  | .O => 0
  | .H => 10236321091594989029757595214383341180131411905782531251025
  | .V => 12797544891705780685227304634800778404795174307344939401927

/-- Node `x27` has the sizes `wx27`. -/
lemma stepx27 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rx27 R).w a = wx27 a := by
  intro a
  change (Realisation.multiSubst ex27 (chx27 R) Gg).w a = wx27 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chx27 R 0).w b = wh7 b := fun b => steph7 R h b
  have h1 : ∀ b, (chx27 R 1).w b = wp11 b := fun b => stepp11 R h b
  have h2 : ∀ b, (chx27 R 2).w b = wh9 b := fun b => steph9 R h b
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### Node `x29`, exponent `29` -/

/-- The child exponents of node `x29`. -/
def ex29 : Fin 3 → Nat := Fin.cases 6 (Fin.cases 12 (fun _ => 11))

/-- The children of node `x29`. -/
def chx29 (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (ex29 i)) :=
  Fin.cases (Rh6 R) (Fin.cases (Rb12 R) (fun _ => (Rp11 R)))

/-- Node `x29`. -/
def Rx29 (R : Realisation Letter Letter.sep G) :
    Realisation Letter Letter.sep (SimpleGraph.strongPower G 29) :=
  Realisation.multiSubst ex29 (chx29 R) Gg

/-- The seven sizes at node `x29`. -/
def wx29 : Letter → Nat
  | .B => 650550713927601334001699389913155348392810457018985339501035264
  | .N => 346665192931762993291506159464838396825673371935586278860476985
  | .A => 364055447564885830181669411441526823563212717301403380227256399
  | .D => 168269857996039112611978515863873677038396310261638361932733188
  | .O => 0
  | .H => 229062463393008670280793150833135414858753202262534604626255086
  | .V => 290676435334973079530748878630130114988535811920654805583084068

/-- Node `x29` has the sizes `wx29`. -/
lemma stepx29 (R : Realisation Letter Letter.sep G) (h : ∀ a, R.w a = w0 a) :
    ∀ a, (Rx29 R).w a = wx29 a := by
  intro a
  change (Realisation.multiSubst ex29 (chx29 R) Gg).w a = wx29 a
  rw [w_multiSubst]
  have h0 : ∀ b, (chx29 R 0).w b = wh6 b := fun b => steph6 R h b
  have h1 : ∀ b, (chx29 R 1).w b = wb12 b := fun b => stepb12 R h b
  have h2 : ∀ b, (chx29 R 2).w b = wp11 b := fun b => stepp11 R h b
  simp only [Fin.prod_univ_three, h0, h1, h2]
  cases a <;> native_decide

/-! ### The bound -/

/-- The exponents of the 3 terminal children. -/
def eT : Fin 3 → Nat := Fin.cases 27 (Fin.cases 29 (fun _ => 13))

/-- The terminal children. -/
def terminalChildren (R : Realisation Letter Letter.sep G) :
    (i : Fin 3) → Realisation Letter Letter.sep (SimpleGraph.strongPower G (eT i)) :=
  Fin.cases (Rx27 R) (Fin.cases (Rx29 R) (fun _ => (Rb13 R)))

/-- **The bound.**  A port system whose seven families have the sizes of `w0` gives an
independent set of size `M` in `G^(box 69)`. -/
theorem bound (S : RichPortSystem G) (hw : ∀ a, (S.fam a).card = w0 a) :
    M ≤ (SimpleGraph.strongPower G 69).indepNum := by
  have base_w : ∀ a, S.toRealisation.w a = w0 a := hw
  refine le_trans (le_of_eq ?_) (le_indepNum_multiCode eT (terminalChildren S.toRealisation) K)
  have h0 : ∀ a, (terminalChildren S.toRealisation 0).w a = wx27 a := by
    intro a; change (Rx27 S.toRealisation).w a = wx27 a; exact stepx27 S.toRealisation base_w a
  have h1 : ∀ a, (terminalChildren S.toRealisation 1).w a = wx29 a := by
    intro a; change (Rx29 S.toRealisation).w a = wx29 a; exact stepx29 S.toRealisation base_w a
  have h2 : ∀ a, (terminalChildren S.toRealisation 2).w a = wb13 a := by
    intro a; change (Rb13 S.toRealisation).w a = wb13 a; exact stepb13 S.toRealisation base_w a
  simp only [Fin.prod_univ_three, h0, h1, h2]
  native_decide

end CertC11
end ShannonBounds
