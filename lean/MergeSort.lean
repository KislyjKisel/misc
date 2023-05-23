import Std.Data.List.Lemmas
import Std.Data.Nat.Lemmas

universe u
variable {α : Type u} {lt : α → α → Prop}


theorem List.splitAt.go.length_fst {α} (as bs : List α) (n : Nat) (h : n < bs.length) (acc : Array α) :
  (List.splitAt.go as bs n acc).1.length = acc.size + n := by
  match bs, n, acc with
  | [], n, _ =>
    apply False.elim
    apply Nat.not_lt_zero n
    exact h
  | x :: xs, n+1, acc =>
    apply (length_fst as xs n (Nat.lt_of_add_lt_add_right h) (acc.push x)).trans
    rw [Array.size_push, Nat.add_assoc, Nat.add_comm 1]
  | x :: xs, 0, acc =>
    show _ = acc.data.length
    unfold List.splitAt.go
    rw [Array.toList_eq]

theorem List.splitAt.go.length_snd {α} (as bs : List α) (n : Nat) (h : n < bs.length) (acc : Array α) :
  (List.splitAt.go as bs n acc).2.length = bs.length - n := by
  match bs, n, acc with
  | [], n, _ =>
    apply False.elim
    apply Nat.not_lt_zero n
    exact h
  | x :: xs, n+1, acc =>
    apply (length_snd as xs n (Nat.lt_of_add_lt_add_right h) (acc.push x)).trans
    show xs.length - n = xs.length.succ - n.succ
    rw [Nat.succ_sub_succ]
  | x :: xs, 0, acc =>
    simp only [List.splitAt.go]
    rw [Nat.sub_zero]



class Asymmetric {α} (op : α → α → Prop) : Prop where
  asymm : ∀{x y}, op x y → ¬ op y x

open Asymmetric



def Sorted (lt : α → α → Prop) (as : List α) : Prop :=
  as.Chain' (λ x y ↦ ¬ lt y x)

namespace Sorted

theorem nil : Sorted lt [] := True.intro

theorem singleton {a} : Sorted lt [a] := List.Chain.nil

theorem cons₂ {a a' as} (h₁ : ¬ lt a' a) (h₂ : Sorted lt (a' :: as)) :
  Sorted lt (a :: a' :: as) :=
    List.Chain.cons h₁ h₂

theorem tail {a : α} {as} : Sorted lt (a :: as) → Sorted lt as
| List.Chain.nil => nil
| List.Chain.cons _ rs => rs

theorem head {a b as} : Sorted lt (a :: b :: as) → ¬ lt b a
| .cons r _ => r

end Sorted



namespace mergeSort

def merge (lt : α → α → Prop) [DecidableRel lt] : List α → List α → List α
| as, [] => as
| [], b :: bs => b :: bs
| a :: as, b :: bs => if lt b a
  then b :: merge lt (a :: as) bs
  else a :: merge lt as (b :: bs)
termination_by _ as bs => as.length + bs.length

def split (as : List α) : List α × List α :=
  as.splitAt (as.length / 2)

theorem split.length_fst_of_length_gt_zero (as : List α) (h : as.length > 0) :
  (split as).1.length = as.length / 2 := by
    unfold split
    unfold List.splitAt
    have : as.length / 2 < as.length := Nat.div_lt_self h (by decide)
    rewrite [List.splitAt.go.length_fst _ _ _ this]
    show 0 + _ = _
    rw [Nat.zero_add]

theorem split.length_snd_of_length_gt_zero (as : List α) (h : as.length > 0) :
  (split as).2.length = as.length - as.length / 2 := by
    unfold split
    unfold List.splitAt
    have : as.length / 2 < as.length := Nat.div_lt_self h (by decide)
    rw [List.splitAt.go.length_snd _ _ _ this]

theorem split.decreasing {as : List α} (h : ¬ as.length < 2) :
  (split as).fst.length < as.length ∧ (split as).snd.length < as.length := by
    have h := Nat.ge_of_not_lt h
    have : as.length > 0 := Nat.lt_of_lt_of_le (by decide) h
    apply And.intro
    · rewrite [split.length_fst_of_length_gt_zero _ this]
      exact Nat.div_lt_self this (by decide)
    · rewrite [split.length_snd_of_length_gt_zero _ this]
      apply Nat.sub_lt_self
      · apply Nat.lt_of_lt_of_eq (Nat.zero_lt_succ $ (as.length - 2) / 2)
        conv =>
          rhs
          rewrite [Nat.div_eq_sub_div (by decide) h]
      · apply Nat.le_of_lt
        exact Nat.div_lt_self this (by decide)

def _root_.mergeSort (lt : α → α → Prop) [DecidableRel lt] (as : List α) : List α :=
  if h: as.length < 2
    then
      match as with
      | a :: a' :: [] =>
        if lt a' a
          then a' :: a :: []
          else a :: a' :: []
      | as => as
    else
      let ss := split as
      have := split.decreasing h
      merge lt (
        have := this.1
        mergeSort lt ss.1
      ) (
        have := this.2
        mergeSort lt ss.2
      )
termination_by _ as _ => as.length

theorem merge.nil_left [DecidableRel lt] (bs : List α) : merge lt [] bs = bs := by
  cases bs <;> rfl

theorem merge.nil_right [DecidableRel lt] (as : List α) : merge lt as [] = as := by
  cases as <;> rfl

theorem merge.cons_left [DecidableRel lt] {a b as bs} (h : ¬ lt b a) :
  merge lt (a :: as) (b :: bs) = a :: merge lt as (b :: bs) := by
    conv => lhs; unfold merge
    simp only [eq_false h, ite_false]

theorem merge.cons_right [DecidableRel lt] {a b as bs} (h : lt b a) :
  merge lt (a :: as) (b :: bs) = b :: merge lt (a :: as) bs := by
    conv => lhs; unfold merge
    simp only [h, ite_true]

theorem merge.length [DecidableRel lt] (as bs : List α) :
  (merge lt as bs).length = as.length + bs.length := by
    match as, bs with
    | as, [] => rewrite [merge.nil_right]; rfl
    | [], b :: bs => show _ = 0 + _; rw [merge.nil_left, Nat.zero_add]
    | a :: as, b :: bs =>
      unfold merge
      if h: lt b a
        then
          simp only [
            h,
            ite_true,
            merge.length (a :: as) bs,
            List.length_cons
          ]
          rfl
        else
          simp only [
            eq_false h,
            ite_false,
            merge.length as (b :: bs),
            List.length_cons
          ]
          simp_arith
termination_by _ as bs => as.length + bs.length

theorem merge.ne_nil_left [DecidableRel lt] (as bs : List α) (h : as ≠ []) :
  merge lt as bs ≠ [] := by
    have : as.length > 0 := List.length_pos.mpr h
    apply List.length_pos.mp
    rewrite [merge.length as bs]
    apply Nat.lt_of_lt_of_le this
    exact Nat.le_add_right _ _

theorem merge.sorted [DecidableRel lt] [Asymmetric lt] (as bs : List α) (ah : Sorted lt as) (bh : Sorted lt bs) :
  Sorted lt (merge lt as bs) := by
    match as, bs with
    | as, [] =>
      rewrite [merge.nil_right]
      exact ah
    | [], b :: bs =>
      rewrite [merge.nil_left]
      exact bh
    | a :: as, b :: bs =>
      unfold merge
      if h: lt b a
        then
          simp only [h, ite_true]
          have : (merge lt (a :: as) bs).length = Nat.succ _ := by
            apply Eq.trans $ merge.length (a :: as) bs
            rewrite [List.length]
            conv => lhs; rw [Nat.add_assoc, Nat.add_comm 1]
          have := List.exists_cons_of_ne_nil (List.ne_nil_of_length_eq_succ this)
          apply this.elim
          intro head tail
          apply tail.elim
          intro tail merge_eq
          rewrite [merge_eq]
          apply Sorted.cons₂
          · match bs with
            | [] =>
              have : head = (merge lt (a :: as) []).head (by intro; contradiction) := by
                simp only [merge_eq]
                dsimp
              have : head = (a :: as).head _ := by
                apply this.trans
                simp only [merge.nil_right]
                exact List.cons_ne_nil _ _
              rewrite [this]
              dsimp
              exact asymm h
            | b' :: bs =>
              if h': lt b' a
                then
                  have : head = b' := by
                    apply List.head_eq_of_cons_eq
                    calc head :: _
                      _ = merge lt (a :: as) (b' :: bs) := merge_eq.symm
                      _ = b' :: merge lt (a :: as) bs := merge.cons_right h'
                  rewrite [this]
                  apply Sorted.head bh
                else
                  have : head = a := by
                    apply List.head_eq_of_cons_eq
                    calc head :: _
                      _ = merge lt (a :: as) (b' :: bs) := merge_eq.symm
                      _ = a :: merge lt as (b' :: bs) := merge.cons_left h'
                  rewrite [this]
                  exact asymm h
          · rewrite [← merge_eq]
            apply merge.sorted _ _ ah bh.tail
        else
          simp only [eq_false h, ite_false]
          have : (merge lt as (b :: bs)).length = Nat.succ _ := by
            apply Eq.trans $ merge.length as (b :: bs)
            rewrite [List.length, ← Nat.add_assoc]
            exact Nat.add_one _
          have := List.exists_cons_of_ne_nil (List.ne_nil_of_length_eq_succ this)
          apply this.elim
          intro head tail
          apply tail.elim
          intro tail merge_eq
          rewrite [merge_eq]
          apply Sorted.cons₂
          · match as with
            | [] =>
              have : head = (merge lt [] (b :: bs)).head (by intro; contradiction) := by
                simp only [merge_eq]
                dsimp
              have : head = (b :: bs).head _ := by
                apply this.trans
                simp only [merge.nil_left]
                exact List.cons_ne_nil _ _
              rewrite [this]
              dsimp
              exact h
            | a' :: as =>
              if h': lt b a'
                then
                  have : head = b := by
                    apply List.head_eq_of_cons_eq
                    calc head :: _
                      _ = merge lt (a' :: as) (b :: bs) := merge_eq.symm
                      _ = b :: merge lt (a' :: as) bs := merge.cons_right h'
                  rewrite [this]
                  exact h
                else
                  have : head = a' := by
                    apply List.head_eq_of_cons_eq
                    calc head :: _
                      _ = merge lt (a' :: as) (b :: bs) := merge_eq.symm
                      _ = a' :: merge lt as (b :: bs) := merge.cons_left h'
                  rewrite [this]
                  exact ah.head
          · rewrite [← merge_eq]
            exact merge.sorted _ _ ah.tail bh
termination_by _ as bs _ _ => as.length + bs.length

theorem sorted [DecidableRel lt] [Asymmetric lt] (as : List α) :
  Sorted lt (mergeSort lt as) := by
    unfold mergeSort
    if h: as.length < 2
      then
        simp only [h, dite_true]
        match as with
        | [] => exact .nil
        | a :: [] => exact .singleton
        | a :: a' :: [] =>
          if h: lt a' a
            then
              simp only [h, ite_true]
              exact Sorted.cons₂ (asymm h) .singleton
            else
              simp only [h, ite_false]
              exact Sorted.cons₂ h .singleton
      else
        simp only [h, dite_false]
        have := split.decreasing h
        apply merge.sorted _ _
        · have := this.1
          exact sorted _
        · have := this.2
          exact sorted _
termination_by _ as => as.length
